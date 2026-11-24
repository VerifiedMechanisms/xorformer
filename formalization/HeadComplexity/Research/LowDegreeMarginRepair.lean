import HeadComplexity.Research.IntegerSeparatorMarginRepair
import HeadComplexity.Results.ThresholdDegreeSpan
import HeadComplexity.Polynomial.ModelToPolynomial

set_option linter.style.header false

/-!
Low threshold degree gives a quantitative original-model margin repair.
The width is the full low-degree monomial dimension, not a constant multiple
of the input width. This is useful for small-width additive repair budgets.
-/

noncomputable section

namespace HeadComplexity.LowDegreeMarginRepair

open Finset Matrix
open scoped BigOperators

lemma span_rows_eq_top_of_columns_independent {α : Type*} [Finite α] {d : ℕ}
    (A : Matrix α (Fin d) ℝ)
    (hA : LinearIndependent ℝ (fun j ↦ fun x ↦ A x j)) :
    Submodule.span ℝ (Set.range A) = ⊤ := by
  haveI := Fintype.ofFinite α
  apply Submodule.eq_top_of_finrank_eq
  have hrank : A.rank = d := by
    have hT : LinearIndependent ℝ A.transpose.row := hA
    have h : A.transpose.rank = d := by simpa using hT.rank_matrix
    simpa only [Matrix.rank_transpose] using h
  change Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) = _
  rw [← A.rank_eq_finrank_span_row, hrank]
  simp

def monomialInteger (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ :=
  if ∀ i ∈ S, x i = true then 1 else 0

lemma monomialInteger_cast (S : Finset (Fin n)) (x : Fin n → Bool) :
    (monomialInteger S x : ℝ) = squarefreeMonomial S x := by
  classical
  unfold monomialInteger
  by_cases h : ∀ i ∈ S, x i = true
  · rw [ite_eq_left h]
    simp only [Int.cast_one, squarefreeMonomial]
    symm
    exact Finset.prod_eq_one fun i hi ↦ by simp [boolToReal, h i hi]
  · push Not at h
    obtain ⟨i, hi, hxi⟩ := h
    have hfalse : x i = false := by cases hx : x i <;> simp_all
    have hall : ¬ ∀ j ∈ S, x j = true := by
      intro hall
      exact hxi (hall i hi)
    rw [ite_eq_right hall]
    simp only [Int.cast_zero, squarefreeMonomial]
    symm
    apply Finset.prod_eq_zero hi
    simp [boolToReal, hfalse]

lemma abs_monomial_le_one (S : Finset (Fin n)) (x : Fin n → Bool) :
    |squarefreeMonomial S x| ≤ 1 := by
  rw [← monomialInteger_cast]
  simp only [monomialInteger]
  split <;> norm_num

abbrev monomialCount (n d : ℕ) : ℕ := Fintype.card (LowDegreeMonomialIndex n d)

noncomputable def monomialAt (n d : ℕ) (j : Fin (monomialCount n d)) :
    Finset (Fin n) := ((Fintype.equivFin (LowDegreeMonomialIndex n d)).symm j).1

def monomialMatrix (n d : ℕ) : Matrix (Fin n → Bool) (Fin (monomialCount n d)) ℤ :=
  fun x j ↦ monomialInteger (monomialAt n d j) x

lemma monomialCount_pos (n d : ℕ) : 0 < monomialCount n d := by
  let : Nonempty (LowDegreeMonomialIndex n d) := ⟨⟨∅, by simp⟩⟩
  exact Fintype.card_pos

lemma monomialMatrix_span (n d : ℕ) :
    Submodule.span ℝ (Set.range ((monomialMatrix n d).map (fun z : ℤ ↦ (z : ℝ)))) = ⊤ := by
  apply span_rows_eq_top_of_columns_independent
  have h := (linearIndependent_lowDegreeMonomials n d).comp
    (Fintype.equivFin (LowDegreeMonomialIndex n d)).symm
    (Fintype.equivFin (LowDegreeMonomialIndex n d)).symm.injective
  simpa only [monomialMatrix, Matrix.map, Matrix.of_apply, monomialAt,
    monomialInteger_cast, Function.comp_def] using h

lemma signed_monomialMatrix_span (n d : ℕ) (f : (Fin n → Bool) → Bool) :
    Submodule.span ℝ (Set.range (fun x : Fin n → Bool ↦ fun j ↦
      (((if f x then (1 : ℤ) else -1) * monomialMatrix n d x j : ℤ) : ℝ))) = ⊤ := by
  let p : Submodule ℝ (Fin (monomialCount n d) → ℝ) := Submodule.span ℝ
    (Set.range (fun x : Fin n → Bool ↦ fun j ↦
      (((if f x then (1 : ℤ) else -1) * monomialMatrix n d x j : ℤ) : ℝ)))
  apply top_unique
  rw [← monomialMatrix_span n d]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  have hm : (fun j ↦ (((if f x then (1 : ℤ) else -1) *
      monomialMatrix n d x j : ℤ) : ℝ)) ∈ p := Submodule.subset_span ⟨x, rfl⟩
  change (fun j ↦ (monomialMatrix n d x j : ℝ)) ∈ p
  cases hfx : f x
  · simp only [hfx, Bool.false_eq_true, ite_false, neg_one_mul, Int.cast_neg] at hm
    convert p.neg_mem hm using 1
    ext j
    simp
  · simpa only [hfx, ite_true, one_mul] using hm

lemma sum_lowDegree_eq_eval (P : SquarefreePolynomial n) (hP : P.DegreeLE d)
    (x : Fin n → Bool) :
    (∑ j : Fin (monomialCount n d), P.coeff (monomialAt n d j) *
      squarefreeMonomial (monomialAt n d j) x) = P.eval x := by
  classical
  rw [← P.fullSum_eq_eval]
  calc
    _ = ∑ S : LowDegreeMonomialIndex n d, P.coeff S.1 * squarefreeMonomial S.1 x := by
      exact Fintype.sum_equiv (Fintype.equivFin (LowDegreeMonomialIndex n d)).symm
        _ _ (fun j ↦ rfl)
    _ = ∑ S : Finset (Fin n), P.coeff S * squarefreeMonomial S x := by
      have hfilter : (∑ S : LowDegreeMonomialIndex n d,
          P.coeff S.1 * squarefreeMonomial S.1 x) =
          ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦ S.card ≤ d),
            P.coeff S * squarefreeMonomial S x := by
        simpa only [Finset.subtype_univ] using
          (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
            (p := fun S : Finset (Fin n) ↦ S.card ≤ d)
            (fun S ↦ P.coeff S * squarefreeMonomial S x))
      rw [hfilter]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro S hS hnot
      have hcard : ¬ S.card ≤ d := by simpa using hnot
      have hcoeff : P.coeff S = 0 := by
        by_contra hne
        exact hcard (hP S hne)
      simp [hcoeff]

lemma signed_monomial_dot (n d : ℕ) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (a : Fin (monomialCount n d) → ℝ) :
    dotProduct (fun j ↦ (((if f x then (1 : ℤ) else -1) *
      monomialMatrix n d x j : ℤ) : ℝ)) a =
      signedLabel f x * ∑ j, a j * squarefreeMonomial (monomialAt n d j) x := by
  simp only [dotProduct, monomialMatrix, Int.cast_mul, monomialInteger_cast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases hfx : f x <;> simp [signedLabel, hfx] <;> ring

/-- Quantitative integer coefficients for every low-degree threshold table. -/
theorem exists_integer_monomial_separator (n d : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : ThresholdDegLE f d) :
    ∃ a : Fin (monomialCount n d) → ℤ,
      (∀ x, 1 ≤ signedLabel f x * ∑ j, (a j : ℝ) *
        squarefreeMonomial (monomialAt n d j) x) ∧
      (∀ j, |(a j : ℝ)| ≤ ((monomialCount n d).factorial : ℝ)) := by
  classical
  obtain ⟨P, hPdeg, hPsign⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE hf
  let w : Fin (monomialCount n d) → ℝ := fun j ↦ P.coeff (monomialAt n d j)
  let A : Matrix (Fin n → Bool) (Fin (monomialCount n d)) ℤ := fun x j ↦
    (if f x then (1 : ℤ) else -1) * monomialMatrix n d x j
  let AR : Matrix (Fin n → Bool) (Fin (monomialCount n d)) ℝ :=
    A.map (fun z : ℤ ↦ (z : ℝ))
  have heval : ∀ x, dotProduct (AR x) w = signedLabel f x * P.eval x := by
    intro x
    rw [show AR x = (fun j ↦ (((if f x then (1 : ℤ) else -1) *
      monomialMatrix n d x j : ℤ) : ℝ)) from rfl, signed_monomial_dot]
    rw [show (∑ j, w j * squarefreeMonomial (monomialAt n d j) x) = P.eval x from
      sum_lowDegree_eq_eval P hPdeg x]
  have hpos : ∀ x, 0 < dotProduct (AR x) w := by
    intro x
    rw [heval]
    cases hfx : f x
    · have hnonpos : P.eval x ≤ 0 := by
        by_contra h
        have := (hPsign x).1.mp (lt_of_not_ge h)
        simp [hfx] at this
      have hneg : P.eval x < 0 := lt_of_le_of_ne hnonpos (hPsign x).2
      simpa [signedLabel, hfx] using neg_pos.mpr hneg
    · simpa [signedLabel, hfx] using (hPsign x).1.mpr hfx
  let margin : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun x : Fin n → Bool ↦ dotProduct (AR x) w)
  have hmpos : 0 < margin := by
    simp only [margin, Finset.lt_inf'_iff, Finset.mem_univ, true_implies]
    exact hpos
  have hmargin : ∀ x, margin ≤ dotProduct (AR x) w := fun x ↦
    Finset.inf'_le _ (Finset.mem_univ x)
  have hfeasible : ∃ u, IntegerSeparatorMarginRepair.feasible AR u := by
    refine ⟨margin⁻¹ • w, fun x ↦ ?_⟩
    rw [dotProduct_smul, smul_eq_mul]
    have hm := mul_le_mul_of_nonneg_left (hmargin x) (inv_pos.mpr hmpos).le
    simpa [hmpos.ne'] using hm
  have hA : ∀ x j, |(A x j : ℝ)| ≤ 1 := by
    intro x j
    have hm : |(monomialInteger (monomialAt n d j) x : ℝ)| ≤ 1 := by
      rw [monomialInteger_cast]
      exact abs_monomial_le_one _ _
    cases hfx : f x <;> simpa [A, hfx, monomialMatrix] using hm
  obtain ⟨a, ha, habound⟩ := IntegerSeparatorMarginRepair.exists_bounded_integer_separator A hA
    (signed_monomialMatrix_span n d f) hfeasible
  refine ⟨a, fun x ↦ ?_, habound⟩
  have hx := ha x
  change 1 ≤ dotProduct (fun j ↦ (((if f x then (1 : ℤ) else -1) *
    monomialMatrix n d x j : ℤ) : ℝ)) (fun j ↦ (a j : ℝ)) at hx
  rw [signed_monomial_dot] at hx
  exact hx

#print axioms exists_integer_monomial_separator

end HeadComplexity.LowDegreeMarginRepair
