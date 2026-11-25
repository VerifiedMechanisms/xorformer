import HeadComplexity.Polynomial.RoPEGroupSymmetrization

set_option linter.style.header false

/-!
# The mixed block coefficient depends only on top squarefree coefficients

Each input variable is weighted by its own block parameter. Extracting the
coefficient with one parameter from every block retains exactly one variable
per block, so replica averaging preserves this projection exactly.
-/

noncomputable section

namespace HeadComplexity.BlockCoefficientProjection

open MvPolynomial
open scoped BigOperators

variable {β σ A : Type*} [Fintype β] [CommRing A] [Algebra ℝ A]

def allOnes : β →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ ↦ 1)

@[simp] theorem allOnes_apply (b : β) : allOnes b = 1 := by simp [allOnes]

def weightedMap (g : β × σ → A) : MvPolynomial (β × σ) ℝ →+* MvPolynomial β A :=
  eval₂Hom (C.comp (algebraMap ℝ A))
    (fun p ↦ monomial (Finsupp.single p.1 1) (g p))

def projection (g : β × σ → A) (P : MvPolynomial (β × σ) ℝ) : A :=
  coeff allOnes (weightedMap g P)

omit [Fintype β] in
theorem weightedMap_monomial (g : β × σ → A) (e : β × σ →₀ ℕ) (c : ℝ) :
    weightedMap g (monomial e c) =
      monomial (e.mapDomain Prod.fst)
        (algebraMap ℝ A c * e.prod (fun p k ↦ g p ^ k)) := by
  classical
  simp only [weightedMap, eval₂Hom_monomial, RingHom.comp_apply, monomial_pow,
    Finsupp.prod, ← monomial_sum_prod, C_mul_monomial, Finsupp.smul_single,
    nsmul_eq_mul, mul_one]
  rfl

theorem projection_monomial [DecidableEq β] (g : β × σ → A) (e : β × σ →₀ ℕ) (c : ℝ) :
    projection g (monomial e c) =
      if e.mapDomain Prod.fst = allOnes then
        algebraMap ℝ A c * e.prod (fun p k ↦ g p ^ k) else 0 := by
  classical
  simp only [projection, weightedMap_monomial, coeff_monomial]

/-- A block degree equal to one forces every individual exponent to be at most one. -/
theorem exponent_le_one_of_block_degree_one (e : β × σ →₀ ℕ)
    (he : e.mapDomain Prod.fst = allOnes) (p : β × σ) : e p ≤ 1 := by
  classical
  have hs : e p ≤ (e.mapDomain Prod.fst) p.1 := by
    rw [Finsupp.mapDomain_apply_eq_sum]
    by_cases hp : p ∈ e.support
    · have h := Finset.single_le_sum
        (fun j _ ↦ Nat.zero_le (if j.1 = p.1 then e j else 0)) hp
      simpa only [Finset.sum_filter, ite_true, eq_self] using h
    · simp only [Finsupp.notMem_support_iff.mp hp, Nat.zero_le]
  simpa only [he, allOnes_apply] using hs

theorem degree_of_block_degree_one (e : β × σ →₀ ℕ)
    (he : e.mapDomain Prod.fst = allOnes) :
    e.sum (fun _ k ↦ k) = Fintype.card β := by
  classical
  have h := Finsupp.sum_mapDomain_index (f := Prod.fst) (s := e)
    (h := fun _ k ↦ k) (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
  rw [he] at h
  have hone : (allOnes : β →₀ ℕ).sum (fun _ k ↦ k) = Fintype.card β := by
    rw [Finsupp.sum_fintype]
    · simp
    · intro b; rfl
  exact h.symm.trans hone

/-- Every linear block projection ignores all other coefficients, even when
those other coefficients have larger total degree. -/
theorem projection_eq_of_top_coeff_eq (g : β × σ → A)
    (P Q : MvPolynomial (β × σ) ℝ)
    (h : ∀ e : β × σ →₀ ℕ, (∀ p, e p ≤ 1) →
      e.sum (fun _ k ↦ k) = Fintype.card β → coeff e P = coeff e Q) :
    projection g P = projection g Q := by
  classical
  have hzero : projection g (P - Q) = 0 := by
    rw [← (P - Q).support_sum_monomial_coeff]
    simp only [projection, map_sum, coeff_sum]
    apply Finset.sum_eq_zero
    intro e he
    change projection g (monomial e (coeff e (P - Q))) = 0
    rw [projection_monomial]
    split_ifs with hb
    · have hc := h e (exponent_le_one_of_block_degree_one e hb)
        (degree_of_block_degree_one e hb)
      simp only [coeff_sub, hc, sub_self, map_zero, zero_mul]
    · rfl
  simpa only [projection, map_sub, coeff_sub, sub_eq_zero] using hzero


/-- Replica averaging preserves the entire block projection whenever the
original polynomial has degree at most the number of blocks. -/
theorem projection_averaged {r : ℕ} [Fintype σ] [DecidableEq β] [DecidableEq σ]
    (hr : 0 < r) (g : β × σ → A)
    (P : MvPolynomial ((β × σ) × Fin r) ℝ)
    (hP : P.totalDegree ≤ Fintype.card β) :
    projection g (RoPEGroupSymmetrization.averagedGroupPolynomial P) =
      projection g (rename Prod.fst P) := by
  apply projection_eq_of_top_coeff_eq
  intro e he hdeg
  apply RoPEGroupSymmetrization.averagedGroupPolynomial_coeff_top_squarefree hr P e he
  simpa only [hdeg] using hP


abbrev BlockExponent (β σ : Type*) [Fintype β] :=
  {e : β × σ →₀ ℕ // e.mapDomain Prod.fst = (allOnes : β →₀ ℕ)}

noncomputable instance [Fintype σ] : Fintype (BlockExponent β σ) :=
  ((Finsupp.finite_of_degree_le (σ := β × σ) (Fintype.card β)).subset
    (fun e he ↦ (degree_of_block_degree_one e he).le)).fintype

/-- The projection is a fixed finite sum indexed by one-variable-per-block
exponents; the index set is independent of the input polynomial. -/
theorem projection_eq_sum [Fintype σ] (g : β × σ → A)
    (P : MvPolynomial (β × σ) ℝ) :
    projection g P = ∑ e : BlockExponent β σ,
      algebraMap ℝ A (coeff e.val P) * e.val.prod (fun p k ↦ g p ^ k) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [projection_monomial]
    split_ifs with hd
    · let e : BlockExponent β σ := ⟨d, hd⟩
      rw [Finset.sum_eq_single e]
      · simp [e]
      · intro e' _ hne
        have hval : d ≠ e'.val := by intro he; exact hne (Subtype.ext he.symm)
        simp only [coeff_monomial, if_neg hval, map_zero, zero_mul]
      · simp
    · symm
      apply Finset.sum_eq_zero
      intro e _
      have hval : d ≠ e.val := by intro he; exact hd (he.symm ▸ e.property)
      simp only [coeff_monomial, if_neg hval, map_zero, zero_mul]
  | add P Q hP hQ =>
    simp only [projection, map_add, coeff_add] at hP hQ ⊢
    rw [hP, hQ]
    simp only [add_mul, Finset.sum_add_distrib]

end HeadComplexity.BlockCoefficientProjection
