import HeadComplexity.Research.WeightedNormalizedCounting

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.NormalizedPolynomialSupport
open Finset MvPolynomial
open PolynomialRootCount NormalizedCounting
open scoped BigOperators

variable {K : Type*} [DecidableEq K]

def CoeffNonneg (P : MvPolynomial K ℝ) : Prop := ∀ m, 0 ≤ P.coeff m

lemma nonneg_C (c : ℝ) (hc : 0 ≤ c) : CoeffNonneg (C c : MvPolynomial K ℝ) := by
  intro m
  simp only [coeff_C]
  split_ifs <;> positivity

lemma nonneg_X (k : K) : CoeffNonneg (X k : MvPolynomial K ℝ) := by
  intro m
  simp only [coeff_X]
  split_ifs <;> positivity

lemma nonneg_add {P Q : MvPolynomial K ℝ} (hp : CoeffNonneg P) (hq : CoeffNonneg Q) :
    CoeffNonneg (P+Q) := by intro m; rw [MvPolynomial.coeff_add]; exact add_nonneg (hp m) (hq m)

lemma nonneg_mul {P Q : MvPolynomial K ℝ} (hp : CoeffNonneg P) (hq : CoeffNonneg Q) :
    CoeffNonneg (P*Q) := by
  intro m
  rw [coeff_mul]
  exact Finset.sum_nonneg fun z _ => mul_nonneg (hp z.1) (hq z.2)

lemma coeff_mul_pos {P Q : MvPolynomial K ℝ} (hp : CoeffNonneg P) (hq : CoeffNonneg Q)
    (a b : K →₀ ℕ) (ha : 0 < P.coeff a) (hb : 0 < Q.coeff b) :
    0 < (P*Q).coeff (a+b) := by
  rw [coeff_mul]
  apply (mul_pos ha hb).trans_le
  exact Finset.single_le_sum (fun z _ => mul_nonneg (hp z.1) (hq z.2))
    (show (a,b) ∈ Finset.antidiagonal (a+b) by simp)

lemma nonneg_sum {I : Type*} (s : Finset I) (P : I → MvPolynomial K ℝ)
    (hp : ∀ i ∈ s, CoeffNonneg (P i)) : CoeffNonneg (∑ i ∈ s, P i) := by
  intro m
  simp only [coeff_sum]
  exact Finset.sum_nonneg fun i hi => hp i hi m

lemma nonneg_prod {I : Type*} (s : Finset I) (P : I → MvPolynomial K ℝ)
    (hp : ∀ i ∈ s, CoeffNonneg (P i)) : CoeffNonneg (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nonneg_C (K := K) 1 (by norm_num)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact nonneg_mul (hp a (by simp)) (ih fun i hi => hp i (by simp [hi]))

lemma coeff_prod_pos {I : Type*} (s : Finset I) (P : I → MvPolynomial K ℝ)
    (m : I → K →₀ ℕ) (hp : ∀ i ∈ s, CoeffNonneg (P i))
    (hm : ∀ i ∈ s, 0 < (P i).coeff (m i)) :
    0 < (∏ i ∈ s, P i).coeff (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact coeff_mul_pos (hp a (by simp))
      (nonneg_prod s P fun i hi => hp i (by simp [hi])) _ _
      (hm a (by simp)) (ih (fun i hi => hp i (by simp [hi]))
        (fun i hi => hm i (by simp [hi])))

variable {n H : ℕ}

lemma top_linear_nonneg (kind : Bool) (h : Fin H) :
    CoeffNonneg (linearPoly (n := n) kind h (fun _ => true)) := by
  simp only [linearPoly, boolToReal, ↓reduceIte, C_1, one_mul]
  exact nonneg_sum _ _ fun i _ => nonneg_X _

lemma top_linear_coeff (kind : Bool) (h : Fin H) (i : Fin n) :
    (linearPoly kind h (fun _ => true)).coeff (Finsupp.single (h,kind,i) 1) = 1 := by
  simp [linearPoly, boolToReal, coeff_single_X]

lemma top_den_nonneg (h : Fin H) :
    CoeffNonneg (denPoly (n := n) h (fun _ => true)) :=
  nonneg_add (by simpa using nonneg_C (K := Parameter n H) 1 (by norm_num))
    (top_linear_nonneg true h)

lemma top_den_coeff_pos (h : Fin H) (i : Fin n) :
    0 < (denPoly h (fun _ => true)).coeff (Finsupp.single (h,true,i) 1) := by
  rw [denPoly, MvPolynomial.coeff_add, top_linear_coeff]
  have hh := (show CoeffNonneg (1 : MvPolynomial (Parameter n H) ℝ) from
    by simpa using nonneg_C (K := Parameter n H) 1 (by norm_num))
      (Finsupp.single (h,true,i) 1)
  linarith

/-- A numerator variable from one head and one denominator variable from
every other head always form a nonzero monomial of the all-one predicate. -/
theorem selected_monomial_mem_support (h : Fin H) (i : Fin n) (j : Fin H → Fin n) :
    Finsupp.single (h,false,i) 1 +
      (∑ g ∈ Finset.univ.erase h, Finsupp.single (g,true,j g) 1) ∈
      (clearedPoly true (fun _ : Fin n => true)).support := by
  classical
  let m := Finsupp.single (h,false,i) 1 +
      (∑ g ∈ Finset.univ.erase h, Finsupp.single (g,true,j g) 1)
  have hp (g : Fin H) : CoeffNonneg
      (linearPoly false g (fun _ : Fin n => true) *
        ∏ k ∈ Finset.univ.erase g, denPoly k (fun _ => true)) :=
    nonneg_mul (top_linear_nonneg false g)
      (nonneg_prod _ _ fun k _ => top_den_nonneg k)
  have hterm : 0 < (linearPoly false h (fun _ : Fin n => true) *
      ∏ g ∈ Finset.univ.erase h, denPoly g (fun _ => true)).coeff m := by
    apply coeff_mul_pos (top_linear_nonneg false h)
      (nonneg_prod _ _ fun g _ => top_den_nonneg g)
    · rw [top_linear_coeff]; norm_num
    · exact coeff_prod_pos _ _ _ (fun g _ => top_den_nonneg g)
        (fun g _ => top_den_coeff_pos g (j g))
  have hsum : 0 < (∑ g : Fin H, linearPoly false g (fun _ : Fin n => true) *
      ∏ k ∈ Finset.univ.erase g, denPoly k (fun _ => true)).coeff m := by
    rw [coeff_sum]
    exact hterm.trans_le (Finset.single_le_sum (fun g _ => hp g m) (Finset.mem_univ h))
  have hprod := nonneg_prod Finset.univ
    (fun g : Fin H => denPoly g (fun _ : Fin n => true))
    (fun g _ => top_den_nonneg g) m
  apply mem_support_iff.mpr
  have he : 0 < (clearedPoly true (fun _ : Fin n => true)).coeff m := by
    simp only [clearedPoly, ↓reduceIte, C_1, one_mul, MvPolynomial.coeff_add]
    linarith
  exact ne_of_gt he

/-- Every actual weighted degree cap obeys each selected-monomial constraint.
Taking coordinate maxima gives the envelope used by AnisotropicWeightBarrier. -/
theorem selected_weight_le (w : Parameter n H → ℕ) (D : ℕ)
    (hdegree : WeightedDegreeLE w (clearedPoly true (fun _ : Fin n => true)) D)
    (h : Fin H) (i : Fin n) (j : Fin H → Fin n) :
    w (h,false,i) + ∑ g ∈ Finset.univ.erase h, w (g,true,j g) ≤ D := by
  have hh := hdegree _ (selected_monomial_mem_support h i j)
  have hs (s : Finset (Fin H)) :
      monomialWeight w (∑ g ∈ s, Finsupp.single (g,true,j g) 1) =
        ∑ g ∈ s, w (g,true,j g) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, monomialWeight_add, monomialWeight_single, mul_one,
        ih, Finset.sum_insert ha]
  simpa only [monomialWeight_add, monomialWeight_single, mul_one, hs] using hh

/-- Applying the actual monomial constraint to coordinates attaining each
block maximum yields the exact denominator-block envelope constraint. -/
theorem attained_block_degree_cap (w : Parameter n H → ℕ) (D : ℕ)
    (hdegree : WeightedDegreeLE w (clearedPoly true (fun _ : Fin n => true)) D)
    (U W : Fin H → ℕ)
    (hU : ∀ h, ∃ i, w (h,false,i) = U h)
    (hW : ∀ h, ∃ i, w (h,true,i) = W h) (h : Fin H) :
    U h + (∑ g, W g) - W h ≤ D := by
  classical
  choose j hj using hW
  obtain ⟨i, hi⟩ := hU h
  have hh := selected_weight_le w D hdegree h i j
  simp only [hi, hj] at hh
  have he := Finset.sum_erase_add Finset.univ W (Finset.mem_univ h)
  rw [← he]
  omega

end HeadComplexity.NormalizedPolynomialSupport
