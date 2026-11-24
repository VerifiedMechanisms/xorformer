import HeadComplexity.Results.RoPETwoHeads
import HeadComplexity.Results.AffineStatisticUpperBound
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option linter.style.header false

/-!
# Positive product differences as finite sign certificates

A strict finite family of sums of positive-denominator fractions has a sign
certificate given by the difference of two products of positive affine forms.
This is an alternate polynomial sign representation, not a head-count theorem.
-/

namespace HeadComplexity

open scoped BigOperators Topology

/-- The derivative of a product of affine perturbations is the cleared
numerator of the original fraction sum. -/
theorem affine_product_hasDerivAt {H : ℕ} (N D : Fin H → ℝ)
    (hD : ∀ h, D h ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ ∏ h, (D h + t * N h))
      ((∏ h, D h) * ∑ h, N h / D h) 0 := by
  classical
  have hd (h : Fin H) : HasDerivAt (fun t : ℝ ↦ D h + t * N h) (N h) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (N h)).const_add (D h)
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun h _ ↦ hd h)
  convert! hp using 1
  simp only [zero_mul, add_zero, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ h)]
  field_simp [hD h]

/-- One common finite positive perturbation realizes every strict sign by a
difference of products, while all individual factors remain positive. -/
theorem exists_positive_product_difference {α : Type*} [Finite α] {H : ℕ}
    (N D : Fin H → α → ℝ) (hD : ∀ h x, 0 < D h x)
    (hne : ∀ x, (∑ h, N h x / D h x) ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ t < a ∧ (∀ h x, 0 < D h x + t * N h x) ∧
      ∀ x, (0 < (∏ h, (D h x + t * N h x)) - ∏ h, D h x ↔
        0 < ∑ h, N h x / D h x) ∧
        (∏ h, (D h x + t * N h x)) - ∏ h, D h x ≠ 0 := by
  classical
  let G (x : α) (t : ℝ) := ∏ h, (D h x + t * N h x)
  let S (t : ℝ) (x : α) := dslope (G x) 0 t
  have hder (x : α) : HasDerivAt (G x)
      ((∏ h, D h x) * ∑ h, N h x / D h x) 0 :=
    affine_product_hasDerivAt (fun h ↦ N h x) (fun h ↦ D h x)
      (fun h ↦ (hD h x).ne')
  have hS0 (x : α) : S 0 x = (∏ h, D h x) * ∑ h, N h x / D h x := by
    exact (dslope_same (G x) 0).trans (hder x).deriv
  have hScont (x : α) : ContinuousAt (fun t ↦ S t x) 0 :=
    continuousAt_dslope_same.mpr (hder x).differentiableAt
  let U (t : ℝ) : α ⊕ (Fin H × α) → ℝ :=
    Sum.elim (S t) (fun hx ↦ D hx.1 hx.2 + t * N hx.1 hx.2)
  have hUcont (i : α ⊕ (Fin H × α)) : ContinuousAt (fun t ↦ U t i) 0 := by
    rcases i with x | ⟨h, x⟩
    · exact hScont x
    · exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hUne (i : α ⊕ (Fin H × α)) : U 0 i ≠ 0 := by
    rcases i with x | ⟨h, x⟩
    · change S 0 x ≠ 0
      rw [hS0]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun h _ ↦ (hD h x).ne') (hne x)
    · simpa [U] using (hD h x).ne'
  obtain ⟨t, ht, hta, hstable⟩ :=
    exists_pos_lt_sign_preserving U hUcont hUne a ha
  refine ⟨t, ht, hta, ?_, fun x ↦ ?_⟩
  · intro h x
    exact (hstable (Sum.inr (h, x))).1.mpr (by simpa [U] using hD h x)
  · have hdiff : (∏ h, (D h x + t * N h x)) - ∏ h, D h x = t * S t x := by
      simpa [G, S] using (sub_smul_dslope (G x) 0 t).symm
    rw [hdiff]
    have hs : (0 < S t x ↔ 0 < ∑ h, N h x / D h x) := by
      have hu := (hstable (Sum.inl x)).1
      change (0 < S t x ↔ 0 < S 0 x) at hu
      rw [hS0, mul_pos_iff_of_pos_left (Finset.prod_pos fun h _ ↦ hD h x)] at hu
      exact hu
    exact ⟨(mul_pos_iff_of_pos_left ht).trans hs,
      mul_ne_zero ht.ne' (hstable (Sum.inl x)).2⟩

namespace CubeAffine

/-- With at least one head, the free constant is absorbed into one numerator.
Every positive affine-fraction classifier then has a strict sign-equivalent
difference of two products with the same number of positive affine factors. -/
theorem classifier_as_product_difference {n H : ℕ}
    (N D : Fin (H + 1) → CubeAffine n) (c : ℝ)
    (hD : ∀ h x, 0 < (D h).eval x) :
    ∃ A B : Fin (H + 1) → CubeAffine n,
      (∀ h x, 0 < (A h).eval x) ∧ (∀ h x, 0 < (B h).eval x) ∧
      ∀ x, (0 < (∏ h, (A h).eval x) - ∏ h, (B h).eval x ↔
        0 < c + ∑ h, (N h).eval x / (D h).eval x) ∧
        (∏ h, (A h).eval x) - ∏ h, (B h).eval x ≠ 0 := by
  classical
  obtain ⟨δ, _, hδ⟩ := exists_strict_shift
    (fun x ↦ c + ∑ h, (N h).eval x / (D h).eval x)
  let M : Fin (H + 1) → CubeAffine n :=
    Fin.cases (combine 1 (N 0) (c - δ) (D 0)) (fun h ↦ N h.succ)
  have hM (x : Fin n → Bool) :
      (∑ h, (M h).eval x / (D h).eval x) =
        (c + ∑ h, (N h).eval x / (D h).eval x) - δ := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [M, Fin.cases_zero, Fin.cases_succ, combine_eval, one_mul]
    field_simp [(hD 0 x).ne']
    ring
  obtain ⟨t, ht, _, hpos, hsign⟩ := exists_positive_product_difference
    (fun h x ↦ (M h).eval x) (fun h x ↦ (D h).eval x) hD
    (fun x ↦ by rw [hM]; exact (hδ x).2) 1 (by norm_num)
  refine ⟨fun h ↦ combine 1 (D h) t (M h), D, ?_, hD, fun x ↦ ?_⟩
  · intro h x
    simpa only [combine_eval, one_mul] using hpos h x
  · simp only [combine_eval, one_mul]
    refine ⟨(hsign x).1.trans ?_, (hsign x).2⟩
    rw [hM]
    exact (hδ x).1

end CubeAffine
end HeadComplexity
