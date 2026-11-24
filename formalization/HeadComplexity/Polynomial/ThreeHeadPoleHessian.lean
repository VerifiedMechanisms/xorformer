import HeadComplexity.Polynomial.GenericCubicHessianPullback
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Module.Submodule.Union

set_option linter.style.header false

/-!
# Three-head cubic Hessians are singular on every denominator pole

This exact form of the pole obstruction avoids compression to the pole: the
ambient Hessian already has rank at most five there. A target with a rank-six
Hessian somewhere on every positive linear hyperplane therefore has no oriented
three-head cubic representation, including representations with zero directions.
-/

namespace HeadComplexity.ThreeHeadPoleHessian
noncomputable section
open scoped BigOperators Matrix
open GenericCubicHessianPullback

/-- A square real matrix with zero determinant cannot have full rank. -/
theorem rank_lt_card_of_det_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hdet : M.det = 0) : M.rank < Fintype.card ι := by
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hk : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro he
    have hm : v ∈ LinearMap.ker M.mulVecLin := by simpa using hz
    rw [he] at hm
    exact hv (by simpa using hm)
  have hp : 1 ≤ Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hk
  have hn := M.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hn
  change Module.finrank ℝ (LinearMap.range M.mulVecLin) < Fintype.card ι
  omega

/-- The latent Hessian loses at least one rank when any denominator vanishes. -/
theorem latent_rank_le_five (s b : Fin 3 → ℝ) (h : Fin 3) (hb : b h = 0) :
    (GenericCubicHessian.hessian s b).rank ≤ 5 := by
  have hd : (GenericCubicHessian.hessian s b).det = 0 := by
    rw [GenericCubicHessian.hessian_det]
    fin_cases h <;> simp_all
  have hr := rank_lt_card_of_det_zero _ hd
  simp only [Fintype.card_sum, Fintype.card_fin] at hr
  omega

/-- Actual polynomial Hessians, with arbitrary numerator and denominator forms. -/
theorem hessian_rank_le_five_at_pole {n : ℕ} (S B : Fin 3 → Fin n → ℝ)
    (z : Fin n → ℝ) (h : Fin 3) (hb : linearValue (B h) z = 0) :
    (polynomialHessian (cubic S B) z).rank ≤ 5 := by
  rw [hessian_pullback]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (latent_rank_le_five _ _ h hb))

/-- Equality of polynomials would preserve their actual evaluated Hessians. -/
theorem ne_cubic_of_rank_six_at_pole {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (S B : Fin 3 → Fin n → ℝ) (z : Fin n → ℝ) (h : Fin 3)
    (hb : linearValue (B h) z = 0) (hp : 6 ≤ (polynomialHessian p z).rank) :
    p ≠ cubic S B := by
  intro he
  rw [he] at hp
  have hl := hessian_rank_le_five_at_pole S B z h hb
  omega

/-- A uniform exact raw-polynomial obstruction for the full oriented class.
The positive-pole rank property is a property of the target, with no assumption
on the sizes, separation, or independence of competing parameters. -/
theorem no_oriented_three_fraction_cubic {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → ∃ z,
      linearValue d z = 0 ∧ 6 ≤ (polynomialHessian p z).rank)
    (S B : Fin 3 → Fin n → ℝ)
    (hB : ∀ h, (∀ i, 0 < B h i) ∨ (∀ i, B h i < 0) ∨ B h = 0) :
    p ≠ cubic S B := by
  intro he
  by_cases hall : ∀ h, B h = 0
  · obtain ⟨z, _, hr⟩ := hp (fun _ ↦ 1) (by intro i; norm_num)
    have hb : linearValue (B 0) z = 0 := by simp [hall 0, linearValue]
    exact ne_cubic_of_rank_six_at_pole p S B z 0 hb hr he
  · push Not at hall
    obtain ⟨h, hh⟩ := hall
    rcases hB h with hpos | hneg | hz
    · obtain ⟨z, hd, hr⟩ := hp (B h) hpos
      exact ne_cubic_of_rank_six_at_pole p S B z h hd hr he
    · obtain ⟨z, hd, hr⟩ := hp (fun i ↦ -B h i) (by intro i; exact neg_pos.mpr (hneg i))
      have hb : linearValue (B h) z = 0 := by
        simp only [linearValue, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at hd
        exact hd
      exact ne_cubic_of_rank_six_at_pole p S B z h hb hr he
    · exact hh hz

/-- The linear functional associated with a coefficient vector. -/
def functional {n : ℕ} (a : Fin n → ℝ) : Module.Dual ℝ (Fin n → ℝ) where
  toFun := linearValue a
  map_add' x y := by simp [linearValue, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i, a i * (c * x i)) = c * ∑ i, a i * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Mixed signs ensure that every positive pole contains a point where a given
form does not vanish. Combining finitely many such forms avoids all their zeros. -/
theorem exists_on_positive_pole {n : ℕ} (B : Fin 3 → Fin n → ℝ)
    (hB : ∀ h, ∃ i j, 0 < B h i ∧ B h j < 0)
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ z, linearValue d z = 0 ∧ ∀ h, linearValue (B h) z ≠ 0 := by
  let p := LinearMap.ker (functional d)
  have hnon : ∀ h, ∃ z ∈ p, functional (B h) z ≠ 0 := by
    intro h
    obtain ⟨i, j, hi, hj⟩ := hB h
    let z : Fin n → ℝ := Pi.single i (d j) - Pi.single j (d i)
    have he : ∀ a : Fin n → ℝ, linearValue a z = a i * d j - a j * d i := by
      intro a
      simp [linearValue, z, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
        Pi.single_apply, mul_ite]
    refine ⟨z, ?_, ?_⟩
    · change linearValue d z = 0
      rw [he]
      ring
    · change linearValue (B h) z ≠ 0
      rw [he]
      exact ne_of_gt (sub_pos.mpr (lt_trans (mul_neg_of_neg_of_pos hj (hd i))
        (mul_pos hi (hd j))))
  obtain ⟨z, hz, hne⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
    p (fun h ↦ functional (B h)) hnon
  exact ⟨z, hz, hne⟩

/-- An independent generic cubic with three mixed denominator forms cannot
coincide with any oriented three-head raw cubic, even with unbounded numerators. -/
theorem mixed_independent_cubic_ne_oriented {n : ℕ} (S B : Fin 3 → Fin n → ℝ)
    (a : Fin 3 ⊕ Fin 3 → Fin n)
    (ha : ((slopes S B).submatrix a id).det ≠ 0)
    (hmixed : ∀ h, ∃ i j, 0 < B h i ∧ B h j < 0)
    (N E : Fin 3 → Fin n → ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    cubic S B ≠ cubic N E := by
  apply no_oriented_three_fraction_cubic _ ?_ N E hE
  intro d hd
  obtain ⟨z, hz, hne⟩ := exists_on_positive_pole B hmixed d hd
  refine ⟨z, hz, ?_⟩
  exact (hessian_rank_eq_six S B z a a ha ha hne).ge

end
end HeadComplexity.ThreeHeadPoleHessian
