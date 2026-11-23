import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

set_option linter.style.header false

/-!
An analytic bridge for exact approximate-inverse certificates. This file does
not assume that a rounded numerical center is a root. It obtains a genuine root
from a contraction on a closed ball. No head-complexity bound is asserted.
-/

namespace HeadComplexity.CertifiedContraction

open Set Metric Filter Asymptotics
open scoped NNReal Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_zero_of_contraction
    (F : E → E) (R : E →L[ℝ] E) (hR : Function.Injective R)
    (c : E) (r : ℝ) (hr : 0 ≤ r) (q : ℝ≥0) (hq : q < 1)
    (hLip : LipschitzOnWith q (fun z ↦ z - R (F z)) (closedBall c r))
    (hcenter : ‖R (F c)‖ ≤ (1 - (q : ℝ)) * r) :
    ∃ z ∈ closedBall c r, F z = 0 := by
  let G : E → E := fun z ↦ z - R (F z)
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  have hmap : MapsTo G (closedBall c r) (closedBall c r) := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    have hb := hLip.dist_le_mul z (show z ∈ closedBall c r from hz) c hc
    have hGc : dist (G c) c = ‖R (F c)‖ := by
      simp [G]
    calc
      dist (G z) c ≤ dist (G z) (G c) + dist (G c) c := dist_triangle _ _ _
      _ ≤ (q : ℝ) * dist z c + (1 - (q : ℝ)) * r :=
        add_le_add hb (hGc ▸ hcenter)
      _ ≤ r := by nlinarith [q.coe_nonneg]
  have hcontract : ContractingWith q (hmap.restrict G (closedBall c r) (closedBall c r)) := by
    refine ⟨hq, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hLip.dist_le_mul x x.property y y.property
  obtain ⟨z, hz, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract hc (edist_ne_top c (G c))
  refine ⟨z, hz, ?_⟩
  apply hR
  have heq : z - R (F z) = z := hfix
  have hzR : R (F z) = 0 := sub_eq_self.mp heq
  simpa using hzR

#print axioms exists_zero_of_contraction

noncomputable def positiveFunctional {m : ℕ} (lam : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i, lam i • ContinuousLinearMap.proj i

theorem positiveFunctional_apply {m : ℕ} (lam v : Fin m → ℝ) :
    positiveFunctional lam v = ∑ i, lam i * v i := by
  simp [positiveFunctional]

theorem positiveFunctional_ge_norm {m : ℕ} (lam v : Fin m → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hlam : ∀ i, η ≤ lam i) (hv : ∀ i, 0 ≤ v i) :
    η * ‖v‖ ≤ positiveFunctional lam v := by
  classical
  have hsum : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ ↦ hv i
  have hnorm : ‖v‖ ≤ ∑ i, v i := by
    apply (pi_norm_le_iff_of_nonneg hsum).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hv i)]
    exact Finset.single_le_sum (fun j _ ↦ hv j) (Finset.mem_univ i)
  calc
    η * ‖v‖ ≤ η * ∑ i, v i := mul_le_mul_of_nonneg_left hnorm hη
    _ = ∑ i, η * v i := Finset.mul_sum ..
    _ ≤ ∑ i, lam i * v i := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hlam i) (hv i)
    _ = positiveFunctional lam v := (positiveFunctional_apply lam v).symm

omit [CompleteSpace E] in
theorem strict_local_minimum_of_positive_multipliers {m : ℕ}
    (F : E → (Fin m → ℝ)) (φ : E → ℝ) (z : E)
    (J : E ≃L[ℝ] (Fin m → ℝ)) (lam : Fin m → ℝ) (η : ℝ)
    (hη : 0 < η) (hlam : ∀ i, η ≤ lam i) (hzero : F z = 0)
    (hF : HasFDerivAt F (J : E →L[ℝ] (Fin m → ℝ)) z)
    (hφ : HasFDerivAt φ ((positiveFunctional lam).comp J.toContinuousLinearMap) z) :
    ∀ᶠ w in 𝓝 z, w ≠ z → (∀ i, 0 ≤ F w i) → φ z < φ w := by
  let M : ℝ := max 1 ‖(J.symm : (Fin m → ℝ) →L[ℝ] E)‖
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMi : ‖(J.symm : (Fin m → ℝ) →L[ℝ] E)‖ ≤ M := le_max_right _ _
  let K : E → ℝ := fun w ↦ φ w - positiveFunctional lam (F w)
  have hK : HasFDerivAt K (0 : E →L[ℝ] ℝ) z := by
    convert! hφ.sub ((positiveFunctional lam).hasFDerivAt.comp z hF) using 1
    simp
  have hremF := (isLittleO_iff.mp (hasFDerivAt_iff_isLittleO.mp hF))
    (show 0 < 1 / (2 * M) by positivity)
  have hremK := (isLittleO_iff.mp (hasFDerivAt_iff_isLittleO.mp hK))
    (show 0 < η / (4 * M) by positivity)
  filter_upwards [hremF, hremK] with w hwF hwK hne hfeas
  have hd : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hFbound : ‖F w - J (w - z)‖ ≤ (1 / (2 * M)) * ‖w - z‖ := by
    simpa [hzero] using hwF
  have hKbound : |K w - K z| ≤ η / (4 * M) * ‖w - z‖ := by
    simpa [Real.norm_eq_abs] using hwK
  have hJbound : ‖w - z‖ ≤ M * ‖J (w - z)‖ := by
    calc
      ‖w - z‖ = ‖J.symm (J (w - z))‖ := by rw [J.symm_apply_apply]
      _ ≤ ‖(J.symm : (Fin m → ℝ) →L[ℝ] E)‖ * ‖J (w - z)‖ :=
        J.symm.toContinuousLinearMap.le_opNorm (J (w - z))
      _ ≤ M * ‖J (w - z)‖ := mul_le_mul_of_nonneg_right hMi (norm_nonneg _)
  have htri : ‖J (w - z)‖ ≤ ‖F w‖ + ‖F w - J (w - z)‖ := by
    exact norm_le_norm_add_norm_sub (F w) (J (w - z))
  have hhalf : M * ((1 / (2 * M)) * ‖w - z‖) = ‖w - z‖ / 2 := by
    field_simp
  have hscale : ‖w - z‖ / 2 ≤ M * ‖F w‖ := by
    nlinarith [mul_le_mul_of_nonneg_left htri hM.le,
      mul_le_mul_of_nonneg_left hFbound hM.le]
  have hpos := positiveFunctional_ge_norm lam (F w) η hη.le hlam hfeas
  have hKlower := (abs_le.mp hKbound).1
  have hidentity : φ w - φ z = (K w - K z) + positiveFunctional lam (F w) := by
    simp only [K, hzero, map_zero]
    ring
  have hbudget : M * (η / (4 * M) * ‖w - z‖) = η * ‖w - z‖ / 4 := by
    field_simp
  have hpositive : 0 < η * ‖w - z‖ := mul_pos hη hd
  nlinarith [mul_le_mul_of_nonneg_left hscale hη.le,
    mul_le_mul_of_nonneg_left hpos hM.le,
    mul_le_mul_of_nonneg_left hKlower hM.le]

#print axioms positiveFunctional_ge_norm
#print axioms strict_local_minimum_of_positive_multipliers

end HeadComplexity.CertifiedContraction
