import HeadComplexity.Results.OddKernelNormalization

set_option linter.style.header false

/-!
# Returning positive odd kernels to the original atom model

Strictly positive kernel parameters have an exact two-atom realization.
Weakly positive parameters can be moved inward while preserving every
strict Boolean sign. The number of heads and input dimension are explicit.
-/

namespace HeadComplexity.OddKernel

open scoped BigOperators
open Filter Topology

variable {n H : ℕ}

theorem centered_affine (v : Fin n → ℝ) (x : Fin n → Bool) :
    affineValue (-(∑ i, v i)) (fun i ↦ 2 * v i) x = dot v x := by
  rw [affine_center]
  rw [← Finset.mul_sum]
  have he : (fun i ↦ 2 * v i / 2) = v := by ext i; ring
  rw [he]
  ring

theorem exists_atoms_of_strict_parameters
    (u w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hs : (∑ i, w i) < 1) :
    ∃ p m : FracAtom n, ∀ x, p.eval x + m.eval x = value u w x := by
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ ↦ (hw i).le)
  let a₀ := -(∑ i, u i) / 2
  let a := fun i ↦ u i
  let p := FracAtom.ofPositiveAffineRatio a₀ a (1 - ∑ i, w i)
    (fun i ↦ 2 * w i) (by linarith) (fun i ↦ mul_pos (by norm_num) (hw i))
  let m := FracAtom.ofNegativeAffineRatio a₀ a (1 + ∑ i, w i)
    (fun i ↦ -(2 * w i)) (by linarith) (fun i ↦ by simpa using hw i)
    (by simp only [neg_neg, ← Finset.mul_sum]; linarith)
  refine ⟨p, m, ?_⟩
  intro x
  have ha : affineValue a₀ a x = dot u x / 2 := by
    rw [affine_center]
    simp [a₀, a, dot, div_mul_eq_mul_div, ← Finset.sum_div]
    ring
  have hp : affineValue (1 - ∑ i, w i) (fun i ↦ 2 * w i) x =
      1 + dot w x := by
    rw [show 1 - (∑ i, w i) = 1 + (-(∑ i, w i)) by ring,
      affineValue_const_add, centered_affine]
  have hm : affineValue (1 + ∑ i, w i) (fun i ↦ -(2 * w i)) x =
      1 - dot w x := by
    have he := centered_affine (fun i ↦ -w i) x
    simp only [Finset.sum_neg_distrib, neg_neg, mul_neg, dot, neg_mul] at he
    rw [← Finset.sum_neg_distrib] at he
    rw [affineValue_const_add, he]
    simp [dot, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hd := abs_lt.mp ((abs_dot_le_sum w (fun i ↦ (hw i).le) x).trans_lt hs)
  have hd1 : 1 + dot w x ≠ 0 := ne_of_gt (by linarith [hd.1])
  have hd2 : 1 - dot w x ≠ 0 := ne_of_gt (by linarith [hd.2])
  have hd3 := (value_den_pos w (fun i ↦ (hw i).le) hs x).ne'
  dsimp [p, m]
  rw [FracAtom.ofPositiveAffineRatio_eval, FracAtom.ofNegativeAffineRatio_eval,
    ha, hp, hm]
  unfold value
  field_simp
  ring

theorem fracComputable_of_strict_parameters {f : (Fin n → Bool) → Bool}
    (u w : Fin H → Fin n → ℝ) (hw : ∀ h i, 0 < w h i)
    (hs : ∀ h, (∑ i, w h i) < 1)
    (hsg : ∀ x, if f x then 0 < ∑ h, value (u h) (w h) x
      else (∑ h, value (u h) (w h) x) < 0) :
    fracComputable n (H + H) f := by
  classical
  choose p m hpm using fun h ↦ exists_atoms_of_strict_parameters (u h) (w h) (hw h) (hs h)
  refine ⟨Fin.addCases p m, 0, ?_⟩
  intro x
  simp only [zero_add, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  rw [← Finset.sum_add_distrib]
  simp only [hpm]
  cases hx : f x
  · have hn : (∑ h, value (u h) (w h) x) < 0 := by simpa [hx] using hsg x
    simpa [hx] using hn.le
  · simpa [hx] using hsg x

theorem exists_strict_parameters {f : (Fin n → Bool) → Bool}
    (u w : Fin H → Fin n → ℝ) (hw : ∀ h i, 0 ≤ w h i)
    (hs : ∀ h, (∑ i, w h i) < 1)
    (hsg : ∀ x, if f x then 0 < ∑ h, value (u h) (w h) x
      else (∑ h, value (u h) (w h) x) < 0) :
    ∃ w' : Fin H → Fin n → ℝ,
      (∀ h i, 0 < w' h i) ∧ (∀ h, (∑ i, w' h i) < 1) ∧
      ∀ x, if f x then 0 < ∑ h, value (u h) (w' h) x
        else (∑ h, value (u h) (w' h) x) < 0 := by
  classical
  let w' := fun ε h i ↦ w h i + ε
  have hc (x : Fin n → Bool) : ContinuousAt
      (fun ε : ℝ ↦ ∑ h, value (u h) (w' ε h) x) 0 := by
    have hh (h : Fin H) : ContinuousAt
        (fun ε : ℝ ↦ value (u h) (w' ε h) x) 0 := by
      apply ContinuousAt.div continuousAt_const
      · unfold dot w'
        fun_prop
      · simpa [dot, w'] using (value_den_pos (w h) (hw h) (hs h) x).ne'
    fun_prop
  have he : ∀ᶠ ε : ℝ in 𝓝 0,
      (∀ h, (∑ i, w' ε h i) < 1) ∧
      ∀ x, if f x then 0 < ∑ h, value (u h) (w' ε h) x
        else (∑ h, value (u h) (w' ε h) x) < 0 := by
    apply Filter.Eventually.and
    · apply Filter.eventually_all.mpr
      intro h
      apply (show ContinuousAt (fun ε : ℝ ↦ ∑ i, w' ε h i) 0 from by
        dsimp [w']; fun_prop).eventually_lt continuousAt_const
      simpa [w'] using hs h
    · apply Filter.eventually_all.mpr
      intro x
      cases hx : f x
      · simp only [Bool.false_eq_true, ite_false]
        apply (hc x).eventually_lt continuousAt_const
        simpa [hx, w'] using hsg x
      · simp only [ite_true]
        apply continuousAt_const.eventually_lt (hc x)
        simpa [hx, w'] using hsg x
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp he
  have hp : 0 < radius / 2 := by positivity
  have hgood := hball (show radius / 2 ∈ Metric.ball (0 : ℝ) radius from by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hp]
    linarith)
  exact ⟨w' (radius / 2), fun h i ↦ add_pos_of_nonneg_of_pos (hw h i) hp,
    hgood.1, hgood.2⟩

/-- Every strict positive-kernel sign representation returns to the unchanged
model with exactly two original heads per kernel, including zero coordinates. -/
theorem fracComputable_of_parameters {f : (Fin n → Bool) → Bool}
    (u w : Fin H → Fin n → ℝ) (hw : ∀ h i, 0 ≤ w h i)
    (hs : ∀ h, (∑ i, w h i) < 1)
    (hsg : ∀ x, if f x then 0 < ∑ h, value (u h) (w h) x
      else (∑ h, value (u h) (w h) x) < 0) :
    fracComputable n (H + H) f := by
  obtain ⟨w', hw', hs', hsg'⟩ := exists_strict_parameters u w hw hs hsg
  exact fracComputable_of_strict_parameters u w' hw' hs' hsg'

end HeadComplexity.OddKernel
