import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- A finite geometric expansion normalized by a positive upper bound
on the denominator. This is an auxiliary approximation, not a head. -/
noncomputable def normalizedReciprocalSum (D : ℕ) (B L : ℝ) : ℝ :=
  (∑ k ∈ Finset.range D, (1 - B / L) ^ k) / L

/-- Exact remainder identity; no asymptotic notation is used. -/
theorem normalizedReciprocalSum_remainder (D : ℕ) (B L : ℝ)
    (hB : B ≠ 0) (hL : L ≠ 0) :
    1 / B - normalizedReciprocalSum D B L = (1 - B / L) ^ D / B := by
  have hg := geom_sum_mul_neg (1 - B / L) D
  have hs : (∑ k ∈ Finset.range D, (1 - B / L) ^ k) * B / L =
      1 - (1 - B / L) ^ D := by
    simpa only [sub_sub_cancel, ← mul_div_assoc] using hg
  dsimp [normalizedReciprocalSum]
  field_simp [hB, hL] at hs ⊢
  nlinarith

/-- Multiplying by an arbitrary signed numerator preserves the exact
relative-error formula. -/
theorem affineFraction_geometric_remainder (D : ℕ) (A B L : ℝ)
    (hB : B ≠ 0) (hL : L ≠ 0) :
    A / B - A * normalizedReciprocalSum D B L =
      (A / B) * (1 - B / L) ^ D := by
  have h := congrArg (fun t : ℝ => A * t)
    (normalizedReciprocalSum_remainder D B L hB hL)
  convert h using 1 <;> ring

/-- A condition-free error bound once a pointwise normalization keeps
the denominator between a fixed fraction of L and L. -/
theorem affineFraction_geometric_error_le (D : ℕ) (A B L r : ℝ)
    (hB : 0 < B) (hL : 0 < L)
    (hq0 : 0 ≤ 1 - B / L) (hqr : 1 - B / L ≤ r) :
    |A / B - A * normalizedReciprocalSum D B L| ≤ |A / B| * r ^ D := by
  rw [affineFraction_geometric_remainder D A B L hB.ne' hL.ne', abs_mul,
    abs_of_nonneg (pow_nonneg hq0 D)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hqr D) (abs_nonneg _)

/-- A sum of nonnegative active terms is uniformly conditioned relative
to its largest active coefficient, regardless of its global condition. -/
theorem largestTerm_normalization_bounds (n : ℕ) (B M : ℝ)
    (hM : 0 < M) (hlo : M ≤ B) (hhi : B ≤ ((n : ℝ) + 1) * M) :
    0 ≤ 1 - B / (((n : ℝ) + 1) * M) ∧
      1 - B / (((n : ℝ) + 1) * M) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hL : 0 < ((n : ℝ) + 1) * M := mul_pos hn hM
  constructor
  · exact sub_nonneg.mpr ((div_le_one hL).mpr hhi)
  · apply (le_div_iff₀ hn).mpr
    have hb : 1 ≤ B / M := (le_div_iff₀ hM).mpr (by simpa using hlo)
    have he : (1 - B / (((n : ℝ) + 1) * M)) * ((n : ℝ) + 1) =
        (n : ℝ) + 1 - B / M := by field_simp
    rw [he]
    linarith

/-- Largest-term normalization gives a convergence factor depending
only on the number of input coordinates. -/
theorem largestTerm_affineFraction_error_le (n D : ℕ) (A B M : ℝ)
    (hM : 0 < M) (hlo : M ≤ B) (hhi : B ≤ ((n : ℝ) + 1) * M) :
    |A / B - A * normalizedReciprocalSum D B (((n : ℝ) + 1) * M)| ≤
      |A / B| * ((n : ℝ) / ((n : ℝ) + 1)) ^ D := by
  obtain ⟨hq0, hqr⟩ := largestTerm_normalization_bounds n B M hM hlo hhi
  exact affineFraction_geometric_error_le D A B (((n : ℝ) + 1) * M)
    ((n : ℝ) / ((n : ℝ) + 1)) (hM.trans_le hlo) (by positivity) hq0 hqr

/-- Summing the geometric approximations costs only the total atomic
amplitude; the free bias introduces no error. -/
theorem sum_largestTerm_affineFraction_error_le {J : Type*} [Fintype J]
    (n D : ℕ) (A B M : J → ℝ) (c : ℝ)
    (hM : ∀ h, 0 < M h) (hlo : ∀ h, M h ≤ B h)
    (hhi : ∀ h, B h ≤ ((n : ℝ) + 1) * M h) :
    |(c + ∑ h, A h / B h) -
      (c + ∑ h, A h * normalizedReciprocalSum D (B h) (((n : ℝ) + 1) * M h))| ≤
      (∑ h, |A h / B h|) * ((n : ℝ) / ((n : ℝ) + 1)) ^ D := by
  classical
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun h _ =>
      largestTerm_affineFraction_error_le n D (A h) (B h) (M h)
        (hM h) (hlo h) (hhi h)))

end HeadComplexity
