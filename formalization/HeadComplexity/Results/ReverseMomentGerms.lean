import HeadComplexity.Results.ReverseMobius

set_option linter.style.header false

/-!
# Exact moment remainders for reverse Cauchy germs

These identities expose the leading coefficient without using numerical
smallness. They do not assert a universal sign-table construction or a
superconstant head saving.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- One exact step of the geometric remainder identity. -/
theorem reciprocal_remainder_step (t x : ℝ) (ht : t ≠ 0) (hx : t - x ≠ 0) :
    1 / (t - x) = 1 / t + x / (t * (t - x)) := by
  field_simp
  ring

/-- A vanishing weighted moment removes one order from a Cauchy sum. -/
theorem cauchy_moment_step {H : ℕ} (a p : Fin H → ℝ) (t δ : ℝ)
    (ht : t ≠ 0) (hd : ∀ h, t - δ * p h ≠ 0)
    (ha : ∑ h, a h = 0) :
    (∑ h, a h / (t - δ * p h)) =
      δ / t * ∑ h, a h * p h / (t - δ * p h) := by
  have he (h : Fin H) : a h / (t - δ * p h) =
      a h / t + δ / t * (a h * p h / (t - δ * p h)) := by
    field_simp [hd h]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ha, zero_div, zero_add,
    Finset.mul_sum]

/-- All lower moments vanish, so the remaining sum has an exact power
factor. This is valid for every order, not only a fixed finite jet. -/
theorem cauchy_moment_remainder {H : ℕ} (a p : Fin H → ℝ) (k : ℕ)
    (t δ : ℝ) (ht : t ≠ 0) (hd : ∀ h, t - δ * p h ≠ 0)
    (hm : ∀ l < k, ∑ h, a h * p h ^ l = 0) :
    (∑ h, a h / (t - δ * p h)) =
      (δ / t) ^ k * ∑ h, a h * p h ^ k / (t - δ * p h) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have ha : ∑ h, a h = 0 := by simpa using hm 0 (Nat.zero_lt_succ k)
    rw [cauchy_moment_step a p t δ ht hd ha]
    have hm' : ∀ l < k, ∑ h, (a h * p h) * p h ^ l = 0 := by
      intro l hl
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        hm (l + 1) (Nat.succ_lt_succ hl)
    rw [ih (fun h ↦ a h * p h) hm']
    simp only [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- The cubic family used in the four-head ten-query construction has
an exact remainder. The two cancellations are the only hypotheses. -/
theorem cauchy_cubic_remainder {H : ℕ} (A P A₃ P₂ : Fin H → ℝ)
    (t δ : ℝ) (ht : t ≠ 0)
    (hd : ∀ h, t - δ * P h - δ ^ 2 * P₂ h ≠ 0)
    (hA : ∑ h, A h = 0) (hAP : ∑ h, A h * P h = 0) :
    (∑ h, (δ * A h + δ ^ 3 * A₃ h) /
      (t - δ * P h - δ ^ 2 * P₂ h)) =
    δ ^ 3 * (∑ h, A₃ h / (t - δ * P h - δ ^ 2 * P₂ h) +
      (∑ h, A h * P₂ h) / t ^ 2 +
      ∑ h, A h * (P h + δ * P₂ h) ^ 2 /
        (t ^ 2 * (t - δ * P h - δ ^ 2 * P₂ h))) := by
  have he (h : Fin H) :
      (δ * A h + δ ^ 3 * A₃ h) / (t - δ * P h - δ ^ 2 * P₂ h) =
      δ * A h / t + δ ^ 2 * (A h * P h) / t ^ 2 +
      δ ^ 3 * (A₃ h / (t - δ * P h - δ ^ 2 * P₂ h) +
        (A h * P₂ h) / t ^ 2 +
        A h * (P h + δ * P₂ h) ^ 2 /
          (t ^ 2 * (t - δ * P h - δ ^ 2 * P₂ h))) := by
    field_simp [hd h]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hA, hAP]
  ring

end HeadComplexity.AxisZeroGluing
