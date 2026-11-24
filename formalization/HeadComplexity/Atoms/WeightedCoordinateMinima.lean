import Mathlib.Tactic

set_option linter.style.header false

/-! Algebraic ingredients for the diagonal coordinate-loss construction.
The analytic existence and perturbation arguments are in the companion note. -/
namespace HeadComplexity.WeightedCoordinateMinima
open Finset

theorem regression_square (A eta R W C : ℝ) (hW : W ≠ 0) :
    W * A ^ 2 - 2 * eta * R * A + eta ^ 2 * C =
      eta ^ 2 * C - eta ^ 2 * R ^ 2 / W + W * (A - eta * R / W) ^ 2 := by
  field_simp
  ring

theorem variance_identity {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (z i - ∑ j, p j * z j) ^ 2 =
      (∑ i, p i * (z i) ^ 2) - (∑ i, p i * z i) ^ 2 := by
  let mu := ∑ i, p i * z i
  have hexpand : ∀ i, p i * (z i - mu) ^ 2 =
      p i * (z i) ^ 2 - 2 * mu * (p i * z i) + mu ^ 2 * p i := by
    intro i
    ring
  change (∑ i, p i * (z i - mu) ^ 2) = (∑ i, p i * (z i) ^ 2) - mu ^ 2
  simp_rw [hexpand, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hp]
  change (∑ i, p i * (z i) ^ 2) - 2 * mu * mu + mu ^ 2 * 1 = _
  ring

theorem variance_nonneg {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∑ i, p i = 1) (hpos : ∀ i, 0 ≤ p i) :
    0 ≤ (∑ i, p i * (z i) ^ 2) - (∑ i, p i * z i) ^ 2 := by
  rw [← variance_identity p z hp]
  exact sum_nonneg fun i _ ↦ mul_nonneg (hpos i) (sq_nonneg _)

theorem log_curvature_bound (rootSum poleSum logVsecond m : ℝ)
    (hr : m - 1 < rootSum) (hp : poleSum < 1)
    (hv : -2 * poleSum ≤ logVsecond) :
    -2 * rootSum - logVsecond < -2 * (m - 2) := by linarith

theorem hessian_square (W a curvature x y : ℝ) :
    2 * W * x ^ 2 - 4 * W * a * x * y + (2 * W * a ^ 2 + curvature) * y ^ 2 =
      2 * W * (x - a * y) ^ 2 + curvature * y ^ 2 := by ring

theorem hessian_positive (W a curvature x y : ℝ)
    (hW : 0 < W) (hc : 0 < curvature) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < 2 * W * x ^ 2 - 4 * W * a * x * y + (2 * W * a ^ 2 + curvature) * y ^ 2 := by
  rw [hessian_square]
  have hterm : 0 ≤ 2 * W * (x - a * y) ^ 2 := by positivity
  by_cases hy : y = 0
  · have hx : x ≠ 0 := hxy.resolve_right (not_not.mpr hy)
    simp only [hy, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    positivity
  · have hypos := sq_pos_of_ne_zero hy
    have := mul_pos hc hypos
    linarith

theorem many_selector_numerator_negative (r k s : ℝ)
    (hk : 0 < k) (hr : 2 ≤ r) (hrk : r ≤ k) (hs : s ≤ r / (4 * k)) :
    1 - r + s ≤ -(3 / 4 : ℝ) := by
  have hq : r / (4 * k) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * k)).mpr
    nlinarith
  linarith

theorem two_samples_injective (A B t s : ℝ)
    (hA : A ≠ 0) (ht1 : t + 1 ≠ 0) (ht2 : t + 2 ≠ 0)
    (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0)
    (h1 : A / (t + 1) = B / (s + 1)) (h2 : A / (t + 2) = B / (s + 2)) :
    t = s ∧ A = B := by
  have he1 := (div_eq_div_iff ht1 hs1).mp h1
  have he2 := (div_eq_div_iff ht2 hs2).mp h2
  have hab : A = B := by nlinarith [he1, he2]
  constructor
  · rw [← hab] at he1
    have hz : A * (s - t) = 0 := by nlinarith [he1]
    have : s - t = 0 := (mul_eq_zero.mp hz).resolve_left hA
    linarith
  · exact hab

end HeadComplexity.WeightedCoordinateMinima
