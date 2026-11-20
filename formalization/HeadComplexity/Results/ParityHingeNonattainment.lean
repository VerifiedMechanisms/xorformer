import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# A positive unattained hinge-loss infimum

Every positive-denominator affine fraction on a square has parity hinge
loss strictly greater than two. An explicit admissible family approaches
two. This audits nonattainment in an optimization route; it is not a
head-count lower bound for the main asymptotic question.
-/

namespace HeadComplexity

/-- The four labels are positive, negative, negative, positive. -/
noncomputable def squareParityHinge
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) : ℝ :=
  max 0 (1 - a₀ / b₀) + max 0 (1 + a₁ / b₁) +
  max 0 (1 + a₂ / b₂) + max 0 (1 - a₃ / b₃)

theorem sub_le_mul_hinge (q v : ℝ) (hq : 0 < q) :
    q - v ≤ q * max 0 (1 - v / q) := by
  have h := mul_le_mul_of_nonneg_left (le_max_right 0 (1 - v / q)) hq.le
  have heq : q * (1 - v / q) = q - v := by field_simp
  rwa [heq] at h

/-- The affine identities alone suffice; no extra slope assumption is used. -/
theorem squareParityHinge_gt_two
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ)
    (ha : a₀ + a₃ = a₁ + a₂) (hb : b₀ + b₃ = b₁ + b₂)
    (h₀ : 0 < b₀) (h₁ : 0 < b₁) (h₂ : 0 < b₂) (h₃ : 0 < b₃) :
    2 < squareParityHinge a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ := by
  let M := max (max b₀ b₁) (max b₂ b₃)
  have hm₀ : b₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hm₁ : b₁ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hm₂ : b₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hm₃ : b₃ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 < M := h₀.trans_le hm₀
  have hmass : 2 * M < b₀ + b₁ + b₂ + b₃ := by
    dsimp [M]
    rcases le_total b₀ b₁ with h01 | h10 <;>
      rcases le_total b₂ b₃ with h23 | h32
    · rw [max_eq_right h01, max_eq_right h23]
      rcases le_total b₁ b₃ with h13 | h31
      · rw [max_eq_right h13]; linarith
      · rw [max_eq_left h31]; linarith
    · rw [max_eq_right h01, max_eq_left h32]
      rcases le_total b₁ b₂ with h12 | h21
      · rw [max_eq_right h12]; linarith
      · rw [max_eq_left h21]; linarith
    · rw [max_eq_left h10, max_eq_right h23]
      rcases le_total b₀ b₃ with h03 | h30
      · rw [max_eq_right h03]; linarith
      · rw [max_eq_left h30]; linarith
    · rw [max_eq_left h10, max_eq_left h32]
      rcases le_total b₀ b₂ with h02 | h20
      · rw [max_eq_right h02]; linarith
      · rw [max_eq_left h20]; linarith
  have e₀ := sub_le_mul_hinge b₀ a₀ h₀
  have e₁ := sub_le_mul_hinge b₁ (-a₁) h₁
  have e₂ := sub_le_mul_hinge b₂ (-a₂) h₂
  have e₃ := sub_le_mul_hinge b₃ a₃ h₃
  simp only [neg_div, sub_neg_eq_add] at e₁ e₂
  have u₀ := mul_le_mul_of_nonneg_right hm₀ (le_max_left 0 (1 - a₀ / b₀))
  have u₁ := mul_le_mul_of_nonneg_right hm₁ (le_max_left 0 (1 + a₁ / b₁))
  have u₂ := mul_le_mul_of_nonneg_right hm₂ (le_max_left 0 (1 + a₂ / b₂))
  have u₃ := mul_le_mul_of_nonneg_right hm₃ (le_max_left 0 (1 - a₃ / b₃))
  unfold squareParityHinge
  nlinarith

/-- The numerator values are affine: 1 + (-3-2t) = (-1-t)+(-1-t).
The denominator values come from 1+t(x₁+x₂), so t>0 is admissible. -/
theorem squareParityHinge_approaching_family (t : ℝ) (ht : 0 < t) :
    squareParityHinge 1 (-1-t) (-1-t) (-3-2*t)
      1 (1+t) (1+t) (1+2*t) = 2 + 2/(1+2*t) := by
  have h1 : (1 : ℝ) + t ≠ 0 := by positivity
  have h2 : (1 : ℝ) + 2*t ≠ 0 := by positivity
  have hratio : (-1-t)/(1+t) = -1 := by field_simp; ring
  have hlast : 0 ≤ 1 - (-3-2*t)/(1+2*t) := by
    have : (-3-2*t)/(1+2*t) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  unfold squareParityHinge
  rw [hratio, max_eq_right hlast]
  norm_num
  field_simp
  ring

theorem exists_squareParityHinge_lt_two_add (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      squareParityHinge 1 (-1-t) (-1-t) (-3-2*t)
        1 (1+t) (1+t) (1+2*t) < 2 + ε := by
  refine ⟨1/ε, by positivity, ?_⟩
  rw [squareParityHinge_approaching_family _ (by positivity)]
  have hden : 0 < (1 : ℝ) + 2 * (1 / ε) := by positivity
  have heq : ε * (1 + 2 * (1 / ε)) = ε + 2 := by field_simp
  have hfrac : 2 / (1 + 2 * (1 / ε)) < ε := by
    apply (div_lt_iff₀ hden).mpr
    rw [heq]
    linarith
  linarith

/-- Losses of all affine fractions whose denominators are positive on the
square. This includes every admissible one-head score after bias absorption. -/
def positiveAffineSquareParityLosses : Set ℝ :=
  {l | ∃ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ,
    a₀ + a₃ = a₁ + a₂ ∧ b₀ + b₃ = b₁ + b₂ ∧
    0 < b₀ ∧ 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧
    l = squareParityHinge a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃}

theorem two_not_mem_positiveAffineSquareParityLosses :
    (2 : ℝ) ∉ positiveAffineSquareParityLosses := by
  rintro ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, ha, hb, h₀, h₁, h₂, h₃, heq⟩
  have h := squareParityHinge_gt_two a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ ha hb h₀ h₁ h₂ h₃
  linarith

theorem isGLB_positiveAffineSquareParityLosses :
    IsGLB positiveAffineSquareParityLosses (2 : ℝ) := by
  constructor
  · rintro l ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, ha, hb, h₀, h₁, h₂, h₃, heq⟩
    rw [heq]
    exact (squareParityHinge_gt_two a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ ha hb h₀ h₁ h₂ h₃).le
  · intro z hz
    by_contra h
    have hz2 : 2 < z := lt_of_not_ge h
    obtain ⟨t, ht, hlt⟩ := exists_squareParityHinge_lt_two_add ((z-2)/2) (by linarith)
    have hmem : squareParityHinge 1 (-1-t) (-1-t) (-3-2*t)
        1 (1+t) (1+t) (1+2*t) ∈ positiveAffineSquareParityLosses := by
      refine ⟨1, -1-t, -1-t, -3-2*t, 1, 1+t, 1+t, 1+2*t,
        ?_, ?_, by norm_num, by positivity, by positivity, by positivity, rfl⟩ <;> ring
    have := hz hmem
    linarith

end HeadComplexity
