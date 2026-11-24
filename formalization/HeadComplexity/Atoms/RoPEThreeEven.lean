import HeadComplexity.Atoms.RoPE

set_option linter.style.header false

/-!
# Antipodal algebra for three scalar rotary heads

These identities explain a limitation of the two-head reorientation argument.
They do not prove or refute a three-head Boolean comparison.
-/

namespace HeadComplexity.RoPEThreeEven

def cleared (T b₁ b₂ b₃ u₁ u₂ u₃ : ℝ) : ℝ :=
  T * (1 + b₁) * (1 + b₂) * (1 + b₃) +
    u₁ * (1 + b₂) * (1 + b₃) +
    u₂ * (1 + b₁) * (1 + b₃) +
    u₃ * (1 + b₁) * (1 + b₂)

def quadratic (T b₁ b₂ b₃ u₁ u₂ u₃ : ℝ) : ℝ :=
  T * (b₁ * b₂ + b₁ * b₃ + b₂ * b₃) +
    u₁ * (b₂ + b₃) + u₂ * (b₁ + b₃) + u₃ * (b₁ + b₂)

def oddPart (T b₁ b₂ b₃ u₁ u₂ u₃ : ℝ) : ℝ :=
  T * (b₁ + b₂ + b₃) + u₁ + u₂ + u₃ +
    T * b₁ * b₂ * b₃ + u₁ * b₂ * b₃ + u₂ * b₁ * b₃ + u₃ * b₁ * b₂

theorem cleared_decomposition (T b₁ b₂ b₃ u₁ u₂ u₃ : ℝ) :
    cleared T b₁ b₂ b₃ u₁ u₂ u₃ =
      T + quadratic T b₁ b₂ b₃ u₁ u₂ u₃ + oddPart T b₁ b₂ b₃ u₁ u₂ u₃ := by
  unfold cleared quadratic oddPart
  ring

theorem antipodal_average (T b₁ b₂ b₃ u₁ u₂ u₃ : ℝ) :
    (cleared T b₁ b₂ b₃ u₁ u₂ u₃ +
      cleared T (-b₁) (-b₂) (-b₃) (-u₁) (-u₂) (-u₃)) / 2 =
      T + quadratic T b₁ b₂ b₃ u₁ u₂ u₃ := by
  unfold cleared quadratic
  ring

/-- Strictly equal antipodal signs are exactly strict domination of the odd
part by the absolute value of the even part. -/
theorem same_sign_iff_odd_dominated (Q O : ℝ) :
    ((0 < Q + O ∧ 0 < Q - O) ∨ (Q + O < 0 ∧ Q - O < 0)) ↔ |O| < |Q| := by
  constructor
  · rintro (⟨hp, hm⟩ | ⟨hp, hm⟩)
    · have hQ : 0 < Q := by linarith
      rw [abs_of_pos hQ]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have hQ : Q < 0 := by linarith
      rw [abs_of_neg hQ]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · intro h
    by_cases hQ : 0 ≤ Q
    · rw [abs_of_nonneg hQ] at h
      obtain ⟨hl, hr⟩ := abs_lt.mp h
      exact Or.inl ⟨by linarith, by linarith⟩
    · rw [abs_of_neg (lt_of_not_ge hQ)] at h
      obtain ⟨hl, hr⟩ := abs_lt.mp h
      exact Or.inr ⟨by linarith, by linarith⟩

/-- The vector dual to the first pure pencil direction in the three-head
even quadratic has the displayed nonzero self-pairing in general. -/
theorem three_head_pencil_translation (T t b₁ b₂ b₃ u₁ u₂ u₃ : ℝ) :
    quadratic T (b₁ - t) (b₂ + t) (b₃ + t)
      (u₁ - (1 - T * t)) (u₂ + (1 - T * t)) (u₃ + (1 - T * t)) =
      quadratic T b₁ b₂ b₃ u₁ u₂ u₃ +
        2 * (b₁ + t * u₁) + (T * t ^ 2 - 2 * t) := by
  unfold quadratic
  ring

theorem three_head_pencil_null_iff (T t : ℝ) :
    T * t ^ 2 - 2 * t = 0 ↔ t = 0 ∨ T * t = 2 := by
  rw [show T * t ^ 2 - 2 * t = t * (T * t - 2) by ring]
  rw [mul_eq_zero, sub_eq_zero]

/-- In contrast, every parameter in the corresponding two-head pencil has
zero self-pairing; this is a genuinely special quadratic identity. -/
theorem two_head_pencil_translation (T t b₁ b₂ u₁ u₂ : ℝ) :
    T * b₁ * (b₂ + 2 * t) + u₁ * (b₂ + 2 * t) +
      (u₂ + 2 - 2 * T * t) * b₁ =
      T * b₁ * b₂ + u₁ * b₂ + u₂ * b₁ + 2 * (b₁ + t * u₁) := by
  ring

end HeadComplexity.RoPEThreeEven
