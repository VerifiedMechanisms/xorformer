import HeadComplexity.Atoms.RoPE

set_option linter.style.header false

/-!
# Limitations of independent output shears

These identities audit a proposed proof route. They are not lower bounds for
Boolean head complexity. A finite Boolean cube may admit wholly different
numerators and denominators, even when a universal algebraic substitution fails.
-/

namespace HeadComplexity.RoPEShearObstruction

/-- Clearing the denominators after three independent fractional-linear
changes `a ↦ a/(1+t*a)` of the head outputs. -/
def clearedThree (a b c t u v : ℝ) : ℝ :=
  a * (1 + u * b) * (1 + v * c) +
    b * (1 + t * a) * (1 + v * c) +
    c * (1 + t * a) * (1 + u * b)

theorem clearedThree_expansion (a b c t u v : ℝ) :
    clearedThree a b c t u v = a + b + c +
      (t + u) * a * b + (t + v) * a * c + (u + v) * b * c +
      (t * u + t * v + u * v) * a * b * c := by
  unfold clearedThree
  ring

/-- The opposite-shear cancellation available for two terms cannot preserve
the additive cleared numerator for three independent terms unless all shears
are zero. This statement requires the displayed polynomial identity, not only
agreement of signs on a particular finite set. -/
theorem independent_three_shears_trivial (t u v : ℝ)
    (h : ∀ a b c : ℝ, clearedThree a b c t u v = a + b + c) :
    t = 0 ∧ u = 0 ∧ v = 0 := by
  have htu := h 1 1 0
  have htv := h 1 0 1
  have huv := h 0 1 1
  rw [clearedThree_expansion] at htu htv huv
  norm_num at htu htv huv
  constructor
  · linarith
  constructor <;> linarith

/-- The same pairwise coefficient obstruction holds at every head count at
least three. It only rules out this coefficient-preserving shear scheme. -/
theorem pairwise_shear_cancellation_trivial {H : ℕ} (hH : 3 ≤ H)
    (t : Fin H → ℝ) (ht : ∀ i j, i ≠ j → t i + t j = 0) :
    ∀ i, t i = 0 := by
  let a : Fin H := ⟨0, by omega⟩
  let b : Fin H := ⟨1, by omega⟩
  let c : Fin H := ⟨2, by omega⟩
  have hab : a ≠ b := by dsimp [a, b]; intro h; cases h
  have hac : a ≠ c := by dsimp [a, c]; intro h; cases h
  have hbc : b ≠ c := by dsimp [b, c]; intro h; cases h
  have htab := ht a b hab
  have htac := ht a c hac
  have htbc := ht b c hbc
  have ha : t a = 0 := by linarith
  intro i
  by_cases hi : i = a
  · simpa [hi] using ha
  · linarith [ht i a hi]

/-- Opposite shears preserve the sign of a pair when the new denominators
are positive, but rescale the pair by an input-dependent positive factor. -/
theorem opposite_shears_pair (a b t : ℝ)
    (ha : 1 + t * a ≠ 0) (hb : 1 - t * b ≠ 0) :
    a / (1 + t * a) + b / (1 - t * b) =
      (a + b) / ((1 + t * a) * (1 - t * b)) := by
  have ha' : 1 + a * t ≠ 0 := by simpa [mul_comm] using ha
  field_simp [ha, hb, ha']
  ring

/-- Preserving the sign of a pair does not justify replacing that pair inside
a larger sum. All denominators in this numerical example are positive. -/
theorem pair_replacement_changes_total_sign :
    (0 < (1 : ℝ) + 1) ∧
    (0 < (1 : ℝ) / (1 + 1 / 2) + 1 / (1 - 1 / 2)) ∧
    (1 + 1 - (5 : ℝ) / 2 < 0) ∧
    (0 < (1 : ℝ) / (1 + 1 / 2) + 1 / (1 - 1 / 2) - 5 / 2) := by
  norm_num

end HeadComplexity.RoPEShearObstruction
