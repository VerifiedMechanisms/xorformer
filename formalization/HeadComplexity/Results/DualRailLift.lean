import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
# Exact positive-affine lifting on complementary coordinate pairs

This changes neither the attention model nor its denominator condition. An
arbitrary affine denominator positive on a logical cube can be represented by
a strictly positive-coefficient affine denominator on twice as many physical
coordinates, exactly on the complementary-pair subset. No extension or
whole-cube synthesis claim is made about prescribed output signs.
-/

namespace HeadComplexity

open scoped BigOperators

/-- Complementary rails encode a logical input in two coordinate blocks. -/
def dualRailBits {n : ℕ} (bits : Fin n → Bool) : Fin (n + n) → Bool :=
  Fin.addCases bits (fun i ↦ !(bits i))

/-- Strictly positive rail slopes induce arbitrary signed logical slopes. -/
noncomputable def dualRailSlopes {n : ℕ} (a : Fin n → ℝ) (ε : ℝ) :
    Fin (n + n) → ℝ :=
  Fin.addCases (fun i ↦ max (a i) 0 + ε) (fun i ↦ max (-a i) 0 + ε)

/-- The constant removes the contribution of the complementary rail. -/
noncomputable def dualRailConstant {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (ε : ℝ) : ℝ :=
  b - ∑ i, max (-a i) 0 - (n : ℝ) * ε

private theorem dualRail_scalar (a ε : ℝ) (bit : Bool) :
    (max a 0 + ε) * boolToReal bit +
      (max (-a) 0 + ε) * boolToReal (!bit) =
    max (-a) 0 + ε + a * boolToReal bit := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0)]
    cases bit
    · simp [boolToReal]
    · simp [boolToReal]
      ring
  · have hneg : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right hneg, max_eq_left (by linarith : 0 ≤ -a)]
    cases bit <;> simp [boolToReal]

/-- The denominator agrees exactly on every complementary-rail input. -/
theorem affineValue_dualRail (n : ℕ) (b : ℝ) (a : Fin n → ℝ) (ε : ℝ)
    (bits : Fin n → Bool) :
    affineValue (dualRailConstant b a ε) (dualRailSlopes a ε) (dualRailBits bits) =
      affineValue b a bits := by
  unfold affineValue dualRailConstant dualRailSlopes dualRailBits
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [← Finset.sum_add_distrib]
  simp_rw [dualRail_scalar]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Every physical slope is strictly positive, including logical zero slopes. -/
theorem dualRailSlopes_pos {n : ℕ} (a : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (i : Fin (n + n)) : 0 < dualRailSlopes a ε i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [dualRailSlopes, Fin.addCases_left]
    exact add_pos_of_nonneg_of_pos (le_max_right _ _) hε
  · intro j
    simp only [dualRailSlopes, Fin.addCases_right]
    exact add_pos_of_nonneg_of_pos (le_max_right _ _) hε

/-- Margin condition sufficient for a positive physical constant. -/
theorem dualRailConstant_pos {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (ε : ℝ)
    (hmargin : (n : ℝ) * ε < b - ∑ i, max (-a i) 0) :
    0 < dualRailConstant b a ε := by
  unfold dualRailConstant
  linarith

/-- The lifted denominator is positive on the entire physical cube. -/
theorem affineValue_dualRail_pos {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hmargin : (n : ℝ) * ε < b - ∑ i, max (-a i) 0)
    (physicalBits : Fin (n + n) → Bool) :
    0 < affineValue (dualRailConstant b a ε) (dualRailSlopes a ε) physicalBits :=
  affineValue_pos _ _ (dualRailConstant_pos b a ε hmargin)
    (dualRailSlopes_pos a ε hε) physicalBits

/-- Positivity on the logical cube supplies the exact margin used in the lift. -/
theorem affineValue_negativeCorner {n : ℕ} (b : ℝ) (a : Fin n → ℝ) :
    affineValue b a (fun i ↦ decide (a i < 0)) = b - ∑ i, max (-a i) 0 := by
  unfold affineValue
  have hterm : ∀ i, a i * boolToReal (decide (a i < 0)) = -max (-a i) 0 := by
    intro i
    by_cases ha : a i < 0
    · simp [ha, boolToReal, max_eq_left (by linarith : 0 ≤ -a i)]
    · have hanonneg : 0 ≤ a i := le_of_not_gt ha
      simp [ha, boolToReal, max_eq_right (by linarith : -a i ≤ 0)]
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  ring

/-- Every positive logical affine denominator has an exact admissible lift. -/
theorem exists_positive_dualRail_lift {n : ℕ} (b : ℝ) (a : Fin n → ℝ)
    (hpositive : ∀ bits, 0 < affineValue b a bits) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < dualRailConstant b a ε ∧
      (∀ i, 0 < dualRailSlopes a ε i) ∧
      (∀ bits, affineValue (dualRailConstant b a ε) (dualRailSlopes a ε)
        (dualRailBits bits) = affineValue b a bits) ∧
      (∀ physicalBits, 0 < affineValue (dualRailConstant b a ε)
        (dualRailSlopes a ε) physicalBits) := by
  let margin := b - ∑ i, max (-a i) 0
  have hm : 0 < margin := by
    simpa only [affineValue_negativeCorner] using
      hpositive (fun i ↦ decide (a i < 0))
  let ε := margin / (2 * ((n : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : (n : ℝ) * ε < margin := by
    dsimp [ε]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
    nlinarith
  refine ⟨ε, hε, dualRailConstant_pos b a ε hsmall, dualRailSlopes_pos a ε hε,
    affineValue_dualRail n b a ε, ?_⟩
  exact affineValue_dualRail_pos b a ε hε hsmall

/-- An arbitrary positive logical affine ratio is one actual attention atom on
complementary rails. The atom itself is admissible on every physical input. -/
theorem exists_fracAtom_dualRail_affineRatio {n : ℕ}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ)
    (hpositive : ∀ bits, 0 < affineValue b₀ b bits) :
    ∃ φ : FracAtom (n + n), ∀ bits,
      φ.eval (dualRailBits bits) = affineValue a₀ a bits / affineValue b₀ b bits := by
  obtain ⟨ε, hε, hc, hs, hid, hfull⟩ := exists_positive_dualRail_lift b₀ b hpositive
  let nums : Fin (n + n) → ℝ := Fin.addCases a (fun _ ↦ 0)
  let φ := FracAtom.ofPositiveAffineRatio a₀ nums
    (dualRailConstant b₀ b ε) (dualRailSlopes b ε) hc hs
  refine ⟨φ, fun bits ↦ ?_⟩
  rw [show φ.eval (dualRailBits bits) =
    affineValue a₀ nums (dualRailBits bits) /
      affineValue (dualRailConstant b₀ b ε) (dualRailSlopes b ε)
        (dualRailBits bits) from
    FracAtom.ofPositiveAffineRatio_eval a₀ nums _ _ hc hs (dualRailBits bits), hid]
  congr 1
  unfold affineValue
  rw [Fin.sum_univ_add]
  simp only [nums, dualRailBits, Fin.addCases_left, Fin.addCases_right,
    zero_mul, Finset.sum_const_zero, add_zero]

end HeadComplexity
