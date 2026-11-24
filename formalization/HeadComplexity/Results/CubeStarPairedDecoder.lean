import HeadComplexity.Results.CubeStarCompactDecoder

set_option linter.style.header false

/-!
# Jointly chosen paired cube decoders

The row directions and affine row numerators may depend on the entire family
of independently labelled columns. Compact column offsets and a paired
baseline give exact zero-column cancellation with twice the head budget.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- A family-dependent decoder. Within the given family, the directions and
affine row numerators are shared. The paired baseline is part of the score. -/
def HasCompactPairedCubeDecoder (k s H : ℕ) : Prop :=
  ∀ table : (Fin k → Bool) → Fin s → Bool, ∀ η : ℝ, 0 < η →
    ∃ d r : Fin H → Fin k → ℝ, ∃ c : Fin H → ℝ,
      ∃ a b : Fin H → Fin s → ℝ,
        (∀ h i, 0 < d h i) ∧
        (∀ h j, 1 < b h j ∧ b h j < 1 + η) ∧
        ∀ x j, 0 < outputSign (table x j) *
          ∑ h, ((affineValue (c h) (r h) x + a h j) /
            (b h j + ∑ i, d h i * boolToReal (x i)) -
            affineValue (c h) (r h) x /
              (1 + ∑ i, d h i * boolToReal (x i)))

private theorem paired_negative_affine_pos {n : ℕ} (C : ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (hC : (∑ i, -b i) < C) (bits : Fin n → Bool) :
    0 < affineValue C b bits := by
  have hs : (∑ i, b i) ≤ ∑ i, b i * boolToReal (bits i) := by
    apply Finset.sum_le_sum
    intro i _
    cases bits i <;> simp [boolToReal, (hb i).le]
  simp only [Finset.sum_neg_distrib] at hC
  unfold affineValue
  linarith

private theorem paired_complement_sum {k : ℕ} (d : Fin k → ℝ)
    (x : Fin k → Bool) :
    (∑ i, d i) - ∑ i, d i * boolToReal (x i) =
      ∑ i, d i * boolToReal (!(x i)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

/-- Compile arbitrary real paired scores, without imposing labels. The compact
range pays for positivity even at multihot column inputs. -/
theorem exists_reverse_cube_star_paired_score {k s H : ℕ}
    (η : ℝ) (hη : 0 < η) (hmarginη : (s : ℝ) * η < 1 + η)
    (d r : Fin H → Fin k → ℝ) (c : Fin H → ℝ) (a b : Fin H → Fin s → ℝ)
    (hd : ∀ h i, 0 < d h i) (hb : ∀ h j, 1 < b h j ∧ b h j < 1 + η) :
    ∃ L : ReverseCubeStarData k s (H + H), ∀ x j,
      L.score (cubeStarInput x j) =
        ∑ h, ((affineValue (c h) (r h) (fun i ↦ !(x i)) + a h j) /
          (b h j + ∑ i, d h i * boolToReal (!(x i))) -
          affineValue (c h) (r h) (fun i ↦ !(x i)) /
            (1 + ∑ i, d h i * boolToReal (!(x i)))) := by
  classical
  let C (h : Fin H) := 1 + η + ∑ i, d h i
  let A₀ (h : Fin H) := c h + ∑ i, r h i
  let A (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (fun i ↦ -r h i) (a h)
  let A' (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (r h) (fun _ ↦ 0)
  let B (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (fun i ↦ -d h i) (fun j ↦ b h j - (1 + η))
  let B' (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (fun i ↦ -d h i) (fun _ ↦ -η)
  have hnegative (h : Fin H) (i : Fin (k + s)) : B h i < 0 := by
    refine Fin.addCases ?_ ?_ i
    · intro l
      simpa [B] using neg_neg_of_pos (hd h l)
    · intro j
      simpa [B] using sub_neg.mpr (hb h j).2
  have hnegative' (h : Fin H) (i : Fin (k + s)) : B' h i < 0 := by
    refine Fin.addCases ?_ ?_ i
    · intro l
      simpa [B'] using neg_neg_of_pos (hd h l)
    · intro j
      simpa [B'] using neg_neg_of_pos hη
  have hmargin (h : Fin H) : (∑ i, -B h i) < C h := by
    have hsum : (∑ j : Fin s, (1 + η - b h j)) ≤ (s : ℝ) * η := by
      calc
        _ ≤ ∑ _j : Fin s, η := by
          apply Finset.sum_le_sum
          intro j _
          linarith [(hb h j).1]
        _ = (s : ℝ) * η := by simp
    simp only [B, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_neg, neg_sub] at ⊢
    dsimp [C]
    nlinarith
  have hmargin' (h : Fin H) : (∑ i, -B' h i) < C h := by
    simp only [B', Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [C]
    nlinarith
  let L : ReverseCubeStarData k s (H + H) :=
    { a₀ := Fin.addCases A₀ (fun h ↦ -A₀ h)
      b₀ := Fin.addCases C C
      a := Fin.addCases A A'
      b := Fin.addCases B B'
      positive := by
        intro h bits
        refine Fin.addCases ?_ ?_ h
        · intro l
          simpa only [Fin.addCases_left] using
            paired_negative_affine_pos _ _ (hnegative l) (hmargin l) bits
        · intro l
          simpa only [Fin.addCases_right] using
            paired_negative_affine_pos _ _ (hnegative' l) (hmargin' l) bits
      negative := by
        intro h i
        refine Fin.addCases ?_ ?_ h
        · intro l
          simpa only [Fin.addCases_left] using hnegative l i
        · intro l
          simpa only [Fin.addCases_right] using hnegative' l i
      zero_column := by
        intro x
        simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
        have hden (h : Fin H) :
            affineValue (C h) (B' h) (Fin.addCases x (fun _ : Fin s ↦ false)) =
              affineValue (C h) (B h) (Fin.addCases x (fun _ : Fin s ↦ false)) := by
          simp [B, B', affineValue, Fin.sum_univ_add, boolToReal]
        have hnum (h : Fin H) :
            affineValue (-A₀ h) (A' h) (Fin.addCases x (fun _ : Fin s ↦ false)) =
              -affineValue (A₀ h) (A h) (Fin.addCases x (fun _ : Fin s ↦ false)) := by
          simp only [A, A', affineValue, Fin.sum_univ_add, Fin.addCases_left,
            Fin.addCases_right, boolToReal, Bool.false_eq_true, ite_false,
            mul_zero, Finset.sum_const_zero, add_zero, neg_mul,
            Finset.sum_neg_distrib]
          ring
        simp only [hden, hnum, neg_div, Finset.sum_neg_distrib, add_neg_cancel] }
  refine ⟨L, ?_⟩
  intro x j
  have hnum (h : Fin H) : affineValue (A₀ h) (A h) (cubeStarInput x j) =
      affineValue (c h) (r h) (fun i ↦ !(x i)) + a h j := by
    simp only [A₀, A, affineValue, cubeStarInput, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, neg_mul, Finset.sum_neg_distrib]
    have hj : (∑ l : Fin s, a h l * boolToReal (decide (l = j))) = a h j := by
      simp [boolToReal]
    rw [hj, ← paired_complement_sum]
    ring
  have hnum' (h : Fin H) : affineValue (-A₀ h) (A' h) (cubeStarInput x j) =
      -affineValue (c h) (r h) (fun i ↦ !(x i)) := by
    simp only [A₀, A', affineValue, cubeStarInput, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
    rw [← paired_complement_sum]
    ring
  have hden (h : Fin H) : affineValue (C h) (B h) (cubeStarInput x j) =
      b h j + ∑ i, d h i * boolToReal (!(x i)) := by
    simp only [C, B, affineValue, cubeStarInput, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, neg_mul, Finset.sum_neg_distrib]
    have hj : (∑ l : Fin s, (b h l - (1 + η)) * boolToReal (decide (l = j))) =
        b h j - (1 + η) := by simp [boolToReal]
    rw [hj, ← paired_complement_sum]
    ring
  have hden' (h : Fin H) : affineValue (C h) (B' h) (cubeStarInput x j) =
      1 + ∑ i, d h i * boolToReal (!(x i)) := by
    simp only [C, B', affineValue, cubeStarInput, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, neg_mul, Finset.sum_neg_distrib]
    have hj : (∑ l : Fin s, η * boolToReal (decide (l = j))) = η := by
      simp [boolToReal]
    rw [hj, ← paired_complement_sum]
    ring
  simp only [ReverseCubeStarData.score, L, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, hnum, hnum', hden, hden', neg_div,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- The full independent-label family compiles into one reverse score.
There are exactly two banks of `H` heads; no uncharged axis repair remains. -/
theorem hasReverseCubeStarCompiler_of_compact_paired {k s H : ℕ}
    (hdecoder : HasCompactPairedCubeDecoder k s H) :
    HasReverseCubeStarCompiler k s (H + H) := by
  classical
  intro table
  let η : ℝ := 1 / ((s : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * ((s : ℝ) + 1) = 1 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨d, r, c, a, b, hd, hb, hsign⟩ :=
    hdecoder (fun x j ↦ table (fun i ↦ !(x i)) j) η hη
  obtain ⟨L, hL⟩ := exists_reverse_cube_star_paired_score η hη (by nlinarith)
    d r c a b hd hb
  refine ⟨H + H, le_rfl, L, fun x j ↦ ?_⟩
  rw [hL]
  simpa only [Bool.not_not] using hsign (fun i ↦ !(x i)) j

/-- Global transfer, including the exceptional face. The decoder hypothesis
is explicit; no asymptotic existence assertion is made here. -/
theorem worstCaseHeadComplexity_real_le_of_compact_paired_cube_decoder {k s H : ℕ}
    (hs : 0 < s) (hdecoder : HasCompactPairedCubeDecoder k s H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      22 * (2 : ℝ) ^ s * (H + H) / s + 2 ^ (k + 1) := by
  have ht := worstCaseHeadComplexity_real_le_of_cube_star_compiler hs
    (hasReverseCubeStarCompiler_of_compact_paired hdecoder)
  simpa only [Nat.cast_add] using ht

end HeadComplexity.AxisZeroGluing
