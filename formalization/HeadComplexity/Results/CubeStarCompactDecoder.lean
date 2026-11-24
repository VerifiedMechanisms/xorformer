import HeadComplexity.Results.CubeStarTransfer

set_option linter.style.header false

/-!
# Compact-offset cube decoder interface

An independently programmable column may vary its scalar numerators and
intercepts. The row directions are fixed before any column labels are chosen.
The arbitrary compactness range is essential for positivity at multihot
column inputs. This file proves the transfer, not existence of an improved
decoder.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- A bias-free scalar decoder with fixed positive row directions and
arbitrarily compact positive intercepts. The quantifier order permits all
columns to carry arbitrary, independently selected labels. -/
def HasCompactPositiveCubeDecoder (k H : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d : Fin H → Fin k → ℝ,
    (∀ h i, 0 < d h i) ∧
    ∀ target : (Fin k → Bool) → Bool,
      ∃ a b : Fin H → ℝ,
        (∀ h, 1 < b h ∧ b h < 1 + η) ∧
        ∀ x, 0 < outputSign (target x) *
          ∑ h, a h / (b h + ∑ i, d h i * boolToReal (x i))

private theorem negative_affine_pos {n : ℕ} (C : ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, b i < 0) (hC : (∑ i, -b i) < C) (bits : Fin n → Bool) :
    0 < affineValue C b bits := by
  have hs : (∑ i, b i) ≤ ∑ i, b i * boolToReal (bits i) := by
    apply Finset.sum_le_sum
    intro i _
    cases bits i <;> simp [boolToReal, (hb i).le]
  simp only [Finset.sum_neg_distrib] at hC
  unfold affineValue
  linarith

private theorem complement_affine_sum {k : ℕ} (d : Fin k → ℝ) (x : Fin k → Bool) :
    (∑ i, d i) - ∑ i, d i * boolToReal (x i) =
      ∑ i, d i * boolToReal (!(x i)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

/-- A compact decoder compiles every full-cube by one-star table with no
additional heads. All row directions are shared, but each column's labels,
numerators and intercepts are chosen independently. -/
theorem hasReverseCubeStarCompiler_of_compact {k s H : ℕ}
    (hdecoder : HasCompactPositiveCubeDecoder k H) :
    HasReverseCubeStarCompiler k s H := by
  classical
  let η : ℝ := 1 / ((s : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * ((s : ℝ) + 1) = 1 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨d, hd, hdecode⟩ := hdecoder η hη
  intro table
  have hex (j : Fin s) : ∃ a b : Fin H → ℝ,
      (∀ h, 1 < b h ∧ b h < 1 + η) ∧
      ∀ x : Fin k → Bool, 0 < outputSign (table (fun i ↦ !(x i)) j) *
        ∑ h, a h / (b h + ∑ i, d h i * boolToReal (x i)) :=
    hdecode (fun x ↦ table (fun i ↦ !(x i)) j)
  choose a b hb hsign using hex
  let C (h : Fin H) := 1 + η + ∑ i, d h i
  let A (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (fun _ ↦ 0) (fun j ↦ a j h)
  let B (h : Fin H) : Fin (k + s) → ℝ :=
    Fin.addCases (fun i ↦ -d h i) (fun j ↦ b j h - (1 + η))
  have hnegative (h : Fin H) (i : Fin (k + s)) : B h i < 0 := by
    refine Fin.addCases ?_ ?_ i
    · intro l
      simpa [B] using neg_neg_of_pos (hd h l)
    · intro j
      simpa [B] using sub_neg.mpr (hb j h).2
  have hmargin (h : Fin H) : (∑ i, -B h i) < C h := by
    have hsum : (∑ j : Fin s, (1 + η - b j h)) ≤ (s : ℝ) * η := by
      calc
        (∑ j : Fin s, (1 + η - b j h)) ≤ ∑ _j : Fin s, η := by
          apply Finset.sum_le_sum
          intro j _
          linarith [(hb j h).1]
        _ = (s : ℝ) * η := by simp
    simp only [B, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_neg, neg_sub] at ⊢
    dsimp [C]
    nlinarith
  let L : ReverseCubeStarData k s H :=
    { a₀ := fun _ ↦ 0
      b₀ := C
      a := A
      b := B
      positive := fun h bits ↦ negative_affine_pos (C h) (B h) (hnegative h) (hmargin h) bits
      negative := hnegative
      zero_column := by
        intro x
        simp [A, affineValue, Fin.sum_univ_add, boolToReal] }
  refine ⟨H, le_rfl, L, ?_⟩
  intro x j
  have heval : L.score (cubeStarInput x j) =
      ∑ h, a j h / (b j h + ∑ i, d h i * boolToReal (!(x i))) := by
    apply Finset.sum_congr rfl
    intro h _
    have hnum : affineValue (L.a₀ h) (L.a h) (cubeStarInput x j) = a j h := by
      simp [L, A, affineValue, cubeStarInput, Fin.sum_univ_add, boolToReal]
    have hden : affineValue (L.b₀ h) (L.b h) (cubeStarInput x j) =
        b j h + ∑ i, d h i * boolToReal (!(x i)) := by
      simp only [L, C, B, affineValue, cubeStarInput, Fin.sum_univ_add,
        Fin.addCases_left, Fin.addCases_right]
      have hj : (∑ l : Fin s, (b l h - (1 + η)) * boolToReal (decide (l = j))) =
          b j h - (1 + η) := by simp [boolToReal]
      rw [hj]
      simp only [neg_mul, Finset.sum_neg_distrib]
      rw [← complement_affine_sum]
      ring
    rw [hnum, hden]
  rw [heval]
  have ht := hsign j (fun i ↦ !(x i))
  simpa only [Bool.not_not] using ht

/-- The compact decoder's complete global budget in the original model.
For `k` comparable to `s`, a decoder of order `2^k / sqrt k` suffices for
the requested exponent one-half benchmark. -/
theorem worstCaseHeadComplexity_real_le_of_compact_cube_decoder {k s H : ℕ}
    (hs : 0 < s) (hdecoder : HasCompactPositiveCubeDecoder k H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      22 * (2 : ℝ) ^ s * H / s + 2 ^ (k + 1) :=
  worstCaseHeadComplexity_real_le_of_cube_star_compiler hs
    (hasReverseCubeStarCompiler_of_compact hdecoder)

end HeadComplexity.AxisZeroGluing
