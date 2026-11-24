import HeadComplexity.Results.CubeStarPairedDecoder
import HeadComplexity.Results.JointFamilyMonomialCorrections
import HeadComplexity.Results.JointFamilyPermutationData

set_option linter.style.header false

/-!
# Column biases in paired cube decoders

A column-dependent bias costs one shared head, including exact axis repair
and positivity on multihot column inputs. This is the interface used by the
finite paired-decoder certificates; no universal decoder existence is assumed.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- The paired decoder with an unrestricted bias for each independent column. -/
def HasCompactBiasedPairedCubeDecoder (k s H : ℕ) : Prop :=
  ∀ table : (Fin k → Bool) → Fin s → Bool, ∀ η : ℝ, 0 < η →
    ∃ d r : Fin H → Fin k → ℝ, ∃ c : Fin H → ℝ,
      ∃ a b : Fin H → Fin s → ℝ, ∃ τ : Fin s → ℝ,
        (∀ h i, 0 < d h i) ∧
        (∀ h j, 1 < b h j ∧ b h j < 1 + η) ∧
        ∀ x j, 0 < outputSign (table x j) *
          ((∑ h, ((affineValue (c h) (r h) x + a h j) /
            (b h j + ∑ i, d h i * boolToReal (x i)) -
            affineValue (c h) (r h) x /
              (1 + ∑ i, d h i * boolToReal (x i)))) + τ j)

/-- Every strict residual may absorb arbitrary independent column biases at
the cost of one head. The resulting correction vanishes on the zero axis. -/
theorem reverseCubeStar_add_column_bias {k s H : ℕ}
    (L : ReverseCubeStarData k s H) (τ : Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (L.score (cubeStarInput x j) + τ j)) :
    ∃ M : ReverseCubeStarData k s (H + 1), ∀ x j,
      0 < outputSign (table x j) * M.score (cubeStarInput x j) := by
  classical
  obtain ⟨B, hB⟩ := jointFamily_row_monomial_correction_preserves_signs
    (fun _ : Fin 1 ↦ (∅ : Finset (Fin k))) (fun _ ↦ τ)
    (fun x j ↦ L.score (cubeStarInput x j)) table (by
      intro x j
      simpa [squarefreeMonomial] using hstrict x j)
  refine ⟨jointFamilyAppendData L B, fun x j ↦ ?_⟩
  rw [jointFamilyAppendData_score]
  exact hB x j

/-- Bias repair is charged once for the whole family, rather than once per
column. All labels in the decoder hypothesis remain independently chosen. -/
theorem hasReverseCubeStarCompiler_of_compact_biased_paired {k s H : ℕ}
    (hdecoder : HasCompactBiasedPairedCubeDecoder k s H) :
    HasReverseCubeStarCompiler k s (H + H + 1) := by
  classical
  intro table
  let η : ℝ := 1 / ((s : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * ((s : ℝ) + 1) = 1 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨d, r, c, a, b, τ, hd, hb, hsign⟩ :=
    hdecoder (fun x j ↦ table (fun i ↦ !(x i)) j) η hη
  obtain ⟨L, hL⟩ := exists_reverse_cube_star_paired_score η hη (by nlinarith)
    d r c a b hd hb
  obtain ⟨M, hM⟩ := reverseCubeStar_add_column_bias L τ table (by
    intro x j
    rw [hL]
    simpa only [Bool.not_not] using hsign (fun i ↦ !(x i)) j)
  exact ⟨H + H + 1, le_rfl, M, hM⟩

/-- Conditional global count, including the exceptional face and the charged
single bias-repair head. -/
theorem worstCaseHeadComplexity_real_le_of_compact_biased_paired_cube_decoder
    {k s H : ℕ} (hs : 0 < s)
    (hdecoder : HasCompactBiasedPairedCubeDecoder k s H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      22 * (2 : ℝ) ^ s * (H + H + 1) / s + 2 ^ (k + 1) := by
  have ht := worstCaseHeadComplexity_real_le_of_cube_star_compiler hs
    (hasReverseCubeStarCompiler_of_compact_biased_paired hdecoder)
  simpa only [Nat.cast_add, Nat.cast_one] using ht

end HeadComplexity.AxisZeroGluing
