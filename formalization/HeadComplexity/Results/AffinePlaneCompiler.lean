import HeadComplexity.Results.ReverseRankCorrection
import HeadComplexity.Results.CompactReverseCauchy
import HeadComplexity.Results.AffinePlaneIncidence
import HeadComplexity.Results.CauchyGridDecoder
import HeadComplexity.Results.AffinePlaneEncoding

set_option linter.style.header false

/-! Exact affine-plane line-sum cancellation gives a compact reverse compiler.
The line aggregates are represented by the checked rank correction. A single
reciprocal correction per point removes all other tokens from every readout. -/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The shared-line decoder itself, before assigning Boolean words to tokens.
No hypothesis on numerator magnitude or precision is used. -/
theorem exists_affinePlane_reverse_grid {r s : ℕ}
    (δ : ℝ) (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (pole token : F → ℝ)
    (hpole : ∀ a, 1 - δ < pole a ∧ pole a < 1)
    (htoken : ∀ z, 0 < token z ∧ token z < δ)
    (point : Fin r → F × F) (memory : (F × F) → Fin s → F)
    (η : Fin r → F → ℝ) (rowBias : Fin r → ℝ) :
    ∃ Q : StrictReverseGridData r s
        ((Fintype.card (F × F) + 1) + Fintype.card (F × F)),
      ∀ i j, Q.score (localGrid i j) =
        rowBias i + ∑ a : F, η i a / (pole a - token (memory (point i) j)) := by
  classical
  let N := Fintype.card (F × F)
  let e : Fin N ≃ (F × F) := (Fintype.equivFin (F × F)).symm
  let Z : (F × F) → Fin s → ℝ := fun L j ↦
    ∑ g : F × F, if g.2 = L.1 * g.1 + L.2 then
      1 / (pole L.1 - token (memory g j)) else 0
  let f : Fin N → Fin r → ℝ := fun l i ↦
    if (e l).2 = (point i).2 - (e l).1 * (point i).1 then η i (e l).1 else 0
  obtain ⟨Rank, hRank⟩ := exists_strict_reverse_rank_grid f (fun l ↦ Z (e l))
    rowBias (fun _ ↦ 0) 0
  let off : Fin r → Fin s → ℝ := fun i j ↦
    ∑ g : F × F, if g.1 ≠ (point i).1 then
      η i (affinePlaneSlope (point i) g) /
        (pole (affinePlaneSlope (point i) g) - token (memory g j)) else 0
  have hRank' (i : Fin r) (j : Fin s) :
      Rank.score (localGrid i j) =
        rowBias i + (∑ a : F, η i a / (pole a - token (memory (point i) j))) +
          off i j := by
    rw [hRank]
    simp only [zero_add, add_zero]
    have hReindex : (∑ l : Fin N, f l i * Z (e l) j) =
        ∑ L : F × F,
          (if L.2 = (point i).2 - L.1 * (point i).1 then η i L.1 else 0) *
            Z L j := by
      exact e.sum_comp (fun L : F × F ↦
        (if L.2 = (point i).2 - L.1 * (point i).1 then η i L.1 else 0) * Z L j)
    rw [hReindex, affinePlane_line_rank_identity]
    have hInc := affinePlane_weighted_pencil_identity (point i) (η i)
      (fun a g ↦ 1 / (pole a - token (memory g j)))
    dsimp [Z]
    simp only [mul_one_div] at hInc
    rw [hInc]
    simp [off, add_assoc]
  let A : (F × F) → Fin r → ℝ := fun g i ↦
    if g.1 ≠ (point i).1 then -η i (affinePlaneSlope (point i) g) else 0
  let D : (F × F) → Fin r → ℝ := fun g i ↦ pole (affinePlaneSlope (point i) g)
  choose Corr hCorr using fun l : Fin N ↦
    exists_strict_reverse_cauchy_ratio δ (A (e l)) (D (e l))
      (fun j ↦ token (memory (e l) j)) hδ hsize
      (fun i ↦ hpole _) (fun j ↦ htoken _)
  have hCorrSum (i : Fin r) (j : Fin s) :
      (∑ l : Fin N, (Corr l).value (localGrid i j)) = -off i j := by
    simp_rw [hCorr]
    have hReindex : (∑ l : Fin N, A (e l) i /
        (D (e l) i - token (memory (e l) j))) =
        ∑ g : F × F, A g i / (D g i - token (memory g j)) :=
      e.sum_comp (fun g : F × F ↦ A g i / (D g i - token (memory g j)))
    rw [hReindex]
    dsimp [off]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro g _
    dsimp [A, D]
    split_ifs <;> simp only [neg_div, zero_div, neg_zero]
  let Q : StrictReverseGridData r s ((N + 1) + N) :=
    { bias := Rank.bias
      head := Fin.addCases Rank.head Corr }
  refine ⟨Q, ?_⟩
  intro i j
  have hScore : Q.score (localGrid i j) =
      Rank.score (localGrid i j) + ∑ l : Fin N, (Corr l).value (localGrid i j) := by
    simp only [Q, StrictReverseGridData.score, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right]
    ring
  rw [hScore, hRank', hCorrSum]
  ring

/-- Every Boolean grid with at most `a * 4^a` rows has an exact strict reverse
compiler with `2 * 4^a + 1` heads, independently of the number of columns. -/
theorem hasStrictReverseGridCompiler_affinePlane (a r s : ℕ)
    (ha : 1 ≤ a) (hr : r ≤ a * 4 ^ a) :
    HasStrictReverseGridCompiler r s (2 * 4 ^ a + 1) := by
  classical
  let F := BinaryGaloisField a
  have hcard : Fintype.card F = 2 ^ a := binaryGaloisField_card ha
  intro table
  obtain ⟨row, decode, memory, hmemory⟩ := exists_affinePlane_encoding F hcard hr table
  let δ : ℝ := 1 / (4 * (((r + s : ℕ) : ℝ) + 1))
  have hn : (0 : ℝ) ≤ ((r + s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (4 * (((r + s : ℕ) : ℝ) + 1)) = 1 := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hsmall : δ < 1 / 2 := by nlinarith
  have hsize : ((r + s : ℕ) : ℝ) * δ < 1 := by nlinarith
  let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  choose c η hη using fun b : Fin a ↦
    exists_compact_cauchy_grid_decoder (q := Fintype.card F) hδ hsmall
      (fun z ↦ outputSign (decode (e.symm z) b))
  let pole : F → ℝ := fun z ↦ compactCauchyPole δ (e z)
  let token : F → ℝ := fun z ↦ compactCauchyToken δ (e z)
  have hdecode (b : Fin a) (z : F) :
      c b + (∑ u : F, η b (e u) / (pole u - token z)) =
        outputSign (decode z b) := by
    have hs := e.sum_comp (fun u ↦ η b u /
      (compactCauchyPole δ u - compactCauchyToken δ (e z)))
    dsimp [pole, token]
    rw [hs]
    simpa using hη b (e z)
  obtain ⟨Q, hQ⟩ := exists_affinePlane_reverse_grid δ hδ hsize pole token
    (fun z ↦ compactCauchyPole_bounds hδ (e z))
    (fun z ↦ ⟨compactCauchyToken_pos hδ (e z), compactCauchyToken_lt hδ (e z)⟩)
    (fun i ↦ (row i).1) memory (fun i z ↦ η (row i).2 (e z))
    (fun i ↦ c (row i).2)
  have hN : Fintype.card (F × F) = 4 ^ a := by
    rw [Fintype.card_prod, hcard, ← mul_pow]
    norm_num
  refine ⟨(Fintype.card (F × F) + 1) + Fintype.card (F × F), ?_, Q, ?_⟩
  · rw [hN]
    omega
  · intro i j
    rw [hQ, hdecode, hmemory]
    cases table i j <;> norm_num [outputSign]

end AxisZeroGluing
end HeadComplexity
