import HeadComplexity.Results.UniversalLinearSaving

set_option linter.style.header false

/-!
# Open downward star covers for reverse gluing

The existing upward star cover transfers by complementation, then by adding
one parent for each proper center. The budget doubles in each block. The
product cover omits exactly the two faces where one block is all ones.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Finset
open scoped BigOperators

/-- Every proper vertex is a child of one selected center. -/
def OpenDownwardCovers {α : Type*} [Fintype α] [DecidableEq α]
    (D : Finset (Finset α)) : Prop :=
  ∀ X : Finset α, X ≠ Finset.univ → ∃ S ∈ D, ∃ i ∈ S, S.erase i = X

/-- Complementing a closed upward cover and adjoining one parent per proper
center gives an open downward cover at a factor of at most two in size. -/
theorem openDownwardCover_of_upward {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (Finset α)) (hC : StarCoverRecursion.Covers C) :
    ∃ D : Finset (Finset α), OpenDownwardCovers D ∧ D.card ≤ 2 * C.card := by
  classical
  have hout (S : Finset α) (hS : S ≠ Finset.univ) : ∃ i, i ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  let parent : Finset α → Finset α := fun S ↦
    if hS : S = Finset.univ then S else insert (Classical.choose (hout S hS)) S
  let E : Finset (Finset α) := C.image (fun S ↦ Sᶜ)
  let D := E ∪ E.image parent
  refine ⟨D, ?_, ?_⟩
  · intro X hX
    obtain ⟨S, hSC, hstar⟩ := hC Xᶜ
    rcases hstar with hSX | ⟨i, hiS, hiX⟩
    · have hSX' : Sᶜ = X := by rw [hSX]; simp
      have hXE : X ∈ E := Finset.mem_image.mpr ⟨S, hSC, hSX'⟩
      let i := Classical.choose (hout X hX)
      have hi : i ∉ X := Classical.choose_spec (hout X hX)
      refine ⟨parent X, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨X, hXE, rfl⟩),
        i, ?_, ?_⟩
      · simp [parent, hX, i]
      · simp [parent, hX, i, Finset.erase_insert hi]
    · refine ⟨Sᶜ, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S, hSC, rfl⟩),
        i, Finset.mem_compl.mpr hiS, ?_⟩
      have h := congrArg (fun T : Finset α ↦ Tᶜ) hiX
      simpa using h
  · calc
      D.card ≤ E.card + (E.image parent).card := Finset.card_union_le _ _
      _ ≤ E.card + E.card := Nat.add_le_add_left Finset.card_image_le _
      _ ≤ C.card + C.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * C.card := by omega

/-- The audited cover transfer uses the existing checked constant eleven. -/
theorem exists_openDownwardCover (n : ℕ) (hn : 0 < n) :
    ∃ D : Finset (Finset (Fin n)), OpenDownwardCovers D ∧
      (D.card : ℝ) ≤ 22 * (2 : ℝ) ^ n / n := by
  obtain ⟨C, hcard, hC⟩ := monomialStarCoverNumber_spec n
  obtain ⟨D, hD, hDcard⟩ := openDownwardCover_of_upward C hC
  refine ⟨D, hD, ?_⟩
  have hnat : (D.card : ℝ) ≤ 2 * (monomialStarCoverNumber n : ℝ) := by
    rw [hcard] at hDcard
    exact_mod_cast hDcard
  have hbound := monomialStarCoverNumber_real_le_eleven n hn
  calc
    (D.card : ℝ) ≤ 2 * (monomialStarCoverNumber n : ℝ) := hnat
    _ ≤ 2 * (11 * (2 : ℝ) ^ n / n) := by gcongr
    _ = 22 * (2 : ℝ) ^ n / n := by ring

/-- A product of open downward covers covers every pair of proper vertices. -/
theorem product_openDownwardCover {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (D : Finset (Finset α)) (E : Finset (Finset β))
    (hD : OpenDownwardCovers D) (hE : OpenDownwardCovers E)
    (X : Finset α) (Y : Finset β) (hX : X ≠ Finset.univ) (hY : Y ≠ Finset.univ) :
    ∃ ST ∈ D ×ˢ E, (∃ i ∈ ST.1, ST.1.erase i = X) ∧
      (∃ j ∈ ST.2, ST.2.erase j = Y) := by
  obtain ⟨S, hS, i, hi, hSi⟩ := hD X hX
  obtain ⟨T, hT, j, hj, hTj⟩ := hE Y hY
  exact ⟨(S, T), Finset.mem_product.mpr ⟨hS, hT⟩, ⟨i, hi, hSi⟩, ⟨j, hj, hTj⟩⟩

/-- Exact finite product budget before balancing: at most
`484 * 2^(a+b) / (a*b)` modules. Empty cells may be discarded. -/
theorem exists_product_openDownwardCover (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ (D : Finset (Finset (Fin a))) (E : Finset (Finset (Fin b))),
      OpenDownwardCovers D ∧ OpenDownwardCovers E ∧
      ((D ×ˢ E).card : ℝ) ≤ 484 * (2 : ℝ) ^ (a + b) / ((a : ℝ) * b) := by
  obtain ⟨D, hD, hDcard⟩ := exists_openDownwardCover a ha
  obtain ⟨E, hE, hEcard⟩ := exists_openDownwardCover b hb
  refine ⟨D, E, hD, hE, ?_⟩
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  calc
    ((D ×ˢ E).card : ℝ) = (D.card : ℝ) * E.card := by simp
    _ ≤ (22 * (2 : ℝ) ^ a / a) * (22 * (2 : ℝ) ^ b / b) := by gcongr
    _ = 484 * (2 : ℝ) ^ (a + b) / ((a : ℝ) * b) := by
      rw [pow_add]
      field_simp
      ring

end AxisZeroGluing
end HeadComplexity
