import HeadComplexity.Results.SyndromeLift

set_option linter.style.header false

/-! # Small exact additive covers and the single-kernel construction -/

namespace HeadComplexity

open Finset
open scoped BigOperators
open SyndromeRecipe

def syndromeColumns12 : Fin 12 → BinaryVector 6 :=
  fun i ↦ wordVector 6 (![17, 18, 20, 23, 26, 31, 34, 39, 56, 58, 61, 63] i)

def syndromeBasisPreimage12 : Fin 6 → BinaryVector 12 :=
  fun j ↦ wordVector 12 (![595, 592, 598, 18, 594, 528] j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
theorem syndromeBasisChecked12 : ∀ j : Fin 6,
    syndromeLinear syndromeColumns12 (syndromeBasisPreimage12 j) = Pi.single j 1 := by
  decide +kernel

def syndromeTargets12 : Finset (BinaryVector 6) :=
  {wordVector 6 0, wordVector 6 6, wordVector 6 10, wordVector 6 20, wordVector 6 22,
    wordVector 6 48, wordVector 6 49}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
theorem syndromeCoverChecked12 : ∀ v : BinaryVector 6,
    ∃ t ∈ syndromeTargets12, ∃ i : Fin 12, v = t + syndromeColumns12 i := by
  decide +kernel

def syndromeRecipe12 : SyndromeRecipe 12 6 where
  column := syndromeColumns12
  surjective := syndromeLinear_surjective _ syndromeBasisPreimage12 syndromeBasisChecked12
  targets := syndromeTargets12
  covers := syndromeCoverChecked12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
@[simp] theorem syndromeTargets12_card : syndromeRecipe12.targets.card = 7 := by
  decide +kernel

def syndromeColumns13 : Fin 13 → BinaryVector 7 :=
  fun i ↦ wordVector 7 (![0, 3, 4, 14, 20, 52, 66, 89, 95, 96, 110, 115, 126] i)

def syndromeBasisPreimage13 : Fin 7 → BinaryVector 13 :=
  fun j ↦ wordVector 13 (![216, 218, 4, 214, 20, 48, 154] j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
theorem syndromeBasisChecked13 : ∀ j : Fin 7,
    syndromeLinear syndromeColumns13 (syndromeBasisPreimage13 j) = Pi.single j 1 := by
  decide +kernel

def syndromeTargets13 : Finset (BinaryVector 7) :=
  {wordVector 7 0, wordVector 7 1, wordVector 7 13, wordVector 7 40, wordVector 7 69,
    wordVector 7 78, wordVector 7 83, wordVector 7 97, wordVector 7 104,
    wordVector 7 112, wordVector 7 120, wordVector 7 125}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
theorem syndromeCoverChecked13 : ∀ v : BinaryVector 7,
    ∃ t ∈ syndromeTargets13, ∃ i : Fin 13, v = t + syndromeColumns13 i := by
  decide +kernel

def syndromeRecipe13 : SyndromeRecipe 13 7 where
  column := syndromeColumns13
  surjective := syndromeLinear_surjective _ syndromeBasisPreimage13 syndromeBasisChecked13
  targets := syndromeTargets13
  covers := syndromeCoverChecked13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
@[simp] theorem syndromeTargets13_card : syndromeRecipe13.targets.card = 12 := by
  decide +kernel

/-- Listing all syndromes, including zero, gives an open-neighborhood cover. -/
def singleKernelRecipe (r : ℕ) : SyndromeRecipe (2 ^ r) r where
  column := wordVector r
  surjective := by
    intro v
    refine ⟨Pi.single (cubeIndex ((binaryCubeEquiv r).symm v)) 1, ?_⟩
    simp
  targets := {0}
  covers := by
    intro v
    refine ⟨0, by simp, cubeIndex ((binaryCubeEquiv r).symm v), ?_⟩
    simp

end HeadComplexity
