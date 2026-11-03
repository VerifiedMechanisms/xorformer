import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

import HeadComplexity.Results.OpenNeighborhoodCover

set_option linter.style.header false

/-! # Additive syndrome covers of Boolean cube neighborhoods -/

namespace HeadComplexity

open Finset
open scoped BigOperators

abbrev BinaryVector (n : ℕ) := Fin n → ZMod 2

/-- Boolean and binary-field coordinates have the same finite encoding. -/
def binaryBitEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by decide
  right_inv := by decide

def binaryCubeEquiv (n : ℕ) : (Fin n → Bool) ≃ BinaryVector n :=
  Equiv.piCongrRight fun _ ↦ binaryBitEquiv

theorem binaryCubeEquiv_flip {n : ℕ} (bits : Fin n → Bool) (i : Fin n) :
    binaryCubeEquiv n (cubeFlip bits i) = binaryCubeEquiv n bits + Pi.single i 1 := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    cases hb : bits i
    all_goals norm_num [binaryCubeEquiv, binaryBitEquiv, cubeFlip, hb]
    decide
  · simp [binaryCubeEquiv, cubeFlip, hji]

/-- A union of syndrome fibers covering every syndrome by one column step. -/
structure SyndromeCover (n : ℕ) (S : Type*) [AddCommGroup S] [Fintype S] where
  syndrome : BinaryVector n →+ S
  surjective : Function.Surjective syndrome
  targets : Finset S
  covers : ∀ s, ∃ t ∈ targets, ∃ i : Fin n, s = t + syndrome (Pi.single i 1)

namespace SyndromeCover

variable {n : ℕ} {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S]

/-- Repeating coordinates preserves a syndrome cover and its target count. -/
def extend (C : SyndromeCover n S) (k : ℕ) : SyndromeCover (n + k) S where
  syndrome := C.syndrome.comp {
    toFun := fun x i ↦ x (Fin.castAdd k i)
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl }
  surjective := by
    intro s
    obtain ⟨x, hx⟩ := C.surjective s
    exact ⟨Fin.addCases x 0, by simpa using hx⟩
  targets := C.targets
  covers := by
    intro s
    obtain ⟨t, ht, i, hs⟩ := C.covers s
    refine ⟨t, ht, Fin.castAdd k i, ?_⟩
    have heq : (fun j : Fin n ↦ (Pi.single (Fin.castAdd k i) 1 : BinaryVector (n + k))
        (Fin.castAdd k j)) = Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    change s = t + C.syndrome (fun j ↦
      (Pi.single (Fin.castAdd k i) 1 : BinaryVector (n + k)) (Fin.castAdd k j))
    rw [heq]
    exact hs

noncomputable def centers (C : SyndromeCover n S) : Finset (BinaryVector n) :=
  Finset.univ.filter fun x ↦ C.syndrome x ∈ C.targets

theorem centers_card_mul (C : SyndromeCover n S) :
    C.centers.card * Fintype.card S = C.targets.card * 2 ^ n := by
  classical
  let K := ((Finset.univ : Finset (BinaryVector n)).filter fun x ↦ C.syndrome x = 0).card
  have hfiber (s : S) :
      ((Finset.univ : Finset (BinaryVector n)).filter fun x ↦ C.syndrome x = s).card = K :=
    AddMonoidHom.card_fiber_eq_of_mem_range C.syndrome (C.surjective s) (C.surjective 0)
  have hc : C.centers.card = C.targets.card * K := by
    rw [centers, ← Finset.sum_card_fiberwise_eq_card_filter Finset.univ C.targets C.syndrome]
    simp_rw [hfiber]
    simp
  have hall : 2 ^ n = Fintype.card S * K := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (BinaryVector n)) Finset.univ C.syndrome
    simp_rw [hfiber] at h
    simpa [BinaryVector, ZMod.card] using h.symm
  rw [hc, hall]
  ring

theorem nonempty_openNeighborhoodCover (C : SyndromeCover n S) :
    Nonempty (OpenNeighborhoodCover n C.centers.card) := by
  classical
  let e := C.centers.equivFin
  refine ⟨{
    center := fun h ↦ (binaryCubeEquiv n).symm (e.symm h).val
    covers := ?_ }⟩
  intro bits
  let v := binaryCubeEquiv n bits
  obtain ⟨t, ht, i, hs⟩ := C.covers (C.syndrome v)
  let c := v - Pi.single i 1
  have hc : c ∈ C.centers := by
    simp only [centers, Finset.mem_filter, Finset.mem_univ, true_and]
    have heq : C.syndrome c = t := by
      dsimp [c]
      rw [map_sub, hs]
      abel
    rwa [heq]
  refine ⟨e ⟨c, hc⟩, i, ?_⟩
  apply (binaryCubeEquiv n).injective
  rw [binaryCubeEquiv_flip]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  change v = c + Pi.single i 1
  simp [c]

noncomputable def toOpenNeighborhoodCover (C : SyndromeCover n S) :
    OpenNeighborhoodCover n C.centers.card := Classical.choice C.nonempty_openNeighborhoodCover

omit [DecidableEq S] in
theorem HStar_mul_le (C : SyndromeCover n S) (f : (Fin n → Bool) → Bool) :
    HStar n f * Fintype.card S ≤ C.targets.card * 2 ^ n := by
  classical
  rw [← C.centers_card_mul]
  exact Nat.mul_le_mul_right _ (C.toOpenNeighborhoodCover.HStar_le f)

end SyndromeCover

end HeadComplexity
