import HeadComplexity.Polynomial.ParityThresholdDegree
import Mathlib.Combinatorics.Colex

set_option linter.style.header false

/-!
# Exact four-bit encodings

The executable certificate uses the conventional little-endian enumeration
of the four-cube and of truth tables.  This module proves that enumeration is
faithful and that every Boolean function is either a representative with a
zero top truth-table bit, or the output complement of such a representative.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- The little-endian four-bit vector encoded by an integer below sixteen. -/
def fourBitCube (x : Fin 16) (i : Fin 4) : Bool :=
  x.val.testBit i.val

/-- The conventional binary enumeration is a bijection onto the four-cube. -/
noncomputable def fourBitCubeEquiv : Fin 16 ≃ (Fin 4 → Bool) :=
  Equiv.ofBijective fourBitCube (by decide)

@[simp] theorem fourBitCubeEquiv_apply (x : Fin 16) :
    fourBitCubeEquiv x = fourBitCube x := rfl

@[simp] theorem fourBitCube_symm (bits : Fin 4 → Bool) :
    fourBitCube (fourBitCubeEquiv.symm bits) = bits := by
  rw [← fourBitCubeEquiv_apply, fourBitCubeEquiv.apply_symm_apply]

@[simp] theorem fourBitCubeEquiv_symm_cube (x : Fin 16) :
    fourBitCubeEquiv.symm (fourBitCube x) = x := by
  rw [← fourBitCubeEquiv_apply, fourBitCubeEquiv.symm_apply_apply]

/-- The Boolean function encoded by a complement-pair representative mask. -/
noncomputable def fourBitRepresentativeFunction (mask : Fin 32768)
    (bits : Fin 4 → Bool) : Bool :=
  mask.val.testBit (fourBitCubeEquiv.symm bits).val

@[simp] theorem fourBitRepresentativeFunction_cube
    (mask : Fin 32768) (x : Fin 16) :
    fourBitRepresentativeFunction mask (fourBitCube x) =
      mask.val.testBit x.val := by
  simp [fourBitRepresentativeFunction, fourBitCubeEquiv]

/-- The representative of four-bit parity in the archived convention. -/
def fourBitParityMask : Fin 32768 := ⟨27030, by decide⟩

/-- The vertex controlling the representative of a complement pair. -/
def fourBitLast : Fin 16 := ⟨15, by decide⟩

theorem fourBitRepresentativeFunction_parity :
    fourBitRepresentativeFunction fourBitParityMask = PARITY 4 := by
  funext bits
  rw [← fourBitCubeEquiv.apply_symm_apply bits]
  change fourBitRepresentativeFunction fourBitParityMask
      (fourBitCube (fourBitCubeEquiv.symm bits)) =
    PARITY 4 (fourBitCube (fourBitCubeEquiv.symm bits))
  rw [fourBitRepresentativeFunction_cube]
  generalize fourBitCubeEquiv.symm bits = x
  revert x
  decide

/-- Normalize a truth table so that its bit at vertex fifteen is false. -/
def normalizeFourBitFunction (f : (Fin 4 → Bool) → Bool) :
    (Fin 4 → Bool) → Bool :=
  if f (fourBitCube fourBitLast) = true then fun bits ↦ !(f bits) else f

@[simp] theorem normalizeFourBitFunction_last
    (f : (Fin 4 → Bool) → Bool) :
    normalizeFourBitFunction f (fourBitCube fourBitLast) = false := by
  cases h : f (fourBitCube fourBitLast) <;>
    simp [normalizeFourBitFunction, h]

/-- The set of true vertex indices of the normalized truth table. -/
def normalizedTruthIndices (f : (Fin 4 → Bool) → Bool) : Finset ℕ :=
  ((Finset.univ : Finset (Fin 16)).filter fun x ↦
      normalizeFourBitFunction f (fourBitCube x) = true).image Fin.val

theorem mem_normalizedTruthIndices
    (f : (Fin 4 → Bool) → Bool) (x : Fin 16) :
    x.val ∈ normalizedTruthIndices f ↔
      normalizeFourBitFunction f (fourBitCube x) = true := by
  simp [normalizedTruthIndices, Fin.val_injective.eq_iff]

/-- Natural-number truth-table mask of the normalized function. -/
def normalizedTruthMaskNat (f : (Fin 4 → Bool) → Bool) : ℕ :=
  ∑ i ∈ normalizedTruthIndices f, 2 ^ i

theorem normalizedTruthMaskNat_lt
    (f : (Fin 4 → Bool) → Bool) :
    normalizedTruthMaskNat f < 32768 := by
  change (∑ i ∈ normalizedTruthIndices f, 2 ^ i) < 2 ^ 15
  apply Nat.geomSum_lt (by decide)
  intro i hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp
    (show i ∈ ((Finset.univ : Finset (Fin 16)).filter fun x ↦
      normalizeFourBitFunction f (fourBitCube x) = true).image Fin.val from hi)
  have htrue := (Finset.mem_filter.mp hx).2
  have hne : x.val ≠ 15 := by
    intro heq
    have hxlast : x = fourBitLast := Fin.ext heq
    subst x
    rw [normalizeFourBitFunction_last] at htrue
    exact Bool.false_ne_true htrue
  omega

/-- The normalized truth-table mask as a complement-pair representative. -/
def normalizedTruthMask (f : (Fin 4 → Bool) → Bool) : Fin 32768 :=
  ⟨normalizedTruthMaskNat f, normalizedTruthMaskNat_lt f⟩

private theorem normalizedTruthMask_bit
    (f : (Fin 4 → Bool) → Bool) (x : Fin 16) :
    (normalizedTruthMask f).val.testBit x.val =
      normalizeFourBitFunction f (fourBitCube x) := by
  apply Bool.eq_iff_iff.mpr
  rw [← Nat.mem_bitIndices]
  change x.val ∈ (normalizedTruthMaskNat f).bitIndices ↔ _
  rw [← List.mem_toFinset]
  rw [normalizedTruthMaskNat, Finset.toFinset_bitIndices_sum_two_pow]
  exact mem_normalizedTruthIndices f x

theorem representative_normalizedTruthMask
    (f : (Fin 4 → Bool) → Bool) :
    fourBitRepresentativeFunction (normalizedTruthMask f) =
      normalizeFourBitFunction f := by
  funext bits
  rw [← fourBitCubeEquiv.apply_symm_apply bits]
  change fourBitRepresentativeFunction (normalizedTruthMask f)
      (fourBitCube (fourBitCubeEquiv.symm bits)) =
    normalizeFourBitFunction f (fourBitCube (fourBitCubeEquiv.symm bits))
  rw [fourBitRepresentativeFunction_cube, normalizedTruthMask_bit]

/-- Every four-bit Boolean function is represented by one of the 32768 masks,
up to output complementation. -/
theorem exists_representative_or_complement
    (f : (Fin 4 → Bool) → Bool) :
    ∃ mask : Fin 32768,
      f = fourBitRepresentativeFunction mask ∨
        f = fun bits ↦ !(fourBitRepresentativeFunction mask bits) := by
  refine ⟨normalizedTruthMask f, ?_⟩
  by_cases hlast : f (fourBitCube fourBitLast) = true
  · right
    have hnorm : normalizeFourBitFunction f = fun bits ↦ !(f bits) := by
      simp [normalizeFourBitFunction, hlast]
    rw [representative_normalizedTruthMask, hnorm]
    funext bits
    cases hbits : f bits <;> simp [hbits]
  · left
    have hfalse : f (fourBitCube fourBitLast) = false := by
      cases h : f (fourBitCube fourBitLast)
      · rfl
      · exact (hlast h).elim
    rw [representative_normalizedTruthMask]
    simp [normalizeFourBitFunction, hfalse]

end HeadComplexity
