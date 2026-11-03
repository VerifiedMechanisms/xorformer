import Mathlib.Combinatorics.Colex

set_option linter.style.header false

/-! # Little-endian cube encoding in arbitrary dimension -/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- Positions of the true bits, interpreted as natural numbers. -/
def trueBitIndices {n : ℕ} (bits : Fin n → Bool) : Finset ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i ↦ bits i = true).image Fin.val

@[simp] theorem mem_trueBitIndices {n : ℕ} (bits : Fin n → Bool) (i : Fin n) :
    i.val ∈ trueBitIndices bits ↔ bits i = true := by
  simp [trueBitIndices, Fin.val_injective.eq_iff]

/-- A cube input as its ordinary binary integer. -/
def cubeIndex {n : ℕ} (bits : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨∑ i ∈ trueBitIndices bits, 2 ^ i, Nat.geomSum_lt (by decide) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.isLt)⟩

/-- The binary digits of a finite cube index. -/
def cubeBits {n : ℕ} (word : Fin (2 ^ n)) (i : Fin n) : Bool :=
  word.val.testBit i.val

@[simp] theorem cubeBits_cubeIndex {n : ℕ} (bits : Fin n → Bool) :
    cubeBits (cubeIndex bits) = bits := by
  funext i
  apply Bool.eq_iff_iff.mpr
  rw [cubeBits, ← Nat.mem_bitIndices, ← List.mem_toFinset]
  change i.val ∈ (∑ j ∈ trueBitIndices bits, 2 ^ j).bitIndices.toFinset ↔ _
  rw [Finset.toFinset_bitIndices_sum_two_pow, mem_trueBitIndices]

theorem cubeIndex_injective (n : ℕ) :
    Function.Injective (cubeIndex : (Fin n → Bool) → Fin (2 ^ n)) :=
  Function.LeftInverse.injective cubeBits_cubeIndex

@[simp] theorem cubeIndex_cubeBits {n : ℕ} (word : Fin (2 ^ n)) :
    cubeIndex (cubeBits word) = word := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact congrFun (cubeBits_cubeIndex (cubeBits word)) ⟨i, hi⟩
  · have hni : n ≤ i := by omega
    rw [Nat.testBit_lt_two_pow ((cubeIndex (cubeBits word)).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) hni)),
      Nat.testBit_lt_two_pow (word.isLt.trans_le (Nat.pow_le_pow_right (by decide) hni))]

theorem cubeBits_surjective (n : ℕ) :
    Function.Surjective (cubeBits : Fin (2 ^ n) → (Fin n → Bool)) :=
  fun bits ↦ ⟨cubeIndex bits, cubeBits_cubeIndex bits⟩

end HeadComplexity
