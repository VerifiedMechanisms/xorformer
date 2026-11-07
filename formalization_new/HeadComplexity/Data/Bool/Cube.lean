module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Function.Basic

/-!
# The Boolean cube

The coordinate embedding into a semiring, Hamming weight, and two-coordinate faces.
-/

@[expose] public section

open scoped BigOperators

namespace Bool

variable {ι R : Type*}

/-- The vertex with coordinates zero or one specified by a Boolean assignment. -/
def cubePoint (R : Type*) [AddMonoidWithOne R] (x : ι → Bool) (i : ι) : R :=
  (x i).toNat

/-- A coordinate of a Boolean vertex is the cast of its bit, either zero or one. -/
@[simp] theorem cubePoint_apply [AddMonoidWithOne R] (x : ι → Bool) (i : ι) :
    cubePoint R x i = (x i).toNat :=
  rfl

/-- The signed encoding of a bit, with false mapped to one. -/
def spin (R : Type*) [Ring R] (b : Bool) : R :=
  if b then -1 else 1

/-- The signed encoding sends false to positive one. -/
@[simp] theorem spin_false [Ring R] : spin R false = 1 := rfl

/-- The signed encoding sends true to negative one. -/
@[simp] theorem spin_true [Ring R] : spin R true = -1 := rfl

/-- Flipping a bit negates its signed encoding. -/
@[simp] theorem spin_not [Ring R] (b : Bool) : spin R (!b) = -spin R b := by
  cases b <;> simp

/-- The signed encoding is one minus twice the zero-or-one encoding. -/
theorem spin_eq_one_sub [Ring R] (b : Bool) : spin R b = 1 - 2 * (b.toNat : R) := by
  cases b
  · simp
  · simp only [spin_true, toNat_true, Nat.cast_one, mul_one]
    rw [← one_add_one_eq_two, sub_add_eq_sub_sub, sub_self, zero_sub]

/-- The number of true coordinates of a Boolean assignment. -/
def hammingWeight [Fintype ι] (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ x i = true).card

/-- The number of true coordinates is at most the number of available coordinates. -/
theorem hammingWeight_le_card [Fintype ι] (x : ι → Bool) :
    hammingWeight x ≤ Fintype.card ι := by
  simpa [hammingWeight] using
    (Finset.card_filter_le Finset.univ fun i ↦ x i = true)

/-- Summing the coordinates of the embedded vertex gives its Hamming weight. -/
theorem sum_cubePoint [Fintype ι] [AddCommMonoidWithOne R] (x : ι → Bool) :
    ∑ i, cubePoint R x i = (hammingWeight x : R) := by
  rw [hammingWeight, Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun i _ ↦ by cases h : x i <;> simp [h]

/-- The face through a fixed assignment obtained by replacing two coordinates. -/
def face [DecidableEq ι] (x : ι → Bool) (i j : ι) (a b : Bool) : ι → Bool :=
  Function.update (Function.update x i a) j b

/-- At the first updated coordinate, a face takes the first supplied bit when the coordinates
differ. -/
@[simp] theorem face_apply_left [DecidableEq ι] (x : ι → Bool) {i j : ι}
    (hij : i ≠ j) (a b : Bool) : face x i j a b i = a := by
  simp [face, Function.update_of_ne hij]

/-- At the second updated coordinate, a face takes the second supplied bit. -/
@[simp] theorem face_apply_right [DecidableEq ι] (x : ι → Bool) (i j : ι) (a b : Bool) :
    face x i j a b j = b := by
  simp [face]

/-- A coordinate outside the two updated positions retains its value from the base assignment. -/
theorem face_apply_of_ne [DecidableEq ι] (x : ι → Bool) {i j k : ι}
    (hki : k ≠ i) (hkj : k ≠ j) (a b : Bool) : face x i j a b k = x k := by
  simp [face, Function.update_of_ne hki, Function.update_of_ne hkj]

end Bool

namespace Finset

variable {ι β M : Type*} [DecidableEq ι] [AddCommMonoid M]

/-- Updating a coordinate in a finite sum replaces its summand and leaves the sum over the
remaining coordinates alone. -/
theorem sum_apply_update_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s)
    (g : ι → β → M) (x : ι → β) (a : β) :
    (∑ j ∈ s, g j (Function.update x i a j)) =
      g i a + ∑ j ∈ s.erase i, g j (x j) := by
  rw [← add_sum_erase s (fun j ↦ g j (Function.update x i a j)) hi, Function.update_self]
  congr 1
  exact sum_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_erase hj)]

end Finset
