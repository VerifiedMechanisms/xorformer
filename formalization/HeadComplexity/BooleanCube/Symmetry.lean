import HeadComplexity.BooleanCube.CoordinateFace

set_option linter.style.header false

/-!
# Boolean-cube symmetries

Coordinate permutations and the simultaneous complement of every coordinate
act on Boolean-cube functions.  These elementary maps are kept separate from
the atom transformations that realize the corresponding model invariances.
-/

namespace HeadComplexity

variable {n : ℕ}

/-- Precompose a cube point with a coordinate permutation. -/
def permuteBits (sigma : Equiv.Perm (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i ↦ x (sigma i)

@[simp] theorem permuteBits_apply (sigma : Equiv.Perm (Fin n))
    (x : Fin n → Bool) (i : Fin n) :
    permuteBits sigma x i = x (sigma i) := rfl

@[simp] theorem permuteBits_refl (x : Fin n → Bool) :
    permuteBits (Equiv.refl (Fin n)) x = x := rfl

@[simp] theorem permuteBits_trans (sigma tau : Equiv.Perm (Fin n))
    (x : Fin n → Bool) :
    permuteBits (sigma.trans tau) x = permuteBits sigma (permuteBits tau x) := rfl

@[simp] theorem permuteBits_symm (sigma : Equiv.Perm (Fin n))
    (x : Fin n → Bool) :
    permuteBits sigma.symm (permuteBits sigma x) = x := by
  funext i
  simp [permuteBits]

/-- Simultaneously complement every Boolean coordinate. -/
def flipBits (x : Fin n → Bool) : Fin n → Bool := fun i ↦ !(x i)

@[simp] theorem flipBits_apply (x : Fin n → Bool) (i : Fin n) :
    flipBits x i = !(x i) := rfl

@[simp] theorem flipBits_involutive (x : Fin n → Bool) :
    flipBits (flipBits x) = x := by
  funext i
  simp [flipBits]

end HeadComplexity
