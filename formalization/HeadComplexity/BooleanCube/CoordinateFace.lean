import HeadComplexity.Model.Head

set_option linter.style.header false

/-!
# Coordinate faces of the Boolean cube

A `CoordFace m n` embeds an `m`-dimensional Boolean cube as a coordinate face
of the `n`-dimensional cube. The injection `free` selects the varying
coordinates and `base` supplies the values of every fixed coordinate.

The sum decomposition at the end of the file is the basic bookkeeping lemma
used to restrict linear-fractional atoms to a face.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- An embedding of the `m`-cube as a coordinate face of the `n`-cube. -/
structure CoordFace (m n : ℕ) where
  /-- The coordinates that remain free on the face. -/
  free : Fin m ↪ Fin n
  /-- Values assigned to coordinates outside the image of `free`. -/
  base : Fin n → Bool

namespace CoordFace

variable {m n : ℕ}

/-- Insert the free bits into their selected coordinates and use `base`
everywhere else. -/
noncomputable def apply (rho : CoordFace m n) (x : Fin m → Bool) : Fin n → Bool :=
  fun j => if h : ∃ i, rho.free i = j then x (Classical.choose h) else rho.base j

@[simp] theorem apply_free (rho : CoordFace m n) (x : Fin m → Bool) (i : Fin m) :
    rho.apply x (rho.free i) = x i := by
  rw [apply, dif_pos ⟨i, rfl⟩]
  congr 1
  exact rho.free.injective
    (Classical.choose_spec (show ∃ k, rho.free k = rho.free i from ⟨i, rfl⟩))

/-- The image of the free-coordinate injection. -/
noncomputable def freeSet (rho : CoordFace m n) : Finset (Fin n) :=
  Finset.univ.image rho.free

/-- The coordinates fixed by the face. -/
noncomputable def fixedSet (rho : CoordFace m n) : Finset (Fin n) :=
  Finset.univ \ rho.freeSet

@[simp] theorem mem_freeSet (rho : CoordFace m n) (j : Fin n) :
    j ∈ rho.freeSet ↔ ∃ i, rho.free i = j := by
  classical
  simp [freeSet]

@[simp] theorem apply_fixed (rho : CoordFace m n) (x : Fin m → Bool) {j : Fin n}
    (hj : j ∈ rho.fixedSet) : rho.apply x j = rho.base j := by
  rw [apply, dif_neg]
  intro h
  have : j ∈ rho.freeSet := (rho.mem_freeSet j).2 h
  exact (Finset.mem_sdiff.mp hj).2 this

/-- Split a sum over all ambient coordinates into its free and fixed parts. -/
@[simp] theorem sum_eq_free_add_fixed {A : Type*} [AddCommMonoid A]
    (rho : CoordFace m n) (u : Fin n → A) :
    (∑ j, u j) = (∑ i, u (rho.free i)) + ∑ j ∈ rho.fixedSet, u j := by
  classical
  calc
    (∑ j, u j) = ∑ j ∈ rho.freeSet ∪ rho.fixedSet, u j := by
      rw [fixedSet, Finset.union_sdiff_of_subset (Finset.subset_univ rho.freeSet)]
    _ = (∑ j ∈ rho.freeSet, u j) + ∑ j ∈ rho.fixedSet, u j := by
      rw [Finset.sum_union]
      exact Finset.disjoint_sdiff
    _ = (∑ i, u (rho.free i)) + ∑ j ∈ rho.fixedSet, u j := by
      rw [freeSet, Finset.sum_image rho.free.injective.injOn]

end CoordFace

end HeadComplexity
