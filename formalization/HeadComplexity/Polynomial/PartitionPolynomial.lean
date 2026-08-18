import HeadComplexity.BooleanCube.Partition
import HeadComplexity.Polynomial.TangentRank
import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Polynomial evaluation across a coordinate partition

Affine polynomials split as a left function plus a right function across any
coordinate partition.  Applying this split to every numerator and denominator
in a cleared affine-fraction family identifies its partition evaluation matrix
with the abstract tangent matrix from `TangentRank`.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ} {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Evaluation matrix of a polynomial across a coordinate partition. -/
noncomputable def polynomialPartitionMatrix (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) : Matrix (ι → Bool) (κ → Bool) ℝ :=
  fun u v ↦ eval (cubePoint (mergePartitionBits part u v)) P

/-- Constant and left-coordinate part of an affine polynomial. -/
noncomputable def affineLeftPart (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) (u : ι → Bool) : ℝ :=
  P.coeff 0 + ∑ i,
    P.coeff (Finsupp.single (part.symm (Sum.inl i)) 1) * boolToReal (u i)

/-- Right-coordinate part of an affine polynomial, with no duplicated
constant term. -/
noncomputable def affineRightPart (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) (v : κ → Bool) : ℝ :=
  ∑ j, P.coeff (Finsupp.single (part.symm (Sum.inr j)) 1) * boolToReal (v j)

omit [DecidableEq κ] in
/-- Every degree-at-most-one polynomial evaluates as its left part plus its
right part across an arbitrary coordinate partition. -/
theorem eval_mergePartitionBits_eq_affineParts (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1)
    (u : ι → Bool) (v : κ → Bool) :
    eval (cubePoint (mergePartitionBits part u v)) P =
      affineLeftPart part P u + affineRightPart part P v := by
  rw [eval_cubePoint_affine P hP]
  unfold affineLeftPart affineRightPart
  rw [← (part.symm.sum_comp fun i : Fin n ↦
    P.coeff (Finsupp.single i 1) *
      boolToReal (mergePartitionBits part u v i))]
  rw [Fintype.sum_sum_type]
  simp only [mergePartitionBits_left, mergePartitionBits_right]
  ring

/-- Evaluation matrix of the cleared polynomial of an abstract affine
fraction family. -/
noncomputable def clearedAffinePartitionMatrix (part : Fin n ≃ ι ⊕ κ)
    (A : AffineFractionFamily n H) (c : ℝ) :
    Matrix (ι → Bool) (κ → Bool) ℝ :=
  polynomialPartitionMatrix part (clearedAffinePoly A c)

omit [DecidableEq κ] in
/-- The cleared affine evaluation matrix is exactly a tangent matrix. -/
theorem clearedAffinePartitionMatrix_eq_tangentMatrix
    (part : Fin n ≃ ι ⊕ κ) (A : AffineFractionFamily n H) (c : ℝ) :
    clearedAffinePartitionMatrix part A c =
      TangentRank.tangentMatrix c
        (fun h ↦ affineLeftPart part (A.den h))
        (fun h ↦ affineLeftPart part (A.num h))
        (fun h ↦ affineRightPart part (A.den h))
        (fun h ↦ affineRightPart part (A.num h)) := by
  ext u v
  simp only [clearedAffinePartitionMatrix, polynomialPartitionMatrix,
    clearedAffinePoly, map_add, map_mul, map_prod, map_sum, eval_C,
    TangentRank.tangentMatrix, TangentRank.tangentValue,
    TangentRank.productValue]
  simp_rw [eval_mergePartitionBits_eq_affineParts part (A.den _) (A.den_degree _)]
  simp_rw [eval_mergePartitionBits_eq_affineParts part (A.num _) (A.num_degree _)]

omit [Fintype ι] in
/-- The partition matrix of every nonempty cleared affine-fraction family has
the exact tangent rank cap. -/
theorem clearedAffinePartitionMatrix_rank_le (hH : 0 < H)
    (part : Fin n ≃ ι ⊕ κ) (A : AffineFractionFamily n H) (c : ℝ) :
    (clearedAffinePartitionMatrix part A c).rank ≤ 2 ^ (H + 1) - 2 := by
  classical
  letI := partitionLeftFintype part
  rw [clearedAffinePartitionMatrix_eq_tangentMatrix]
  simpa using TangentRank.tangentMatrix_rank_le
    (I := Fin H) (X := ι → Bool) (Y := κ → Bool) (by simpa using hH) c
    (fun h ↦ affineLeftPart part (A.den h))
    (fun h ↦ affineLeftPart part (A.num h))
    (fun h ↦ affineRightPart part (A.den h))
    (fun h ↦ affineRightPart part (A.num h))

end HeadComplexity
