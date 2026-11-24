import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
A compact full-dimensional system of separately affine inequalities need not
have a point with four independent active normals.  This is an obstruction to
a generic active-contact argument, not a counterexample for original heads.
-/
noncomputable section
namespace HeadComplexity.BlockAffineNoVertex
open scoped BigOperators

abbrev Point := Fin 4 → ℝ

def constraints (p : Point) : Fin 5 → ℝ :=
  ![1 - p 0 + p 2, 1 + p 0 - p 2,
    1 - p 1 + p 3, 1 + p 1 - p 3,
    1 - p 0 * p 2 - p 1 * p 3]

def Feasible (p : Point) : Prop := ∀ i, 0 ≤ constraints p i

def normals (p : Point) : Matrix (Fin 5) (Fin 4) ℝ :=
  ![![-1, 0, 1, 0], ![1, 0, -1, 0],
    ![0, -1, 0, 1], ![0, 1, 0, -1],
    ![-p 2, -p 3, -p 0, -p 1]]

theorem zero_strict : ∀ i, 0 < constraints 0 i := by
  intro i
  fin_cases i <;> norm_num [constraints]

theorem feasible_square_bound (p : Point) (hp : Feasible p) :
    ∑ i, (p i)^2 ≤ 4 := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  norm_num [constraints] at h0 h1 h2 h3 h4
  have hd0 : (p 0 - p 2)^2 ≤ 1 := by nlinarith
  have hd1 : (p 1 - p 3)^2 ≤ 1 := by nlinarith
  simp only [Fin.sum_univ_succ]
  norm_num
  nlinarith

theorem feasible_coordinate_bound (p : Point) (hp : Feasible p) (i : Fin 4) :
    |p i| ≤ 2 := by
  have h := feasible_square_bound p hp
  have hi : (p i)^2 ≤ ∑ j, (p j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (p i + 2), sq_nonneg (p i - 2)]

theorem continuous_constraint (i : Fin 5) : Continuous (fun p : Point => constraints p i) := by
  fin_cases i <;> unfold constraints <;> fun_prop

theorem feasible_isClosed : IsClosed {p : Point | Feasible p} := by
  simp only [Feasible, Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_constraint i))

theorem feasible_isCompact : IsCompact {p : Point | Feasible p} := by
  have hc : IsCompact (Set.Icc (fun _ : Fin 4 => (-2 : ℝ)) (fun _ => 2)) :=
    isCompact_Icc
  apply hc.of_isClosed_subset feasible_isClosed
  intro p hp
  constructor <;> intro i
  · exact (abs_le.mp (feasible_coordinate_bound p hp i)).1
  · exact (abs_le.mp (feasible_coordinate_bound p hp i)).2

/-- The full five-row normal matrix, and hence every active submatrix, has
rank at most three at every parameter point. -/
theorem normals_rank_le_three (p : Point) : (normals p).rank ≤ 3 := by
  let L : Matrix (Fin 5) (Fin 3) ℝ :=
    ![![1,0,0], ![-1,0,0], ![0,1,0], ![0,-1,0], ![0,0,1]]
  let R : Matrix (Fin 3) (Fin 4) ℝ :=
    ![![-1,0,1,0], ![0,-1,0,1], ![-p 2,-p 3,-p 0,-p 1]]
  have hf : normals p = L * R := by
    ext i j
    change normals p i j = ∑ k : Fin 3, L i k * R k j
    fin_cases i <;> fin_cases j <;>
      norm_num [normals, L, R, Fin.sum_univ_succ]
  rw [hf]
  exact (Matrix.rank_mul_le_left L R).trans (by
    simpa using Matrix.rank_le_card_width L)

/-- Each constraint is affine in the first two coordinates when the second
block is fixed. -/
theorem first_block_affine (p q : Point) (t : ℝ)
    (h2 : p 2 = q 2) (h3 : p 3 = q 3) (i : Fin 5) :
    constraints (t • p + (1-t) • q) i =
      t * constraints p i + (1-t) * constraints q i := by
  fin_cases i <;> simp [constraints, Pi.add_apply, Pi.smul_apply, h2, h3] <;> ring

/-- The same is true in the second parameter block. -/
theorem second_block_affine (p q : Point) (t : ℝ)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (i : Fin 5) :
    constraints (t • p + (1-t) • q) i =
      t * constraints p i + (1-t) * constraints q i := by
  fin_cases i <;> simp [constraints, Pi.add_apply, Pi.smul_apply, h0, h1] <;> ring

/-- Translation by three places the whole feasible region strictly inside
an ambient positive box.  Thus positivity and inactive box faces do not fix
the missing full-rank contact certificate. -/
theorem translated_coordinate_bounds (p : Point) (hp : Feasible p) (i : Fin 4) :
    0 < p i + 3 ∧ p i + 3 < 6 := by
  have h := feasible_coordinate_bound p hp i
  rw [abs_le] at h
  constructor <;> linarith

end HeadComplexity.BlockAffineNoVertex
