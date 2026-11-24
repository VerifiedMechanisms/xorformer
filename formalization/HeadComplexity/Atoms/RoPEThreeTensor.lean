import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite tensor algebra for the three-head grid investigation

These lemmas concern contraction ranks and coefficient cones. They do not by
themselves assert a Boolean head-count separation.
-/

namespace HeadComplexity.RoPEThreeTensor

open scoped BigOperators

noncomputable def cross (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, v 2, v 1; v 2, 0, v 0; v 1, v 0, 0]

noncomputable def pureContraction (d u : Fin 3 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, u 2, u 1, 0, d 2, d 1;
     u 2, 0, u 0, d 2, 0, d 0;
     u 1, u 0, 0, d 1, d 0, 0;
     0, d 2, d 1, 0, 0, 0;
     d 2, 0, d 0, 0, 0, 0;
     d 1, d 0, 0, 0, 0, 0]

noncomputable def minorFour (d u : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ match i.val, j.val with
    | 0, 1 | 1, 0 => u
    | 0, 3 | 3, 0 | 1, 2 | 2, 1 => d
    | _, _ => 0

def minorIndex (i : Fin 3) : Fin 4 → Fin 6 :=
  ![![1, 2, 4, 5], ![0, 2, 3, 5], ![0, 1, 3, 4]] i

set_option maxRecDepth 2000 in
theorem minorFour_det (d u : ℝ) : (minorFour d u).det = d^4 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [minorFour, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
    Fin.lt_def]
  ring

theorem pureContraction_minor (d u : Fin 3 → ℝ) (i : Fin 3) :
    (pureContraction d u).submatrix (minorIndex i) (minorIndex i) = minorFour (d i) (u i) := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> rfl

/-- Each nonzero denominator coordinate forces a nonsingular four-dimensional
minor, independently of the numerator coordinates. -/
theorem denominator_zero_of_rank_le_three (d u : Fin 3 → ℝ)
    (hr : (pureContraction d u).rank ≤ 3) : d = 0 := by
  ext i
  by_contra hi
  have hdet : (minorFour (d i) (u i)).det ≠ 0 := by
    rw [minorFour_det]
    exact pow_ne_zero _ hi
  have hu : IsUnit (minorFour (d i) (u i)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hfour : (minorFour (d i) (u i)).rank = 4 := by
    simpa using Matrix.rank_of_isUnit _ hu
  have hsmall := Matrix.rank_submatrix_le (pureContraction d u) (minorIndex i) (minorIndex i)
  rw [pureContraction_minor, hfour] at hsmall
  omega

theorem pureContraction_rank_le_three_iff (d u : Fin 3 → ℝ) :
    (pureContraction d u).rank ≤ 3 ↔ d = 0 := by
  constructor
  · exact denominator_zero_of_rank_le_three d u
  · intro hd
    subst d
    let L : Matrix (Fin 6) (Fin 3) ℝ :=
      !![0, u 2, u 1; u 2, 0, u 0; u 1, u 0, 0; 0, 0, 0; 0, 0, 0; 0, 0, 0]
    let R : Matrix (Fin 3) (Fin 6) ℝ :=
      !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0]
    have he : pureContraction 0 u = L * R := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pureContraction, L, R, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [he]
    exact (Matrix.rank_mul_le_left L R).trans (by simpa using Matrix.rank_le_card_width L)

/-- The rank detector is stable under limits, without any boundedness assumption
on a factorization of the approximating matrices. -/
theorem denominator_zero_of_tendsto_low_rank
    (A : ℕ → Matrix (Fin 6) (Fin 6) ℝ) (d u : Fin 3 → ℝ)
    (hr : ∀ k, (A k).rank ≤ 3)
    (hlim : Filter.Tendsto A Filter.atTop (nhds (pureContraction d u))) : d = 0 := by
  ext i
  have hz (k : ℕ) : ((A k).submatrix (minorIndex i) (minorIndex i)).det = 0 := by
    by_contra hn
    have hu : IsUnit ((A k).submatrix (minorIndex i) (minorIndex i)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
    have hf : ((A k).submatrix (minorIndex i) (minorIndex i)).rank = 4 := by
      simpa using Matrix.rank_of_isUnit _ hu
    have hs := Matrix.rank_submatrix_le (A k) (minorIndex i) (minorIndex i)
    rw [hf] at hs
    have := hr k
    omega
  have hc : Continuous (fun M : Matrix (Fin 6) (Fin 6) ℝ ↦
      (M.submatrix (minorIndex i) (minorIndex i)).det) := by fun_prop
  have hp := hc.continuousAt.tendsto.comp hlim
  simp only [Function.comp_def, pureContraction_minor, minorFour_det] at hp
  have hzero : Filter.Tendsto
      (fun k ↦ ((A k).submatrix (minorIndex i) (minorIndex i)).det)
      Filter.atTop (nhds (0 : ℝ)) := by simpa only [hz] using tendsto_const_nhds
  have he : (d i)^4 = 0 := tendsto_nhds_unique hp hzero
  by_contra hn
  exact pow_ne_zero 4 hn he

/-- The mixed block tensor contraction of a three-head cleared cubic. -/
noncomputable def crossContraction
    (Dx Nx Dy Ny : Matrix (Fin 3) (Fin 6) ℝ) (d u : Fin 3 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  Dx.transpose * cross u * Dy + Nx.transpose * cross d * Dy + Dx.transpose * cross d * Ny

theorem cross_zero : cross 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Killing all three denominator covectors gives contraction rank at most
three, for arbitrary numerator coefficients. -/
theorem crossContraction_rank_le_three
    (Dx Nx Dy Ny : Matrix (Fin 3) (Fin 6) ℝ) (u : Fin 3 → ℝ) :
    (crossContraction Dx Nx Dy Ny 0 u).rank ≤ 3 := by
  simp only [crossContraction, cross_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width Dx.transpose))

noncomputable def denominatorRows (ε : ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  !![ε, 0, 0, -ε, 0, 0; 0, ε, 0, 0, -ε, 0; 0, 0, ε, 0, 0, -ε]

noncomputable def numeratorRows (δ : ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  !![2*δ, δ, δ, δ, δ, δ; δ, 2*δ, δ, δ, δ, δ; δ, δ, 2*δ, δ, δ, δ]

/-- The six denominator and numerator linear coordinates in one source block. -/
noncomputable def blockCoordinates (ε δ : ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![ε * (x 0 - x 3), ε * (x 1 - x 4), ε * (x 2 - x 5),
    δ * ((∑ i, x i) + x 0), δ * ((∑ i, x i) + x 1),
    δ * ((∑ i, x i) + x 2)]

theorem blockCoordinates_injective (ε δ : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) :
    Function.Injective (blockCoordinates ε δ) := by
  intro x y h
  have h0 := congrFun h (0 : Fin 6)
  have h1 := congrFun h (1 : Fin 6)
  have h2 := congrFun h (2 : Fin 6)
  have h3 := congrFun h (3 : Fin 6)
  have h4 := congrFun h (4 : Fin 6)
  have h5 := congrFun h (5 : Fin 6)
  simp only [blockCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3 h4 h5
  have e0 := mul_left_cancel₀ hε h0
  have e1 := mul_left_cancel₀ hε h1
  have e2 := mul_left_cancel₀ hε h2
  have e3 := mul_left_cancel₀ hδ h3
  have e4 := mul_left_cancel₀ hδ h4
  have e5 := mul_left_cancel₀ hδ h5
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at e3 e4 e5
  change x 0 + (x 1 + (x 2 + (x 3 + (x 4 + x 5)))) + x 0 =
    y 0 + (y 1 + (y 2 + (y 3 + (y 4 + y 5)))) + y 0 at e3
  change x 0 + (x 1 + (x 2 + (x 3 + (x 4 + x 5)))) + x 1 =
    y 0 + (y 1 + (y 2 + (y 3 + (y 4 + y 5)))) + y 1 at e4
  change x 0 + (x 1 + (x 2 + (x 3 + (x 4 + x 5)))) + x 2 =
    y 0 + (y 1 + (y 2 + (y 3 + (y 4 + y 5)))) + y 2 at e5
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith only [e0, e1, e2, e3, e4, e5]
  · change x 1 = y 1
    linarith only [e0, e1, e2, e3, e4, e5]
  · change x 2 = y 2
    linarith only [e0, e1, e2, e3, e4, e5]
  · change x 3 = y 3
    linarith only [e0, e1, e2, e3, e4, e5]
  · change x 4 = y 4
    linarith only [e0, e1, e2, e3, e4, e5]
  · change x 5 = y 5
    linarith only [e0, e1, e2, e3, e4, e5]

noncomputable def blockMatrix (ε δ : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![ε, 0, 0, -ε, 0, 0; 0, ε, 0, 0, -ε, 0; 0, 0, ε, 0, 0, -ε;
    2*δ, δ, δ, δ, δ, δ; δ, 2*δ, δ, δ, δ, δ; δ, δ, 2*δ, δ, δ, δ]

theorem blockMatrix_mulVec (ε δ : ℝ) (x : Fin 6 → ℝ) :
    (blockMatrix ε δ).mulVec x = blockCoordinates ε δ x := by
  ext i
  fin_cases i <;>
    simp [blockMatrix, blockCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem blockMatrix_isUnit (ε δ : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) :
    IsUnit (blockMatrix ε δ) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  apply blockCoordinates_injective ε δ hε hδ
  simpa only [blockMatrix_mulVec] using h

/-- An invertible change to the concrete source coordinates preserves the
rank detector. This is the rank locus in any of the three six-variable blocks. -/
theorem transformed_pureContraction_rank_le_three_iff
    (ε δ : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (d u : Fin 3 → ℝ) :
    ((blockMatrix ε δ).transpose * pureContraction d u * blockMatrix ε δ).rank ≤ 3 ↔
      d = 0 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (blockMatrix_isUnit ε δ hε hδ)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by simpa using hu)]
  exact pureContraction_rank_le_three_iff d u

theorem denominatorRows_sum (ε : ℝ) (h : Fin 3) :
    (∑ i, denominatorRows ε h i) = 0 := by
  fin_cases h <;> simp [denominatorRows, Fin.sum_univ_succ]

/-- The denominator row span has coordinate sum zero. -/
theorem denominator_combination_sum (ε : ℝ) (a : Fin 3 → ℝ) :
    (∑ i, ∑ h, a h * denominatorRows ε h i) = 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, denominatorRows_sum, mul_zero]
  simp

/-- In particular no row in this span can be normalized to have sum one. -/
theorem no_normalized_denominator_combination (ε : ℝ) (a : Fin 3 → ℝ)
    (v : Fin 6 → ℝ) (hv : v = fun i ↦ ∑ h, a h * denominatorRows ε h i) :
    (∑ i, v i) ≠ 1 := by
  rw [hv, denominator_combination_sum]
  norm_num

end HeadComplexity.RoPEThreeTensor
