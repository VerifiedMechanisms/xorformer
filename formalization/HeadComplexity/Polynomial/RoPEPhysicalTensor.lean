import HeadComplexity.Polynomial.RoPEPhysicalCoordinates
import HeadComplexity.Polynomial.RoPEMixedTensor
import HeadComplexity.Polynomial.RoPECrossBlockCoefficients
import HeadComplexity.Atoms.RoPETensorFactors

set_option linter.style.header false

/-!
# The actual mixed tensor of the physical source polynomial

Restriction to three selected variables identifies an arbitrary mixed cubic
coefficient with the six assignments to three affine factors.
-/

namespace HeadComplexity.RoPEPhysicalTensor

open scoped BigOperators
open MvPolynomial RoPEMixedTensor RoPEThreeTensor RoPEPhysicalCoordinates
open RoPECrossBlockCoefficients

theorem killCompl_affine {σ : Type*} [Fintype σ]
    (f : Fin 3 → σ) (hf : Function.Injective f) (a : ℝ) (v : σ → ℝ) :
    killCompl hf (affine a v) = affine a (fun i ↦ v (f i)) := by
  classical
  simp only [affine, map_add, killCompl_C, map_sum, map_mul]
  congr 1
  apply Eq.symm
  apply Fintype.sum_of_injective f hf
  · intro j hj
    have hx : killCompl hf (X j : MvPolynomial σ ℝ) = 0 := by
      simp only [killCompl, aeval_X, dif_neg hj]
    rw [hx, mul_zero]
  · intro i
    have hx : killCompl hf (X (f i) : MvPolynomial σ ℝ) = X i := by
      rw [← rename_X f i, killCompl_rename_app]
    rw [hx]

theorem coeff_three_selected_affine_product {σ : Type*} [Fintype σ]
    (f : Fin 3 → σ) (hf : Function.Injective f)
    (a b c : ℝ) (A B C' : σ → ℝ) :
    coeff (threeExponent.mapDomain f) (affine a A * affine b B * affine c C') =
      A (f 0) * B (f 1) * C' (f 2) + A (f 0) * B (f 2) * C' (f 1) +
      A (f 1) * B (f 0) * C' (f 2) + A (f 1) * B (f 2) * C' (f 0) +
      A (f 2) * B (f 0) * C' (f 1) + A (f 2) * B (f 1) * C' (f 0) := by
  rw [← coeff_killCompl hf]
  simp only [map_mul, killCompl_affine, coeff_three_affine_product]

def select (i j k : Fin 6) : Fin 3 → Fin 18 :=
  ![blockIndex 0 i, blockIndex 1 j, blockIndex 2 k]

theorem select_injective (i j k : Fin 6) : Function.Injective (select i j k) := by
  have hval (a : Fin 3) : (select i j k a).val / 6 = a.val := by
    fin_cases a <;> simp [select, blockIndex] <;> omega
  intro a b hab
  apply Fin.ext
  have h := congrArg (fun q : Fin 18 ↦ q.val / 6) hab
  simpa only [hval] using h

theorem threeExponent_map_select (i j k : Fin 6) :
    threeExponent.mapDomain (select i j k) = mixedExponent i j k := by
  simp [threeExponent, mixedExponent, select, Finsupp.mapDomain_add]

theorem coeff_mixed_affine_product
    (i j k : Fin 6) (a b c : ℝ) (A B C' : Fin 18 → ℝ) :
    coeff (mixedExponent i j k) (affine a A * affine b B * affine c C') =
      A (blockIndex 0 i) * B (blockIndex 1 j) * C' (blockIndex 2 k) +
      A (blockIndex 0 i) * B (blockIndex 2 k) * C' (blockIndex 1 j) +
      A (blockIndex 1 j) * B (blockIndex 0 i) * C' (blockIndex 2 k) +
      A (blockIndex 1 j) * B (blockIndex 2 k) * C' (blockIndex 0 i) +
      A (blockIndex 2 k) * B (blockIndex 0 i) * C' (blockIndex 1 j) +
      A (blockIndex 2 k) * B (blockIndex 1 j) * C' (blockIndex 0 i) := by
  rw [← threeExponent_map_select]
  simpa [select] using coeff_three_selected_affine_product
    (select i j k) (select_injective i j k) a b c A B C'

theorem d_blockIndex (h b : Fin 3) (i : Fin 6) :
    PureThreeReplicatedGrid.d h (blockIndex b i) = denominatorRows 1 h i := by
  fin_cases h <;> fin_cases b <;> fin_cases i <;>
    norm_num [PureThreeReplicatedGrid.d, blockIndex, denominatorRows]

theorem u_blockIndex (h b : Fin 3) (i : Fin 6) :
    PureThreeReplicatedGrid.u h (blockIndex b i) = numeratorRows 2 h i := by
  fin_cases h <;> fin_cases b <;> fin_cases i <;>
    norm_num [PureThreeReplicatedGrid.u, blockIndex, numeratorRows]

/-- The mixed coefficient tensor of any three-head cleared affine numerator,
with no restrictions on its constants or slopes. -/
theorem mixedTensor_three_affine
    (nc dc : Fin 3 → ℝ) (N D : Fin 3 → Fin 18 → ℝ) :
    mixedTensor
      (affine (nc 0) (N 0) * affine (dc 1) (D 1) * affine (dc 2) (D 2) +
        affine (nc 1) (N 1) * affine (dc 0) (D 0) * affine (dc 2) (D 2) +
        affine (nc 2) (N 2) * affine (dc 0) (D 0) * affine (dc 1) (D 1)) =
      factorTensor
        (fun h i ↦ D h (blockIndex 0 i)) (fun h i ↦ N h (blockIndex 0 i))
        (fun h i ↦ D h (blockIndex 1 i)) (fun h i ↦ N h (blockIndex 1 i))
        (fun h i ↦ D h (blockIndex 2 i)) (fun h i ↦ N h (blockIndex 2 i)) := by
  ext i j k
  simp only [mixedTensor, coeff_add, coeff_mixed_affine_product]
  simp [factorTensor, crossContraction, cross, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem mixedTensor_physical : mixedTensor physical =
    factorTensor (denominatorRows 1) (numeratorRows 2)
      (denominatorRows 1) (numeratorRows 2) (denominatorRows 1) (numeratorRows 2) := by
  ext i j k
  rw [physical_explicit]
  simp only [mixedTensor, coeff_add]
  have hd (h : Fin 3) : denominatorPolynomial h = affine 200 (PureThreeReplicatedGrid.d h) := rfl
  have hn (h : Fin 3) : numeratorPolynomial h = affine 0 (PureThreeReplicatedGrid.u h) := by
    simp [numeratorPolynomial, affine]
  simp only [hd, hn, coeff_mixed_affine_product, d_blockIndex, u_blockIndex]
  simp [factorTensor, crossContraction, cross, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem mixedTensor_physical_ne_zero : mixedTensor physical ≠ 0 := by
  intro h
  have he := congrFun (congrFun (congrFun h 0) 1) 2
  rw [mixedTensor_physical] at he
  norm_num [factorTensor, crossContraction, cross, denominatorRows, numeratorRows,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at he

end HeadComplexity.RoPEPhysicalTensor
