import HeadComplexity.Polynomial.PureRoPEThreeHeadCross
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.header false

namespace HeadComplexity.PositiveGramObstruction

noncomputable section

open Finset Matrix
open scoped BigOperators

variable {n : ℕ}

/-- A symmetric matrix with nonpositive off-diagonal entries and positive row
sums has a strictly positive quadratic form on every nonzero vector. -/
theorem quadratic_pos_of_row_sums (D : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, D i j = D j i)
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (hrow : ∀ i, 0 < ∑ j, D i j)
    (w : Fin n → ℝ) (hw : w ≠ 0) :
    0 < dotProduct w (D.mulVec w) := by
  classical
  have he : (∑ i, ∑ j, D i j * (w i - w j) ^ 2) =
      2 * (∑ i, (∑ j, D i j) * (w i) ^ 2) -
      2 * dotProduct w (D.mulVec w) := by
    have hsym' : (∑ i, ∑ j, D i j * (w j) ^ 2) =
        ∑ i, ∑ j, D i j * (w i) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym j i]
    simp only [sub_sq, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_mul] at *
    rw [hsym']
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    ring_nf
    simp only [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hle : (∑ i, ∑ j, D i j * (w i - w j) ^ 2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (sq_nonneg _)
  have hpos : 0 < ∑ i, (∑ j, D i j) * (w i) ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hn
      apply hw
      funext i
      simpa using not_exists.mp hn i
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hrow j).le (sq_nonneg _)
    · exact ⟨i, Finset.mem_univ i, mul_pos (hrow i) (sq_pos_of_ne_zero hi)⟩
  linarith

/-- The positive row sums may be supplied after multiplication by an arbitrary
strictly positive vector. -/
theorem quadratic_pos_of_positive_solution (D : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, D i j = D j i)
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hDv : ∀ i, 0 < (D.mulVec v) i)
    (w : Fin n → ℝ) (hw : w ≠ 0) :
    0 < dotProduct w (D.mulVec w) := by
  let E : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ v i * D i j * v j
  let z : Fin n → ℝ := fun i ↦ w i / v i
  have hE : ∀ i j, E i j = E j i := by
    intro i j
    dsimp [E]
    rw [hsym i j]
    ring
  have hoffE : ∀ i j, i ≠ j → E i j ≤ 0 := by
    intro i j hij
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hv i).le (hoff i j hij)) (hv j).le
  have hrowE : ∀ i, 0 < ∑ j, E i j := by
    intro i
    have he : (∑ j, E i j) = v i * (D.mulVec v) i := by
      simp [E, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [he]
    exact mul_pos (hv i) (hDv i)
  have hz : z ≠ 0 := by
    intro h
    apply hw
    funext i
    have hi := congrFun h i
    dsimp [z] at hi
    exact (div_eq_zero_iff).mp hi |>.resolve_right (ne_of_gt (hv i))
  have hp := quadratic_pos_of_row_sums E hE hoffE hrowE z hz
  have he : dotProduct z (E.mulVec z) = dotProduct w (D.mulVec w) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [z, E]
    field_simp [ne_of_gt (hv i), ne_of_gt (hv j)]
  rwa [he] at hp

/-- Column diagonal dominance also gives a strictly positive solution for
any strictly positive right-hand side. -/
theorem positive_solution_of_column_sums [NeZero n]
    (C : Matrix (Fin n) (Fin n) ℝ)
    (hoff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hcol : ∀ j, 0 < ∑ i, C i j)
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧ C.mulVec v = u := by
  classical
  have hoffT : ∀ i j, i ≠ j → C.transpose i j ≤ 0 :=
    fun i j hij ↦ hoff j i (Ne.symm hij)
  have hinjT := PureRoPEThreeHeadCross.mulVec_injective C.transpose hoffT hcol
  have hunit : IsUnit C := (Matrix.isUnit_transpose C).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinjT)
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit u
  refine ⟨v, fun j ↦ ?_, hv⟩
  have hsurjT : Function.Surjective C.transpose.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_transpose C).mpr hunit)
  let ej : Fin n → ℝ := fun i ↦ if i = j then 1 else 0
  obtain ⟨w, hw⟩ := hsurjT ej
  have hwp : ∀ i, 0 ≤ w i := by
    have h := PureRoPEThreeHeadCross.maximum_principle C.transpose hoffT hcol (-w)
      (fun i ↦ by
        rw [Matrix.mulVec_neg, hw]
        dsimp [ej]
        split_ifs <;> norm_num)
    intro i
    simpa using h i
  have hwn : w ≠ 0 := by
    intro hz
    have hj := congrFun hw j
    simp [hz, ej] at hj
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra hn
    apply hwn
    funext i
    exact le_antisymm (le_of_not_gt (not_exists.mp hn i)) (hwp i)
  have hp : 0 < dotProduct w u := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hwp i) (hu i).le
    · exact ⟨i, Finset.mem_univ i, mul_pos hi (hu i)⟩
  have heq : dotProduct w u = v j := by
    rw [← hv, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hw]
    simp [ej, dotProduct]
  rwa [heq] at hp

/-- A common strictly positive column in two square factor matrices prevents
an inverse-positive cross matrix and a nonpositive-off-diagonal Gram matrix
when the middle form has a nonzero isotropic vector in that column direction. -/
theorem gram_obstruction (X Y H : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (e : Fin n → ℝ) (he : e ≠ 0)
    (hnull : dotProduct e (H.mulVec e) = 0)
    (_hXe : ∀ i, 0 < (X.mulVec e) i)
    (hYe : ∀ i, 0 < (Y.mulVec e) i)
    (hinj : Function.Injective (X * H * Y.transpose).mulVec)
    (hsolve : ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧
      (X * H * Y.transpose).mulVec v = X.mulVec e)
    (hGram : ∀ i j, i ≠ j → (Y * H * Y.transpose) i j ≤ 0) : False := by
  let C := X * H * Y.transpose
  let D := Y * H * Y.transpose
  have hinjY : Function.Injective Y.transpose.mulVec := by
    intro a b hab
    apply hinj
    simp only [← Matrix.mulVec_mulVec, hab]
  have hsurjY : Function.Surjective Y.transpose.mulVec := by
    exact LinearMap.injective_iff_surjective.mp
      (show Function.Injective Y.transpose.mulVecLin from hinjY)
  have hsurjC : Function.Surjective C.mulVec := by
    exact LinearMap.injective_iff_surjective.mp
      (show Function.Injective C.mulVecLin from hinj)
  have hsurjX : Function.Surjective X.mulVec := by
    intro a
    obtain ⟨v, hv⟩ := hsurjC a
    refine ⟨H.mulVec (Y.transpose.mulVec v), ?_⟩
    simpa only [C, ← Matrix.mulVec_mulVec] using hv
  have hinjX : Function.Injective X.mulVec := by
    exact LinearMap.injective_iff_surjective.mpr
      (show Function.Surjective X.mulVecLin from hsurjX)
  obtain ⟨v, hv, hCv⟩ := hsolve
  have hHv : H.mulVec (Y.transpose.mulVec v) = e := by
    apply hinjX
    simpa only [← Matrix.mulVec_mulVec] using hCv
  have hDv : ∀ i, 0 < (D.mulVec v) i := by
    intro i
    simpa only [D, ← Matrix.mulVec_mulVec, hHv] using hYe i
  have hsymD : ∀ i j, D i j = D j i := by
    have hH : H.transpose = H := by
      ext i j
      exact hsym j i
    have hD : D.transpose = D := by
      simp only [D, Matrix.transpose_mul, Matrix.transpose_transpose, hH]
      exact (Matrix.mul_assoc _ _ _).symm
    intro i j
    exact congrFun (congrFun hD j) i
  obtain ⟨w, hw⟩ := hsurjY e
  have hw0 : w ≠ 0 := by
    intro hz
    apply he
    simpa [hz] using hw.symm
  have hp := quadratic_pos_of_positive_solution D hsymD hGram v hv hDv w hw0
  have hquad : dotProduct w (D.mulVec w) = dotProduct e (H.mulVec e) := by
    dsimp only [D]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose, hw]
  rw [hquad, hnull] at hp
  exact lt_irrefl 0 hp

/-- The form of the obstruction used by the local Boolean matching witnesses. -/
theorem gram_obstruction_of_column_sums [NeZero n]
    (X Y H : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (e : Fin n → ℝ) (he : e ≠ 0)
    (hnull : dotProduct e (H.mulVec e) = 0)
    (hXe : ∀ i, 0 < (X.mulVec e) i)
    (hYe : ∀ i, 0 < (Y.mulVec e) i)
    (hCross : ∀ i j, i ≠ j → (X * H * Y.transpose) i j ≤ 0)
    (hcol : ∀ j, 0 < ∑ i, (X * H * Y.transpose) i j)
    (hGram : ∀ i j, i ≠ j → (Y * H * Y.transpose) i j ≤ 0) : False := by
  let C := X * H * Y.transpose
  have hoffT : ∀ i j, i ≠ j → C.transpose i j ≤ 0 :=
    fun i j hij ↦ hCross j i (Ne.symm hij)
  have hinjT := PureRoPEThreeHeadCross.mulVec_injective C.transpose hoffT hcol
  have hinjC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_transpose C).mp (Matrix.mulVec_injective_iff_isUnit.mp hinjT))
  exact gram_obstruction X Y H hsym e he hnull hXe hYe hinjC
    (positive_solution_of_column_sums C hCross hcol (X.mulVec e) hXe) hGram

end
end HeadComplexity.PositiveGramObstruction
