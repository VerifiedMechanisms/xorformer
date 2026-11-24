import HeadComplexity.Polynomial.ExplicitCubicQuantitativeBounds
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block

set_option linter.style.header false

/-! # Uniform determinant bounds for every six-row target coefficient minor -/

namespace HeadComplexity.ExplicitCubicVandermonde
noncomputable section
open scoped BigOperators Matrix
open PureRoPEReplication GenericCubicHessianPullback ExplicitCubicQuantitativeBounds

/-- The six coefficient columns in ordinary `Fin 6` order. -/
def rows (a : Fin 6 → Fin 14) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i ↦ ![baseS 0 (a i), baseS 1 (a i), baseS 2 (a i),
    baseB 0 (a i), baseB 1 (a i), baseB 2 (a i)]

def changeColumns : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1 / 10000, 0, 0, -(15 / 2 : ℝ)^3 / 1000000000,
      -(15 / 2 : ℝ)^4 / 1000000000, -(15 / 2 : ℝ)^5 / 1000000000;
    0, 1 / 10000, 0, 0, 0, 0;
    0, 0, 1 / 10000, 0, 0, 0;
    0, 0, 0, 1 / 1000000000, 0, 0;
    0, 0, 0, 0, 1 / 1000000000, 0;
    0, 0, 0, 0, 0, 1 / 1000000000]

theorem rows_factorization (a : Fin 6 → Fin 14) :
    rows a = Matrix.vandermonde (fun i ↦ ((a i).val + 1 : ℝ)) * changeColumns := by
  ext i j
  fin_cases j <;>
    norm_num [rows, changeColumns, baseS, baseB, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.vandermonde_apply] <;> ring

theorem changeColumns_det : changeColumns.det = 1 / (10 : ℝ)^39 := by
  have ht : changeColumns.BlockTriangular id := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [changeColumns] at *
  rw [Matrix.det_of_upperTriangular ht]
  norm_num [changeColumns, Fin.prod_univ_succ]

theorem rows_det (a : Fin 6 → Fin 14) :
    (rows a).det = (Matrix.vandermonde (fun i ↦ ((a i).val + 1 : ℝ))).det /
      (10 : ℝ)^39 := by
  rw [rows_factorization, Matrix.det_mul, changeColumns_det]
  ring

/-- Divisibility by the fifth superfactorial gives the uniform integer bound,
without sorting the selected coordinates or enumerating their possible subsets. -/
theorem integer_vandermonde_lower (v : Fin 6 → ℤ) (hv : Function.Injective v) :
    34560 ≤ |(Matrix.vandermonde v).det| := by
  have hd := Matrix.superFactorial_dvd_vandermonde_det (n := 5) v
  have hn : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hl := Int.natAbs_le_of_dvd_ne_zero hd hn
  norm_num [Nat.superFactorial] at hl
  have hr : (34560 : ℤ) ≤ ((Matrix.vandermonde v).det.natAbs : ℤ) := by exact_mod_cast hl
  simpa only [Int.natCast_natAbs] using hr

theorem rows_det_lower (a : Fin 6 → Fin 14) (ha : Function.Injective a) :
    vandermondeBound ≤ |(rows a).det| := by
  let v : Fin 6 → ℤ := fun i ↦ (a i).val + 1
  have hv : Function.Injective v := by
    intro i j hij
    apply ha
    apply Fin.ext
    dsimp [v] at hij
    omega
  have hl := integer_vandermonde_lower v hv
  have hcast : ((Matrix.vandermonde v).det : ℝ) =
      (Matrix.vandermonde (fun i ↦ ((a i).val + 1 : ℝ))).det := by
    rw [Int.cast_det]
    congr 1
    ext i j
    simp [Matrix.vandermonde_apply, v]
  have hlreal : (34560 : ℝ) ≤ |(Matrix.vandermonde (fun i ↦ ((a i).val + 1 : ℝ))).det| := by
    rw [← hcast]
    exact_mod_cast hl
  rw [rows_det, abs_div]
  unfold vandermondeBound
  rw [abs_of_pos (by positivity : (0 : ℝ) < 10^39)]
  exact div_le_div_of_nonneg_right hlreal (by positivity)


theorem sum_rows_det_lower (a : Fin 3 ⊕ Fin 3 → Fin 14)
    (ha : Function.Injective a) :
    vandermondeBound ≤ |((slopes baseS baseB).submatrix a id).det| := by
  have hm : ((slopes baseS baseB).submatrix a id).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm =
        rows (a ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm) := by
    ext i j
    fin_cases j <;> simp [rows, slopes, Matrix.submatrix_apply, finSumFinEquiv,
      Fin.addCases]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm, hm]
  exact rows_det_lower _ (ha.comp finSumFinEquiv.symm.injective)

def nonzeroBound : Fin 3 → ℝ :=
  ![631 / 8000000000, 12209 / 16000000000, 221551 / 32000000000]

@[simp] theorem nonzeroBound_zero : nonzeroBound 0 = 631 / 8000000000 := rfl
@[simp] theorem nonzeroBound_one : nonzeroBound 1 = 12209 / 16000000000 := rfl
@[simp] theorem nonzeroBound_two : nonzeroBound 2 = 221551 / 32000000000 := rfl

theorem nonzeroBound_pos (h : Fin 3) : 0 < nonzeroBound h := by
  fin_cases h <;> norm_num [nonzeroBound]

theorem baseB_abs_lower (h : Fin 3) (i : Fin 14) :
    nonzeroBound h ≤ |baseB h i| := by
  fin_cases h <;> fin_cases i <;> norm_num [nonzeroBound, baseB]

def crossGap : ℝ := 4 * vandermondeBound^2 *
  (nonzeroBound 0 * nonzeroBound 1 * nonzeroBound 2)^2

theorem crossGap_pos : 0 < crossGap := by
  have hv := vandermondeBound_pos
  have h0 := nonzeroBound_pos 0
  have h1 := nonzeroBound_pos 1
  have h2 := nonzeroBound_pos 2
  unfold crossGap
  positivity

theorem cross_hessian_det_lower (k : Fin 14)
    (a b : Fin 3 ⊕ Fin 3 → Fin 14)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    crossGap ≤ |((polynomialHessian (cubic baseS baseB)
      (Pi.single k 1)).submatrix a b).det| := by
  rw [cross_hessian_det]
  simp only [linearValue, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, abs_mul, abs_pow]
  rw [show |(-4 : ℝ)| = 4 by norm_num]
  have ha' := sum_rows_det_lower a ha
  have hb' := sum_rows_det_lower b hb
  have h0 := baseB_abs_lower 0 k
  have h1 := baseB_abs_lower 1 k
  have h2 := baseB_abs_lower 2 k
  have hpos (h : Fin 3) := (nonzeroBound_pos h).le
  unfold crossGap
  calc
    _ = 4 * vandermondeBound * vandermondeBound *
      (nonzeroBound 0 * nonzeroBound 1 * nonzeroBound 2)^2 := by ring
    _ ≤ _ := by
      gcongr <;> norm_num [nonzeroBound, vandermondeBound]
      all_goals exact (nonzeroBound_pos _).le

theorem cross_hessian_fin_det_lower (k : Fin 14) (a b : Fin 6 → Fin 14)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    crossGap ≤ |((polynomialHessian (cubic baseS baseB)
      (Pi.single k 1)).submatrix a b).det| := by
  have h := cross_hessian_det_lower k (a ∘ finSumFinEquiv) (b ∘ finSumFinEquiv)
    (ha.comp finSumFinEquiv.injective) (hb.comp finSumFinEquiv.injective)
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm] at h
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using h

/-- Twelve remaining coordinates split into two disjoint six-coordinate blocks. -/
theorem exists_disjoint_blocks (i k : Fin 14) (hik : i ≠ k) :
    ∃ a b : Fin 6 → Fin 14, Function.Injective a ∧ Function.Injective b ∧
      (∀ p, a p ≠ i ∧ a p ≠ k ∧ b p ≠ i ∧ b p ≠ k) ∧
      (∀ p q, a p ≠ b q) := by
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hik.symm
  let e : Fin 12 → Fin 14 := fun p ↦ i.succAbove (k'.succAbove p)
  have he : Function.Injective e :=
    Fin.succAbove_right_injective.comp Fin.succAbove_right_injective
  have hei (p) : e p ≠ i := Fin.succAbove_ne _ _
  have hek (p) : e p ≠ k := by
    rw [← hk']
    exact fun h ↦ Fin.succAbove_ne k' p (Fin.succAbove_right_injective h)
  let a : Fin 6 → Fin 14 := fun p ↦ e (Fin.castAdd 6 p)
  let b : Fin 6 → Fin 14 := fun p ↦ e (Fin.natAdd 6 p)
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro p q h
    apply Fin.ext
    have := congrArg Fin.val (he h)
    simpa [a] using this
  · intro p q h
    apply Fin.ext
    have := congrArg Fin.val (he h)
    simp only [Fin.val_natAdd] at this
    omega
  · intro p
    exact ⟨hei _, hek _, hei _, hek _⟩
  · intro p q h
    have := congrArg Fin.val (he h)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem exists_cross_lower (i k : Fin 14) (hik : i ≠ k) :
    ∃ a b : Fin 6 → Fin 14,
      (∀ p, a p ≠ i ∧ a p ≠ k ∧ b p ≠ i ∧ b p ≠ k) ∧
      (∀ p q, a p ≠ b q) ∧
      crossGap ≤ |((polynomialHessian (cubic baseS baseB)
        (Pi.single k 1)).submatrix a b).det| := by
  obtain ⟨a, b, ha, hb, hav, hab⟩ := exists_disjoint_blocks i k hik
  exact ⟨a, b, hav, hab, cross_hessian_fin_det_lower k a b ha hb⟩

end
end HeadComplexity.ExplicitCubicVandermonde
