import HeadComplexity.Polynomial.FiniteInterpolationBounds
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extract a finite interpolation minor from a one-dimensional kernel

These abstract finite linear-algebra statements justify choosing an invertible
evaluation minor after deleting a nonzero target coefficient. They make no
numerical or generic-position assumption on the sampled rows.
-/

namespace HeadComplexity.FiniteKernelMinor

noncomputable section

open Matrix Module
open scoped BigOperators

theorem exists_rows_det_ne_zero {ζ : Type*} [Finite ζ] {n : ℕ}
    (A : Matrix ζ (Fin n) ℝ) (hA : Function.Injective A.mulVecLin) :
    ∃ rows : Fin n → ζ, (A.submatrix rows id).det ≠ 0 := by
  classical
  letI := Fintype.ofFinite ζ
  have hrank : A.rank = n := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hA]
    simp
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.row)
  rw [← A.rank_eq_finrank_span_row, hrank] at hex
  obtain ⟨f, hf, _, hind⟩ := hex
  choose rows hrows using hf
  refine ⟨rows, ?_⟩
  have heq : (A.submatrix rows id).row = f := by
    funext i
    exact hrows i
  have hi : LinearIndependent ℝ (A.submatrix rows id).row := by rw [heq]; exact hind
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hi))

theorem deleted_columns_injective {ζ : Type*} {n : ℕ}
    (A : Matrix ζ (Fin (n + 1)) ℝ) (F : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hj : F j ≠ 0)
    (hker : ∀ q, A *ᵥ q = 0 → ∃ c : ℝ, q = c • F) :
    Function.Injective (A.submatrix id j.succAbove).mulVecLin := by
  classical
  let B := A.submatrix id j.succAbove
  have hzero (x : Fin n → ℝ) (hx : B *ᵥ x = 0) : x = 0 := by
    let q : Fin (n + 1) → ℝ := Fin.insertNth j 0 x
    have hq : A *ᵥ q = 0 := by
      ext r
      have hx' := congrFun hx r
      change (∑ k, A r k * q k) = 0
      rw [Fin.sum_univ_succAbove _ j]
      simpa [q, B, Matrix.mulVec, dotProduct, Matrix.submatrix] using hx'
    obtain ⟨c, hc⟩ := hker q hq
    have hcj := congrFun hc j
    have hc0 : c = 0 := by
      have hmul : c * F j = 0 := by simpa [q] using hcj.symm
      exact (mul_eq_zero.mp hmul).resolve_right hj
    have hq0 : q = 0 := by simpa [hc0] using hc
    ext i
    have hi := congrFun hq0 (j.succAbove i)
    simpa [q] using hi
  intro x y hxy
  have hx : B *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (hzero (x - y) hx)

theorem exists_deleted_minor {ζ : Type*} [Finite ζ] {n : ℕ}
    (A : Matrix ζ (Fin (n + 1)) ℝ) (F : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hj : F j ≠ 0)
    (hker : ∀ q, A *ᵥ q = 0 → ∃ c : ℝ, q = c • F) :
    ∃ rows : Fin n → ζ, (A.submatrix rows j.succAbove).det ≠ 0 := by
  obtain ⟨rows, hr⟩ := exists_rows_det_ne_zero (A.submatrix id j.succAbove)
    (deleted_columns_injective A F j hj hker)
  exact ⟨rows, hr⟩

theorem strict_coefficient_recovery {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hBA : B * A = 1) (x : Fin n → ℝ) (K ε : ℝ) (hε : 0 < ε)
    (hB : ∀ i, ∑ j, |B i j| < K)
    (hx : ∀ i, |(A *ᵥ x) i| ≤ ε) (i : Fin n) : |x i| < K * ε := by
  have hid : B *ᵥ (A *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  rw [← hid]
  change |∑ j, B i j * (A *ᵥ x) j| < K * ε
  calc
    _ ≤ ∑ j, |B i j * (A *ᵥ x) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |B i j| * ε := Finset.sum_le_sum fun j _ ↦ by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |B i j|) * ε := (Finset.sum_mul _ _ _).symm
    _ < K * ε := mul_lt_mul_of_pos_right (hB i) hε

/-- A finite evaluation matrix with one-dimensional kernel forces a polynomial
with small evaluations to be coefficientwise close to a scalar target. The
row denominator and size assumptions are precisely those of the chart proof. -/
theorem quantitative_kernel_recovery {ζ : Type*} [Finite ζ]
    (A : Matrix ζ (Fin 680) ℝ) (F Q : Fin 680 → ℝ) (j : Fin 680)
    (hj : F j ≠ 0) (hF : A *ᵥ F = 0)
    (hker : ∀ q, A *ᵥ q = 0 → ∃ c : ℝ, q = c • F)
    (K : Matrix ζ (Fin 680) ℤ) (q : ζ → ℝ)
    (hA : ∀ r k, |A r k| ≤ 1) (hq : ∀ r, 0 < q r)
    (hqbound : ∀ r, q r ≤ (2 : ℝ) ^ 414)
    (hrow : ∀ r k, q r * A r k = (K r k : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hQ : ∀ r, |(A *ᵥ Q) r| ≤ ε) :
    ∃ c : ℝ, ∀ k, |Q k - c * F k| < (2 : ℝ) ^ 300000 * ε := by
  classical
  obtain ⟨rows, hdet⟩ := exists_deleted_minor A F j hj hker
  let M := A.submatrix rows j.succAbove
  let c := Q j / F j
  let u := Q - c • F
  let x : Fin 679 → ℝ := fun k ↦ u (j.succAbove k)
  have huj : u j = 0 := by
    dsimp [u, c]
    field_simp
    ring
  have hu : A *ᵥ u = A *ᵥ Q := by
    simp only [u, Matrix.mulVec_sub, Matrix.mulVec_smul, hF, smul_zero, sub_zero]
  have hMx (r : Fin 679) : (M *ᵥ x) r = (A *ᵥ Q) (rows r) := by
    rw [← hu]
    change (∑ k, A (rows r) (j.succAbove k) * u (j.succAbove k)) =
      ∑ k, A (rows r) k * u k
    rw [Fin.sum_univ_succAbove _ j, huj, mul_zero, zero_add]
  have hinv : M⁻¹ * M = 1 :=
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
  have hbound (r : Fin 679) : ∑ k, |M⁻¹ r k| < (2 : ℝ) ^ 300000 := by
    exact FiniteInterpolationBounds.inverse_row_bound_679 M
      (K.submatrix rows j.succAbove) (q ∘ rows)
      (fun r k ↦ hA (rows r) (j.succAbove k)) (fun r ↦ hq (rows r))
      (fun r ↦ hqbound (rows r)) hdet
      (fun r k ↦ hrow (rows r) (j.succAbove k)) r
  have hx (r : Fin 679) : |x r| < (2 : ℝ) ^ 300000 * ε :=
    strict_coefficient_recovery M M⁻¹ hinv x _ ε hε hbound
      (fun k ↦ by rw [hMx]; exact hQ _) r
  refine ⟨c, ?_⟩
  intro k
  by_cases hk : k = j
  · subst k
    change |u j| < _
    rw [huj, abs_zero]
    exact mul_pos (pow_pos (by norm_num) _) hε
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hk
    subst k
    exact hx r

end
end HeadComplexity.FiniteKernelMinor
