import HeadComplexity.Polynomial.RoPECrossBlockCoefficients
import Mathlib.Combinatorics.Nullstellensatz

set_option linter.style.header false

/-!
# Top squarefree coefficients determined by centered Boolean values

The argument uses polynomial interpolation on the two-point set in each
variable. It concerns top-degree squarefree coefficients; general real-score
representations need not have equal coefficients.
-/

namespace HeadComplexity.RoPECrossBlockCoefficients

open scoped BigOperators
open MvPolynomial

theorem centeredReduction_degreeOf_le {σ : Type*}
    (P : MvPolynomial σ ℝ) (i : σ) :
    (centeredReduction P).degreeOf i ≤ 1 := by
  classical
  apply (degreeOf_sum_le i P.support _).trans
  apply Finset.sup_le
  intro d hd
  rw [degreeOf_monomial_eq _ _ (mem_support_iff.mp hd)]
  change d i % 2 ≤ 1
  omega

theorem eq_of_centered_cube_eval_eq {σ : Type*} [Finite σ]
    (P Q : MvPolynomial σ ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (hQ : ∀ i, Q.degreeOf i ≤ 1)
    (heval : ∀ z : σ → ℝ, (∀ i, z i = -1 ∨ z i = 1) → eval z P = eval z Q) :
    P = Q := by
  classical
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero_at_prod_finset (P - Q) (fun _ ↦ {-1, 1})
  · intro i
    have hd := (degreeOf_sub_le i P Q).trans (max_le (hP i) (hQ i))
    norm_num
    omega
  · intro z hz
    rw [map_sub, heval z (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz)]
    exact sub_self _

theorem centeredReduction_eq_of_cube_eval_eq {σ : Type*} [Finite σ]
    (P Q : MvPolynomial σ ℝ)
    (heval : ∀ z : σ → ℝ, (∀ i, z i = -1 ∨ z i = 1) → eval z P = eval z Q) :
    centeredReduction P = centeredReduction Q := by
  apply eq_of_centered_cube_eval_eq _ _ (centeredReduction_degreeOf_le P)
    (centeredReduction_degreeOf_le Q)
  intro z hz
  have hs : ∀ i, z i ^ 2 = 1 := by
    intro i
    rcases hz i with hi | hi <;> rw [hi] <;> norm_num
  rw [centeredReduction_eval_eq P z hs, centeredReduction_eval_eq Q z hs]
  exact heval z hz

theorem coeff_eq_of_top_squarefree_cube_eval_eq {σ : Type*} [Finite σ]
    (P Q : MvPolynomial σ ℝ) (e : σ →₀ ℕ)
    (he : ∀ i, e i ≤ 1)
    (hP : P.totalDegree ≤ e.sum (fun _ k ↦ k))
    (hQ : Q.totalDegree ≤ e.sum (fun _ k ↦ k))
    (heval : ∀ z : σ → ℝ, (∀ i, z i = -1 ∨ z i = 1) → eval z P = eval z Q) :
    P.coeff e = Q.coeff e := by
  have hp := coeff_collapse_centeredReduction id P e he hP
  have hq := coeff_collapse_centeredReduction id Q e he hQ
  simp only [rename_id, AlgHom.id_apply] at hp hq
  rw [← hp, ← hq, centeredReduction_eq_of_cube_eval_eq P Q heval]

end HeadComplexity.RoPECrossBlockCoefficients
