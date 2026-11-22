import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Algebraic checks for the transverse stabilizer

These lemmas verify the nonsingular Hessian and explicit contraction budgets
used in `artifacts/beyond-counting-bound/stabilized-reciprocal-saddles.md`.
They do not formalize that entire analytic construction and do not assert an
attention-head lower bound.
-/

namespace HeadComplexity.StabilizedReciprocalSaddles

open scoped BigOperators

noncomputable def hessianAction {d : ℕ} (A : Fin d → ℝ) (N : ℝ) (v : Fin d → ℝ)
    (i : Fin d) : ℝ := 2 * (v i / A i - (∑ j, v j) / N)

theorem hessian_kernel_trivial {d : ℕ} (hd : 2 ≤ d)
    (A : Fin d → ℝ) (N : ℝ) (hA : ∀ i, A i ≠ 0) (hN : N ≠ 0)
    (hsum : ∑ i, A i = N + d - 1) (v : Fin d → ℝ)
    (hv : ∀ i, hessianAction A N v i = 0) : v = 0 := by
  classical
  let T : ℝ := ∑ i, v i
  have hi (i : Fin d) : v i = A i * T / N := by
    have h : v i / A i = T / N := by
      have := hv i
      dsimp [hessianAction] at this
      change 2 * (v i / A i - T / N) = 0 at this
      linarith
    have := (div_eq_iff (hA i)).mp h
    calc
      v i = T / N * A i := this
      _ = A i * T / N := by ring
  have hT : T = (∑ i, A i) * T / N := by
    calc
      T = ∑ i, A i * T / N := Finset.sum_congr rfl (fun i _ ↦ hi i)
      _ = (∑ i, A i) * T / N := by rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [hsum] at hT
  have hmul := (eq_div_iff hN).mp hT
  have hd' : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hz : ((d : ℝ) - 1) * T = 0 := by nlinarith [hmul]
  have hzero : T = 0 := (mul_eq_zero.mp hz).resolve_left (by linarith)
  funext i
  simpa [hzero] using hi i

theorem radius_budget (L K : ℝ) (hL : 0 < L) (hK : 0 < K) :
    0 < 1 / (4 * (1 + L * K)) ∧
      1 / (4 * (1 + L * K)) < 1 / 4 ∧
      L * K * (1 / (4 * (1 + L * K))) < 1 / 4 := by
  have hden : 0 < 4 * (1 + L * K) := by positivity
  have hprod : 0 < L * K := mul_pos hL hK
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_lt_iff₀ hden).2
    nlinarith
  · rw [mul_one_div]
    apply (div_lt_iff₀ hden).2
    nlinarith

theorem perturbation_budget (L A K1 δ ε : ℝ)
    (hL : 0 < L) (hA : 0 ≤ A) (hK1 : 0 ≤ K1) (hδ : 0 < δ)
    (hε1 : ε ≤ δ / (4 * L * (1 + A)))
    (hε2 : ε ≤ 1 / (8 * L * (1 + K1))) :
    L * ε * A < δ / 4 ∧ L * ε * K1 < 1 / 8 := by
  have hden1 : 0 < 4 * L * (1 + A) := by positivity
  have hden2 : 0 < 8 * L * (1 + K1) := by positivity
  have he1 := (le_div_iff₀ hden1).mp hε1
  have he2 := (le_div_iff₀ hden2).mp hε2
  constructor
  · by_cases he : ε ≤ 0
    · have : L * ε * A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hL.le he) hA
      linarith
    · have hepos : 0 < ε := lt_of_not_ge he
      have : 0 < L * ε := mul_pos hL hepos
      nlinarith [he1]
  · by_cases he : ε ≤ 0
    · have : L * ε * K1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hL.le he) hK1
      linarith
    · have hepos : 0 < ε := lt_of_not_ge he
      have : 0 < L * ε := mul_pos hL hepos
      nlinarith [he2]

theorem total_contraction_budget (L K K1 δ ε : ℝ)
    (hbase : L * K * δ < 1 / 4)
    (hperturb : L * ε * K1 < 1 / 8) :
    L * (K * δ + ε * K1) < 3 / 8 := by nlinarith

theorem cross_hessian_kernel_trivial {d : ℕ}
    (B : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hB : Function.Injective B) (v w : Fin d → ℝ)
    (h : (B w, B v) = (0, 0)) : (v, w) = (0, 0) := by
  have hw : B w = B 0 := by simpa using congrArg Prod.fst h
  have hv : B v = B 0 := by simpa using congrArg Prod.snd h
  exact Prod.ext (hB hv) (hB hw)

end HeadComplexity.StabilizedReciprocalSaddles
