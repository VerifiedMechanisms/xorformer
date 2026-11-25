import HeadComplexity.Polynomial.BlockCoefficientDerivatives
import Mathlib.Topology.Algebra.MvPolynomial

set_option linter.style.header false

/-!
# Moving block contractions preserve top-coefficient limits

Both the polynomial and its contraction directions may vary. Only the top
squarefree coefficients need converge; no bound on factor parameters is used.
-/

noncomputable section

namespace HeadComplexity.BlockCoefficientLimit

open MvPolynomial RoPEGeneralPolarization BlockCoefficientProjection
open BlockCoefficientDerivatives
open scoped BigOperators Topology
open Filter

variable {X σ : Type*} [TopologicalSpace X]

theorem continuous_coeff_mul (P Q : X → MvPolynomial σ ℝ)
    (hP : ∀ d, Continuous (fun x ↦ coeff d (P x)))
    (hQ : ∀ d, Continuous (fun x ↦ coeff d (Q x))) (d : σ →₀ ℕ) :
    Continuous (fun x ↦ coeff d (P x * Q x)) := by
  classical
  simp only [coeff_mul]
  fun_prop

theorem continuous_coeff_pow (P : X → MvPolynomial σ ℝ)
    (hP : ∀ d, Continuous (fun x ↦ coeff d (P x))) (k : ℕ) (d : σ →₀ ℕ) :
    Continuous (fun x ↦ coeff d (P x ^ k)) := by
  induction k generalizing d with
  | zero => simp only [pow_zero]; exact continuous_const
  | succ k ih =>
    simp only [pow_succ]
    exact continuous_coeff_mul (fun x ↦ P x ^ k) P (fun e ↦ ih e) hP d

theorem continuous_coeff_prod {ι : Type*} (s : Finset ι)
    (P : ι → X → MvPolynomial σ ℝ)
    (hP : ∀ i ∈ s, ∀ d, Continuous (fun x ↦ coeff d (P i x))) (d : σ →₀ ℕ) :
    Continuous (fun x ↦ coeff d (∏ i ∈ s, P i x)) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simp only [Finset.prod_empty]; exact continuous_const
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact continuous_coeff_mul (P i) (fun x ↦ ∏ j ∈ s, P j x)
      (hP i (Finset.mem_insert_self _ _))
      (fun e ↦ ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)) e) d

theorem continuous_weight_coeff (m : ℕ) (p : Block m × σ) (d : σ →₀ ℕ) :
    Continuous (fun z : (σ → ℝ) × (σ → ℝ) ↦
      coeff d (contractionWeight m z.1 z.2 p)) := by
  classical
  rcases p with ⟨b, i⟩
  rcases b with _ | b
  · simp only [contractionWeight, coeff_C]
    split_ifs <;> fun_prop
  · rcases b with _ | b
    · simp only [contractionWeight, coeff_C]
      split_ifs <;> fun_prop
    · exact continuous_const

theorem continuous_weight_product_coeff (m : ℕ) (e : Block m × σ →₀ ℕ)
    (d : σ →₀ ℕ) :
    Continuous (fun z : (σ → ℝ) × (σ → ℝ) ↦
      coeff d (e.prod (fun p k ↦ contractionWeight m z.1 z.2 p ^ k))) := by
  classical
  apply continuous_coeff_prod e.support
  intro p hp c
  exact continuous_coeff_pow
    (fun z : (σ → ℝ) × (σ → ℝ) ↦ contractionWeight m z.1 z.2 p)
    (continuous_weight_coeff m p) (e p) c

set_option maxHeartbeats 2000000 in
-- Elaborating the nested finite coefficient sum requires additional reduction steps.
/-- Exact coefficient convergence of projected contractions, including moving
first and second directions. This is the analytic interface used by the compact
kernel-frame obstruction. -/
theorem tendsto_contractDiagonal_coeff [Finite σ] (m : ℕ)
    (P : ℕ → BlockPoly m σ) (Q : BlockPoly m σ)
    (hP : ∀ e : Block m × σ →₀ ℕ, (∀ p, e p ≤ 1) →
      e.sum (fun _ k ↦ k) = m + 2 →
      Tendsto (fun k ↦ coeff e (P k)) atTop (𝓝 (coeff e Q)))
    (v w : ℕ → σ → ℝ) (v₀ w₀ : σ → ℝ)
    (hv : Tendsto v atTop (𝓝 v₀)) (hw : Tendsto w atTop (𝓝 w₀))
    (d : σ →₀ ℕ) :
    Tendsto (fun k ↦ coeff d (contractDiagonal m (P k) (v k) (w k))) atTop
      (𝓝 (coeff d (contractDiagonal m Q v₀ w₀))) := by
  classical
  letI := Fintype.ofFinite σ
  simp_rw [← projection_eq_contractDiagonal, projection_eq_sum, coeff_sum]
  apply tendsto_finsetSum
  intro e he
  change Tendsto (fun k ↦ coeff d
    (C (coeff e.val (P k)) * e.val.prod
      (fun p j ↦ contractionWeight m (v k) (w k) p ^ j))) atTop
    (𝓝 (coeff d (C (coeff e.val Q) * e.val.prod
      (fun p j ↦ contractionWeight m v₀ w₀ p ^ j))))
  simp only [coeff_C_mul]
  apply Tendsto.mul
  · apply hP e.val (exponent_le_one_of_block_degree_one e.val e.property)
    have hdeg := degree_of_block_degree_one e.val e.property
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc] using hdeg
  · exact (continuous_weight_product_coeff m e.val d).continuousAt.tendsto.comp
      (hv.prodMk_nhds hw)

end HeadComplexity.BlockCoefficientLimit
