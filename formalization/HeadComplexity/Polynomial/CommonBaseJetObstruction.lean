import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

set_option linter.style.header false

/-!
# A limitation of regular common-denominator second-order jets

This module proves an exact algebraic moment obstruction. It does not prove
a lower bound for arbitrary four- or five-head vanilla representations.
The moment hypotheses describe one regular common-base finite-difference
ansatz; other parameter degenerations are outside the statement.
-/

namespace HeadComplexity.CommonBaseJetObstruction

open scoped BigOperators

abbrev Form (n : ℕ) := (Fin n → ℝ) →ₗ[ℝ] ℝ

/-- A split quadratic zero identity forces the two linear maps to have a
common nonzero kernel whenever the domain is larger than the number of pairs. -/
theorem exists_common_kernel_of_quadratic_zero {n k : ℕ} (hkn : k < n)
    (A B : Fin k → Form n) (hzero : ∀ x, ∑ i, A i x * B i x = 0) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ ∀ i, A i v = 0 ∧ B i v = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ) := LinearMap.pi (fun i ↦ A i + B i)
  have hdim : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    simpa using hkn
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff (LinearMap.ker L)).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  have hsum (i : Fin k) : A i v + B i v = 0 := congrFun hv i
  have hsquare : ∑ i, (A i v)^2 = 0 := by
    calc
      _ = -(∑ i, A i v * B i v) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have hi := hsum i
        linear_combination A i v * hi
      _ = 0 := by rw [hzero, neg_zero]
  refine ⟨v, hvne, fun i ↦ ?_⟩
  have hle : (A i v)^2 ≤ ∑ j, (A j v)^2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (A j v)) (Finset.mem_univ i)
  have ha : A i v = 0 := by rw [hsquare] at hle; nlinarith [sq_nonneg (A i v)]
  exact ⟨ha, by linarith [hsum i]⟩

/-- Removing the first pair after the two cancellation identities leaves only
`k` effective linear-coordinate pairs from `k+1` heads. -/
theorem exists_cubic_translation_direction {n k : ℕ} (hkn : k < n)
    (A B : Fin (k + 1) → Form n)
    (hfirst : ∀ x, ∑ i, A i x = 0)
    (hsecond : ∀ x, ∑ i, A i x * B i x = 0) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ ∀ x,
      (∑ i, A i (x + v) * (B i (x + v))^2) = ∑ i, A i x * (B i x) ^ 2 := by
  let A' (i : Fin k) : Form n := A i.succ
  let B' (i : Fin k) : Form n := B i.succ - B 0
  have hquadratic (x : Fin n → ℝ) : ∑ i, A' i x * B' i x = 0 := by
    have h₁ := hfirst x
    have h₂ := hsecond x
    rw [Fin.sum_univ_succ] at h₁ h₂
    dsimp [A', B']
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    linear_combination h₂ - B 0 x * h₁
  have hshift (x : Fin n → ℝ) :
      (∑ i, A' i x * (B' i x)^2) = ∑ i, A i x * (B i x) ^ 2 := by
    have h₁ := hfirst x
    have h₂ := hsecond x
    rw [Fin.sum_univ_succ] at h₁ h₂ ⊢
    dsimp [A', B']
    have he : (∑ i : Fin k, A i.succ x * (B i.succ x - B 0 x)^2) =
        (∑ i : Fin k, A i.succ x * (B i.succ x)^2) -
          2 * B 0 x * (∑ i : Fin k, A i.succ x * B i.succ x) +
          (B 0 x)^2 * (∑ i : Fin k, A i.succ x) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    linear_combination (B 0 x)^2 * h₁ - 2 * B 0 x * h₂
  obtain ⟨v, hvne, hv⟩ := exists_common_kernel_of_quadratic_zero hkn A' B' hquadratic
  refine ⟨v, hvne, fun x ↦ ?_⟩
  rw [← hshift, ← hshift]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_add, (hv i).1, (hv i).2, add_zero]

/-- The source cubic on the hyperplane `N₀ + c D₀ = 0`. -/
def endpointSection (c : ℝ) (x : Fin 5 → ℝ) : ℝ :=
  x 0 * (x 3 * x 2 + x 4 * x 1 - c * x 1 * x 2)

def endpointDirectional (c : ℝ) (v x : Fin 5 → ℝ) : ℝ :=
  v 0 * (x 3 * x 2 + x 4 * x 1 - c * x 1 * x 2) +
    x 0 * (v 3 * x 2 + x 3 * v 2 + v 4 * x 1 + x 4 * v 1 -
      c * (v 1 * x 2 + x 1 * v 2))

theorem endpoint_polarization (c : ℝ) (v x : Fin 5 → ℝ) :
    endpointSection c (x + v) - endpointSection c (x - v) -
      2 * endpointSection c v = 2 * endpointDirectional c v x := by
  simp only [endpointSection, endpointDirectional, Pi.add_apply, Pi.sub_apply]
  ring

/-- Every one of the five coordinates of the section is essential. -/
theorem endpoint_no_translation_direction (c : ℝ) (v : Fin 5 → ℝ)
    (h : ∀ x, endpointSection c (x + v) = endpointSection c x) : v = 0 := by
  have hv : endpointSection c v = 0 := by
    simpa [endpointSection] using h 0
  have hd (x : Fin 5 → ℝ) : endpointDirectional c v x = 0 := by
    have hp := h x
    have hm := h (x - v)
    have he : x - v + v = x := by abel
    rw [he] at hm
    have hi := endpoint_polarization c v x
    rw [hp, ← hm, hv] at hi
    linarith
  have h0 := hd ![0, 0, 1, 1, 0]
  have h2 := hd ![1, 0, 0, 1, 0]
  have h1 := hd ![1, 0, 0, 0, 1]
  have h3 := hd ![1, 0, 1, 0, 0]
  have h4 := hd ![1, 1, 0, 0, 0]
  norm_num [endpointDirectional, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3 h4
  rw [h1, mul_zero, sub_zero] at h3
  rw [h2, mul_zero, sub_zero] at h4
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- At most five regular common-base second-order moments cannot produce the
five-coordinate source section. This is an ansatz obstruction only. -/
theorem no_endpoint_moments_of_small_head_count {k : ℕ} (hk : k < 5) (c : ℝ)
    (A B : Fin (k + 1) → Form 5)
    (hfirst : ∀ x, ∑ i, A i x = 0)
    (hsecond : ∀ x, ∑ i, A i x * B i x = 0)
    (hsource : ∀ x, ∑ i, A i x * (B i x) ^ 2 = endpointSection c x) : False := by
  obtain ⟨v, hv, htrans⟩ := exists_cubic_translation_direction
    (n := 5) (k := k) hk A B hfirst hsecond
  apply hv
  apply endpoint_no_translation_direction c v
  intro x
  rw [← hsource, ← hsource]
  exact htrans x

/-- The five-head specialization of the exact moment obstruction. -/
theorem no_five_head_endpoint_moments (c : ℝ)
    (A B : Fin 5 → Form 5)
    (hfirst : ∀ x, ∑ i, A i x = 0)
    (hsecond : ∀ x, ∑ i, A i x * B i x = 0)
    (hsource : ∀ x, ∑ i, A i x * (B i x) ^ 2 = endpointSection c x) : False :=
  no_endpoint_moments_of_small_head_count (by norm_num : 4 < 5) c A B
    hfirst hsecond hsource

end HeadComplexity.CommonBaseJetObstruction
