import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Algebraic ingredients for the affine-residue Boolean projection module.
The complete arbitrary-dimension module and graph statements are written proofs.
No change to the HeadComplexity model is made here. -/

namespace HeadComplexity.AffineProjectionModule

theorem transfer_identity {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : R) (e₀ eᵢ eⱼ : M) :
    (u ^ 2) • eⱼ - (u * v) • eⱼ =
      u • (u • eⱼ - v • eᵢ) - v • (u • (e₀ - eᵢ)) +
        u • (v • (e₀ - eⱼ)) := by
  module

theorem first_generator_boolean (t : ℝ) (x : Bool) :
    (t * (if x then 1 else 0)) * (1 - (if x then 1 else 0)) = 0 := by
  cases x <;> simp

theorem second_generator_boolean (t : ℝ) (x y : Bool) :
    (t * (if x then 1 else 0)) * (if y then 1 else 0) -
      (t * (if y then 1 else 0)) * (if x then 1 else 0) = 0 := by
  cases x <;> cases y <;> simp

theorem two_head_identity (D ε : ℝ) (x : Bool) :
    (1 - (if x then 1 else 0)) *
      (1 / (D + ε * (if x then 1 else 0)) - 1 / D) = 0 := by
  cases x <;> simp

theorem three_head_identity (D ε : ℝ) (x y : Bool) :
    (if y then 1 else 0) *
        (1 / (D + ε * (if x then 1 else 0)) - 1 / D) -
      (if x then 1 else 0) *
        (1 / (D + ε * (if y then 1 else 0)) - 1 / D) = 0 := by
  cases x <;> cases y <;> simp

theorem graph_edge_identity (g : ℝ → ℝ) (x y : Bool) :
    g (2 * (if x then 1 else 0) + (if y then 1 else 0)) -
      g ((if x then 1 else 0) + 2 * (if y then 1 else 0)) =
      (g 2 - g 1) * ((if x then 1 else 0) - (if y then 1 else 0)) := by
  cases x <;> cases y <;> norm_num

theorem cycle_identity {I : Type*} [Fintype I] (σ : Equiv.Perm I)
    (x : I → Bool) (g : ℝ → ℝ) :
    ∑ i, (g (2 * (if x i then 1 else 0) + (if x (σ i) then 1 else 0)) -
      g ((if x i then 1 else 0) + 2 * (if x (σ i) then 1 else 0))) = 0 := by
  simp_rw [graph_edge_identity]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have h : (∑ i, (if x (σ i) then (1 : ℝ) else 0)) =
      ∑ i, (if x i then (1 : ℝ) else 0) := by
    simpa using (Equiv.sum_comp σ (fun i : I => if x i then (1 : ℝ) else 0))
  rw [h, sub_self, mul_zero]

theorem square_edge_difference (z x y : ℝ) :
    (z + 2 * x + y) ^ 2 - (z + x + 2 * y) ^ 2 =
      2 * z * (x - y) + 3 * (x ^ 2 - y ^ 2) := by ring

theorem cube_edge_difference (z x y : ℝ) :
    (z + 2 * x + y) ^ 3 - (z + x + 2 * y) ^ 3 =
      3 * z ^ 2 * (x - y) + 9 * z * (x ^ 2 - y ^ 2) +
      7 * (x ^ 3 - y ^ 3) + 6 * x * y * (x - y) := by ring

theorem cube_pair_independent (a b : ℝ)
    (h₁ : 12 * a + 6 * b = 0) (h₂ : 6 * a + 12 * b = 0) :
    a = 0 ∧ b = 0 := by constructor <;> linarith

end HeadComplexity.AffineProjectionModule
