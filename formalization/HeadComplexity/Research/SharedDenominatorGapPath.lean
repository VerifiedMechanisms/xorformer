import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.SharedDenominatorGapPath
open Finset
open scoped BigOperators Topology

/-- The scalar value of the affine coefficient perturbation. -/
def transport (A B u D t : ℝ) : ℝ := (A+t*u*D)/(B+t*D)

/-- The exact nonlinear gap-product update at a common denominator. -/
theorem transport_identity (A₁ A₂ B u₁ u₂ t : ℝ)
    (hB : B ≠ 0) (hnew : B+t*(u₂*B-A₂) ≠ 0) :
    transport A₁ B u₁ (u₂*B-A₂) t =
      A₁/B+t*(u₁-A₁/B)*(u₂-A₂/B)/(1+t*(u₂-A₂/B)) := by
  have hd : 1+t*(u₂-A₂/B) ≠ 0 := by
    intro hz
    apply hnew
    have hh : B*(1+t*(u₂-A₂/B)) = B+t*(u₂*B-A₂) := by
      field_simp
    rw [hz, mul_zero] at hh
    exact hh.symm
  unfold transport
  field_simp
  ring

/-- A nonnegative step contracts the entire value interval toward its top. -/
theorem transport_interval (A B u D t l : ℝ) (hB : 0 < B)
    (hD : 0 ≤ D) (ht : 0 ≤ t) (hlo : l ≤ A/B) (hhi : A/B ≤ u) :
    l ≤ transport A B u D t ∧ transport A B u D t ≤ u := by
  have hnew : 0 < B+t*D := add_pos_of_pos_of_nonneg hB (mul_nonneg ht hD)
  have hlo' : l*B ≤ A := (le_div_iff₀ hB).mp hlo
  have hhi' : A ≤ u*B := (div_le_iff₀ hB).mp hhi
  have hlu : l ≤ u := hlo.trans hhi
  have hp : 0 ≤ t*D*(u-l) := mul_nonneg (mul_nonneg ht hD) (sub_nonneg.mpr hlu)
  constructor
  · unfold transport
    apply (le_div_iff₀ hnew).mpr
    nlinarith
  · unfold transport
    apply (div_le_iff₀ hnew).mpr
    nlinarith

/-- Every attained top value stays exactly fixed, for either step sign. -/
theorem transport_at_max (A B u D t : ℝ) (hB : B ≠ 0)
    (hnew : B+t*D ≠ 0) (hmax : A/B = u) : transport A B u D t = u := by
  have hA : A = u*B := (div_eq_iff hB).mp hmax
  unfold transport
  rw [hA]
  apply (div_eq_iff hnew).mpr
  ring

/-- The entire finite-domain supremum norm cannot increase in a
nonnegative step when the designated top value is attained. -/
theorem transport_norm_le {X : Type*} [Fintype X]
    (A B D : X → ℝ) (u t : ℝ) (p : X)
    (hB : ∀ x, 0 < B x) (hD : ∀ x, 0 ≤ D x) (ht : 0 ≤ t)
    (hhi : ∀ x, A x/B x ≤ u) (hmax : A p/B p = u) :
    ‖fun x => transport (A x) (B x) u (D x) t‖ ≤ ‖fun x => A x/B x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro x
  have hx := norm_le_pi_norm (fun x => A x/B x) x
  have hp := norm_le_pi_norm (fun x => A x/B x) p
  rw [Real.norm_eq_abs] at hx hp
  rw [hmax] at hp
  have hlo := (abs_le.mp hx).1
  have hu := (abs_le.mp hp).2
  obtain ⟨hlo', hhi'⟩ := transport_interval (A x) (B x) u (D x) t
    (-‖fun x => A x/B x‖) (hB x) (hD x) ht hlo (hhi x)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlo', hhi'.trans hu⟩

/-- The path is an actual admissible original-model head whenever its
positive affine denominator coefficients stay positive. No relaxed head is
introduced. The coefficient inequalities hold for all sufficiently small
signed steps at a strictly positive starting denominator. -/
theorem exists_admissible_path {n : ℕ}
    (a₁₀ a₂₀ b₀ u₁ u₂ t : ℝ) (a₁ a₂ b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i)
    (hnew₀ : 0 < b₀+t*(u₂*b₀-a₂₀))
    (hnew : ∀ i, 0 < b i+t*(u₂*b i-a₂ i)) :
    ∃ φ : FracAtom n, ∀ x,
      φ.eval x = affineValue a₁₀ a₁ x / affineValue b₀ b x +
        t*(u₁-affineValue a₁₀ a₁ x / affineValue b₀ b x)*
          (u₂-affineValue a₂₀ a₂ x / affineValue b₀ b x)/
          (1+t*(u₂-affineValue a₂₀ a₂ x / affineValue b₀ b x)) := by
  let φ := FracAtom.ofPositiveAffineRatio
    (a₁₀+t*u₁*(u₂*b₀-a₂₀)) (fun i => a₁ i+t*u₁*(u₂*b i-a₂ i))
    (b₀+t*(u₂*b₀-a₂₀)) (fun i => b i+t*(u₂*b i-a₂ i)) hnew₀ hnew
  refine ⟨φ, fun x => ?_⟩
  have hgap : affineValue (u₂*b₀-a₂₀) (fun i => u₂*b i-a₂ i) x =
      u₂*affineValue b₀ b x-affineValue a₂₀ a₂ x := by
    simp only [affineValue, sub_mul, mul_assoc, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    ring
  have hnum : affineValue (a₁₀+t*u₁*(u₂*b₀-a₂₀))
      (fun i => a₁ i+t*u₁*(u₂*b i-a₂ i)) x =
      affineValue a₁₀ a₁ x+t*u₁*(u₂*affineValue b₀ b x-affineValue a₂₀ a₂ x) := by
    rw [affineValue_add, affineValue_smul, hgap]
  have hden : affineValue (b₀+t*(u₂*b₀-a₂₀))
      (fun i => b i+t*(u₂*b i-a₂ i)) x =
      affineValue b₀ b x+t*(u₂*affineValue b₀ b x-affineValue a₂₀ a₂ x) := by
    rw [affineValue_add, affineValue_smul, hgap]
  have hB := affineValue_pos b₀ b hb₀ hb x
  have hN := affineValue_pos _ _ hnew₀ hnew x
  rw [hden] at hN
  change (FracAtom.ofPositiveAffineRatio _ _ _ _ hnew₀ hnew).eval x = _
  rw [FracAtom.ofPositiveAffineRatio_eval, hnum, hden]
  exact transport_identity _ _ _ _ _ _ hB.ne' hN.ne'

/-- Every strictly positive starting denominator admits a genuine signed
neighborhood of admissible one-head gap-product updates. -/
theorem eventually_admissible_path {n : ℕ}
    (a₁₀ a₂₀ b₀ u₁ u₂ : ℝ) (a₁ a₂ b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) :
    ∀ᶠ t : ℝ in 𝓝 0, ∃ φ : FracAtom n, ∀ x,
      φ.eval x = affineValue a₁₀ a₁ x / affineValue b₀ b x +
        t*(u₁-affineValue a₁₀ a₁ x / affineValue b₀ b x)*
          (u₂-affineValue a₂₀ a₂ x / affineValue b₀ b x)/
          (1+t*(u₂-affineValue a₂₀ a₂ x / affineValue b₀ b x)) := by
  have hc : Continuous (fun t : ℝ => b₀+t*(u₂*b₀-a₂₀)) := by fun_prop
  have hs (i : Fin n) : Continuous (fun t : ℝ => b i+t*(u₂*b i-a₂ i)) := by
    fun_prop
  have h₀ : ∀ᶠ t : ℝ in 𝓝 0, 0 < b₀+t*(u₂*b₀-a₂₀) :=
    (hc.tendsto 0).eventually (eventually_gt_nhds (by simpa using hb₀))
  have hi (i : Fin n) : ∀ᶠ t : ℝ in 𝓝 0, 0 < b i+t*(u₂*b i-a₂ i) :=
    ((hs i).tendsto 0).eventually (eventually_gt_nhds (by simpa using hb i))
  filter_upwards [h₀, Filter.eventually_all.mpr hi] with t ht₀ ht
  exact exists_admissible_path a₁₀ a₂₀ b₀ u₁ u₂ t a₁ a₂ b hb₀ hb ht₀ ht

end HeadComplexity.SharedDenominatorGapPath
