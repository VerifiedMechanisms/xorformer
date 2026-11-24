import HeadComplexity.Results.ExteriorCauchyInterpolation

set_option linter.style.header false

/-!
Two arbitrary query-value vectors can share the absolute residues of two
exterior Cauchy blocks. Each block has q poles for q queries. This is a
root-only interpolation statement, not a recursive decoder or an asymptotic
HeadComplexity bound.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators
open Polynomial

/-- Square Cauchy interpolation with unrestricted signed residues. -/
theorem exists_exterior_cauchy_interpolation {q : ℕ}
    (p t y : Fin q → ℝ)
    (hp : Function.Injective p) (ht : Function.Injective t)
    (hpt : ∀ h j, p h < t j) :
    ∃ c : Fin q → ℝ, ∀ j, (∑ h, c h / (t j - p h)) = y j := by
  let N : ℝ[X] := Lagrange.interpolate Finset.univ t
    (fun j ↦ y j * (Lagrange.nodal Finset.univ p).eval (t j))
  have hN : N.degree < (q : WithBot ℕ) := by
    simpa [N] using Lagrange.degree_interpolate_lt
      (s := Finset.univ) (v := t)
      (fun j ↦ y j * (Lagrange.nodal Finset.univ p).eval (t j)) ht.injOn
  refine ⟨fun h ↦ N.eval (p h) * Lagrange.nodalWeight Finset.univ p h, ?_⟩
  intro j
  rw [exterior_cauchy_barycentric p hp N hN (t j)
    (fun h ↦ ne_of_gt (hpt h j))]
  have hNeval : N.eval (t j) = y j * (Lagrange.nodal Finset.univ p).eval (t j) :=
    Lagrange.eval_interpolate_at_node _ ht.injOn (Finset.mem_univ j)
  rw [hNeval]
  exact mul_div_cancel_right₀ _ (Lagrange.eval_nodal_not_at_node
    (fun h _ ↦ ne_of_gt (hpt h j)))

/-- Two arbitrary value vectors use the same residues on the first block,
and opposite residues on the second. Thus their absolute residue pools
agree, with a total of 2q pole slots. -/
theorem exists_shared_exterior_cauchy_pair {q : ℕ}
    (p₁ p₂ t y₁ y₂ : Fin q → ℝ)
    (hp₁ : Function.Injective p₁) (hp₂ : Function.Injective p₂)
    (ht : Function.Injective t)
    (hpt₁ : ∀ h j, p₁ h < t j) (hpt₂ : ∀ h j, p₂ h < t j) :
    ∃ c₁ c₂ : Fin q → ℝ, ∀ j,
      ((∑ h, c₁ h / (t j - p₁ h)) +
        (∑ h, c₂ h / (t j - p₂ h)) = y₁ j) ∧
      ((∑ h, c₁ h / (t j - p₁ h)) +
        (∑ h, (-c₂ h) / (t j - p₂ h)) = y₂ j) := by
  obtain ⟨c₁, hc₁⟩ := exists_exterior_cauchy_interpolation
    p₁ t (fun j ↦ (y₁ j + y₂ j) / 2) hp₁ ht hpt₁
  obtain ⟨c₂, hc₂⟩ := exists_exterior_cauchy_interpolation
    p₂ t (fun j ↦ (y₁ j - y₂ j) / 2) hp₂ ht hpt₂
  refine ⟨c₁, c₂, ?_⟩
  intro j
  constructor
  · rw [hc₁ j, hc₂ j]
    ring
  · simp_rw [neg_div, Finset.sum_neg_distrib]
    rw [hc₁ j, hc₂ j]
    ring

end HeadComplexity.AxisZeroGluing
