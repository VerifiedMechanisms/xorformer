import Mathlib.Tactic

set_option linter.style.header false

/-!
# Dominant summands in a positive two-vector combination

These lemmas audit the free-amplitude sign-orbit obstruction. They do not
assert a universal attention bound or a restriction on general dictionaries.
-/

namespace HeadComplexity

theorem positive_dominant_summand {u v : ℝ}
    (h : 0 < u + v) (hdom : |v| ≤ |u|) : 0 < u := by
  by_contra hn
  have hu : u ≤ 0 := le_of_not_gt hn
  have hv := le_abs_self v
  rw [abs_of_nonpos hu] at hdom
  linarith

theorem positive_sign_multiplier_of_dominant_span {α β τ η a b : ℝ}
    (ha : 0 < a) (h : 0 < α * τ * a + β * η * b)
    (hdom : |β * η * b| ≤ |α * τ * a|) : 0 < α * τ := by
  have hp := positive_dominant_summand h hdom
  rcases mul_pos_iff.mp hp with hp | hp
  · exact hp.1
  · linarith [hp.2]

theorem binary_signs_eq_of_positive_common_multiplier {α τ η : ℝ}
    (hτ : τ = 1 ∨ τ = -1) (hη : η = 1 ∨ η = -1)
    (hp : 0 < α * τ) (hq : 0 < α * η) : τ = η := by
  rcases hτ with rfl | rfl <;> rcases hη with rfl | rfl <;>
    simp_all <;> linarith

theorem dominant_span_signs_constant {ι : Type*}
    (J : Finset ι) (hJ : J.Nonempty) (α β : ℝ)
    (τ η a b : ι → ℝ)
    (hτ : ∀ i ∈ J, τ i = 1 ∨ τ i = -1)
    (ha : ∀ i ∈ J, 0 < a i)
    (hpos : ∀ i ∈ J, 0 < α * τ i * a i + β * η i * b i)
    (hdom : ∀ i ∈ J, |β * η i * b i| ≤ |α * τ i * a i|) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i ∈ J, τ i = s := by
  obtain ⟨j, hj⟩ := hJ
  refine ⟨τ j, hτ j hj, ?_⟩
  intro i hi
  apply binary_signs_eq_of_positive_common_multiplier (hτ i hi) (hτ j hj)
  · exact positive_sign_multiplier_of_dominant_span (ha i hi) (hpos i hi) (hdom i hi)
  · exact positive_sign_multiplier_of_dominant_span (ha j hj) (hpos j hj) (hdom j hj)

end HeadComplexity
