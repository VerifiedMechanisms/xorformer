import HeadComplexity.Research.RelativeMarginQuantifiers
import HeadComplexity.Atoms.UniformApproximation

set_option linter.style.header false

/-!
A quantitative relative-margin compiler for bounded score terms that each admit
uniform approximation by one original admissible head. The error tolerance is
chosen explicitly; it does not assume a conditioning bound for the approximating
head parameters. All suprema are over the full Boolean cube.
-/

noncomputable section

namespace HeadComplexity.UniformMarginCompiler

open Finset RelativeMarginQuantifiers
open scoped BigOperators

variable {n H : ℕ}

/-- Uniform approximation controls the full-cube head norm. -/
theorem atomSup_le_of_uniform_error {phi : FracAtom n}
    {g : (Fin n → Bool) → ℝ} {M epsilon : ℝ}
    (hg : ∀ x, |g x| ≤ M) (he : ∀ x, |phi.eval x - g x| ≤ epsilon) :
    atomSup phi ≤ M + epsilon := by
  unfold atomSup
  apply Finset.sup'_le
  intro x _
  calc
    |phi.eval x| = |(phi.eval x - g x) + g x| := by congr 1; ring
    _ ≤ |phi.eval x - g x| + |g x| := abs_add_le _ _
    _ ≤ epsilon + M := add_le_add (he x) (hg x)
    _ = M + epsilon := add_comm _ _

/-- One head per term preserves a unit signed score with explicit relative margin.
The original terms can have arbitrary signs and can cancel. -/
theorem hasRelativeMargin_of_uniformlyOneAtomApproximable
    (g : Fin H → (Fin n → Bool) → ℝ)
    (hg : ∀ h, UniformlyOneAtomApproximable (g h))
    (M : Fin H → ℝ) (hM : ∀ h, 0 ≤ M h)
    (hbound : ∀ h x, |g h x| ≤ M h) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hmargin : ∀ x, 1 ≤ signedLabel f x * (c + ∑ h, g h x)) :
    HasRelativeMargin n H f (1 / (2 * (|c| + ∑ h, M h) + 1)) := by
  classical
  let epsilon : ℝ := 1 / (4 * ((H : ℝ) + 1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  choose phi hphi using fun h ↦ hg h epsilon hepsilon
  have herror_budget : (H : ℝ) * epsilon ≤ 1 / 4 := by
    dsimp [epsilon]
    have hden : 0 < (H : ℝ) + 1 := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    field_simp
    nlinarith
  have herr (x : Fin n → Bool) :
      |score phi c x - (c + ∑ h, g h x)| ≤ 1 / 4 := by
    calc
      _ = |∑ h, ((phi h).eval x - g h x)| := by
        congr 1
        simp only [score, Finset.sum_sub_distrib]
        ring
      _ ≤ ∑ h, |(phi h).eval x - g h x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h : Fin H, epsilon := sum_le_sum fun h _ ↦ (hphi h x).le
      _ = (H : ℝ) * epsilon := by simp
      _ ≤ 1 / 4 := herror_budget
  have hscore (x : Fin n → Bool) : 3 / 4 ≤ signedLabel f x * score phi c x := by
    have he := (abs_le.mp (herr x))
    have hm := hmargin x
    cases hfx : f x <;> simp [signedLabel, hfx] at hm ⊢ <;> linarith
  have hs : StrictlyRepresents f phi c := fun x ↦ lt_of_lt_of_le (by norm_num) (hscore x)
  have hamp : amplitude phi c ≤ |c| + ∑ h, M h + 1 / 4 := by
    calc
      _ ≤ |c| + ∑ h, (M h + epsilon) := by
        unfold amplitude
        exact add_le_add le_rfl (sum_le_sum fun h _ ↦
          atomSup_le_of_uniform_error (hbound h) (fun x ↦ (hphi h x).le))
      _ = |c| + ∑ h, M h + (H : ℝ) * epsilon := by
        rw [sum_add_distrib]
        simp
        ring
      _ ≤ |c| + ∑ h, M h + 1 / 4 := add_le_add le_rfl herror_budget
  have hB : 0 ≤ |c| + ∑ h, M h :=
    add_nonneg (abs_nonneg _) (sum_nonneg fun h _ ↦ hM h)
  have hden : 0 < 2 * (|c| + ∑ h, M h) + 1 := by linarith
  refine ⟨phi, c, hs, (le_relativeMargin_iff hs).mpr fun x ↦ ?_⟩
  have hhalf : 1 / (2 * (|c| + ∑ h, M h) + 1) * amplitude phi c ≤ 1 / 2 := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).2
    linarith
  exact hhalf.trans ((by norm_num : (1 : ℝ) / 2 ≤ 3 / 4).trans (hscore x))

#print axioms atomSup_le_of_uniform_error
#print axioms hasRelativeMargin_of_uniformlyOneAtomApproximable

end HeadComplexity.UniformMarginCompiler
