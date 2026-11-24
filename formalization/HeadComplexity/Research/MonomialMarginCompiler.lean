import HeadComplexity.Research.LowDegreeMarginRepair
import HeadComplexity.Research.UniformMarginCompiler
import HeadComplexity.Research.MarginInvariance

set_option linter.style.header false

/-!
An unconditional quantitative original-model margin repair for low threshold
degree. The comparison width is the complete low-degree monomial dimension;
it is not asserted to be a constant multiple of an arbitrary original width.
-/

noncomputable section

namespace HeadComplexity.MonomialMarginCompiler

open Finset RelativeMarginQuantifiers LowDegreeMarginRepair UniformMarginCompiler
open scoped BigOperators

/-- A low-degree threshold table has an original-model representation with one
head per low-degree monomial and an explicit full-cube relative margin. -/
theorem hasRelativeMargin_of_thresholdDegree (n d : ℕ)
    (f : (Fin n → Bool) → Bool) (hf : ThresholdDegLE f d) :
    HasRelativeMargin n (monomialCount n d) f
      (1 / (2 * (monomialCount n d : ℝ) * ((monomialCount n d).factorial : ℝ) + 1)) := by
  classical
  obtain ⟨a, ha, habound⟩ := exists_integer_monomial_separator n d f hf
  let g : Fin (monomialCount n d) → (Fin n → Bool) → ℝ := fun j x ↦
    (a j : ℝ) * squarefreeMonomial (monomialAt n d j) x
  have hg : ∀ j, UniformlyOneAtomApproximable (g j) := by
    intro j epsilon hepsilon
    exact exists_fracAtom_approx_signedMonomial (monomialAt n d j) (a j) epsilon hepsilon
  have hbound : ∀ j x, |g j x| ≤ ((monomialCount n d).factorial : ℝ) := by
    intro j x
    dsimp [g]
    rw [abs_mul]
    calc
      |(a j : ℝ)| * |squarefreeMonomial (monomialAt n d j) x| ≤ |(a j : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (abs_monomial_le_one _ _) (abs_nonneg _)
      _ ≤ ((monomialCount n d).factorial : ℝ) := by simpa using habound j
  have hm : ∀ x, 1 ≤ signedLabel f x * ((0 : ℝ) + ∑ j, g j x) := by
    intro x
    simpa only [zero_add] using ha x
  have h := hasRelativeMargin_of_uniformlyOneAtomApproximable g hg
    (fun _ ↦ ((monomialCount n d).factorial : ℝ)) (fun _ ↦ Nat.cast_nonneg _)
    hbound 0 f hm
  simpa only [abs_zero, zero_add, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc] using h

/-- The repair can be padded to any larger comparison width. -/
theorem hasRelativeMargin_of_thresholdDegree_at_width (n d K : ℕ)
    (f : (Fin n → Bool) → Bool) (hf : ThresholdDegLE f d)
    (hK : monomialCount n d ≤ K) :
    HasRelativeMargin n K f
      (1 / (2 * (monomialCount n d : ℝ) * ((monomialCount n d).factorial : ℝ) + 1)) :=
  hasRelativeMargin_mono_width hK (hasRelativeMargin_of_thresholdDegree n d f hf)

/-- Clearing an original width-H representation gives threshold degree at most H.
The resulting repair width is the full degree-H monomial dimension. -/
theorem hasRelativeMargin_of_computable (n H : ℕ)
    (f : (Fin n → Bool) → Bool) (hf : computableWithHeadsN n H f) :
    HasRelativeMargin n (monomialCount n H) f
      (1 / (2 * (monomialCount n H : ℝ) * ((monomialCount n H).factorial : ℝ) + 1)) :=
  hasRelativeMargin_of_thresholdDegree n H f (signReprDegLe_of_computableWithHeadsN hf)

/-- The universal bad-margin class contains no table of a degree that fits the
explicit monomial repair budget. This is about all alternative representations. -/
theorem not_mem_allRepresentationsLowMargin_of_thresholdDegree
    (n H K d : ℕ) (f : (Fin n → Bool) → Bool) (gamma : ℝ)
    (hf : ThresholdDegLE f d) (hK : monomialCount n d ≤ K)
    (hgamma : gamma ≤
      1 / (2 * (monomialCount n d : ℝ) * ((monomialCount n d).factorial : ℝ) + 1)) :
    f ∉ allRepresentationsLowMargin n H K gamma := by
  intro hbad
  exact hbad.2 (hasRelativeMargin_mono hgamma
    (hasRelativeMargin_of_thresholdDegree_at_width n d K f hf hK))

#print axioms hasRelativeMargin_of_computable
#print axioms not_mem_allRepresentationsLowMargin_of_thresholdDegree

#print axioms hasRelativeMargin_of_thresholdDegree
#print axioms hasRelativeMargin_of_thresholdDegree_at_width

end HeadComplexity.MonomialMarginCompiler
