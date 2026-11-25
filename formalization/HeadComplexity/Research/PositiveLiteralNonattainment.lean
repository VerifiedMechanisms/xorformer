import HeadComplexity.Research.LiteralMarginNonattainment
import HeadComplexity.Research.PositiveNormalizationSharpness

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.PositiveLiteralNonattainment
open Finset RelativeMarginQuantifiers LiteralMarginNonattainmentWitness
open scoped BigOperators

/-- The canonical positive literal has strict margin below one third in every
finite width when the input dimension is at least two. No norm or minimum-zero
assumption is required. -/
theorem relativeMargin_lt_third (n H : ℕ) (φ : Fin H → FracAtom (n+2))
    (hn : ∀ h x, 0 ≤ (φ h).eval x)
    (hs : StrictlyRepresents (literal (n+1)) φ (-1)) :
    relativeMargin (literal (n+1)) φ (-1) < 1/3 := by
  by_contra hnot
  have hm : (1:ℝ)/3 ≤ relativeMargin (literal (n+1)) φ (-1) := le_of_not_gt hnot
  have hg := (le_relativeMargin_iff hs).mp hm
  have ha : amplitude φ (-1) = 1+∑ h, atomSup (φ h) := by simp [amplitude]
  have hz := hg (fun _ => false)
  have ht := hg (fun _ => true)
  have hzn : 0 ≤ ∑ h, (φ h).eval (fun _ => false) := sum_nonneg fun h _ => hn h _
  have htu : (∑ h, (φ h).eval (fun _ => true)) ≤ ∑ h, atomSup (φ h) :=
    sum_le_sum fun h _ => (le_abs_self _).trans (abs_eval_le_atomSup (φ h) _)
  have hzs : signedLabel (literal (n+1)) (fun _ => false) = -1 := rfl
  have hts : signedLabel (literal (n+1)) (fun _ => true) = 1 := rfl
  rw [ha,hzs] at hz
  rw [ha,hts] at ht
  change (1:ℝ)/3 * (1+∑ h, atomSup (φ h)) ≤ -1 * (-1+∑ h, (φ h).eval (fun _ => false)) at hz
  change (1:ℝ)/3 * (1+∑ h, atomSup (φ h)) ≤ 1 * (-1+∑ h, (φ h).eval (fun _ => true)) at ht
  have hsum : (∑ h, atomSup (φ h)) = 2 := by linarith
  have hgap (x : Fin (n+2) → Bool) : 1 ≤ signedLabel (literal (n+1)) x * score φ (-1) x := by
    have hx := hg x
    rw [ha,hsum] at hx
    norm_num at hx
    exact hx
  let ψ : Fin H → FracAtom (n+2) := fun h => (φ h).translate (-(atomSup (φ h)/2))
  have hnorm (h : Fin H) : atomSup (ψ h) ≤ atomSup (φ h)/2 := by
    apply Finset.sup'_le
    intro x _
    change |(ψ h).eval x| ≤ atomSup (φ h)/2
    dsimp [ψ]
    rw [FracAtom.translate_eval]
    apply abs_le.mpr
    have hh := hn h x
    have hu := (le_abs_self ((φ h).eval x)).trans (abs_eval_le_atomSup (φ h) x)
    constructor <;> linarith
  have hamp : amplitude ψ 0 ≤ 1 := by
    calc
      amplitude ψ 0 = ∑ h, atomSup (ψ h) := by simp [amplitude]
      _ ≤ ∑ h, atomSup (φ h)/2 := sum_le_sum fun h _ => hnorm h
      _ = 1 := by rw [← Finset.sum_div,hsum]; norm_num
  have hscore (x : Fin (n+2) → Bool) : score ψ 0 x = score φ (-1) x := by
    simp only [score,ψ,FracAtom.translate_eval,zero_add,Finset.sum_add_distrib,Finset.sum_neg_distrib,← Finset.sum_div,hsum]
    ring
  have hs' : StrictlyRepresents (literal (n+1)) ψ 0 := by
    intro x
    rw [hscore]
    exact hs x
  apply LiteralMarginNonattainment.not_hasRelativeMargin_one n H
  refine ⟨ψ,0,hs',(le_relativeMargin_iff hs').mpr ?_⟩
  intro x
  rw [one_mul,hscore]
  exact hamp.trans (hgap x)

/-- The endpoint excluded above is also excluded in the exact same-width
positive normal form used for the capacity reduction. -/
theorem not_hasNormalizedMargin_third (n H : ℕ) :
    ¬ SameWidthPositiveNormalization.HasNormalizedMargin (n+2) H (literal (n+1)) (1/3) := by
  rintro ⟨φ,hn,_hz,_hA,hs,hγ⟩
  exact (not_le_of_gt (relativeMargin_lt_third n H φ hn hs)) hγ

end HeadComplexity.PositiveLiteralNonattainment
