import HeadComplexity.Results.RoPEDummyExtension
import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Restricting dummy inputs preserves vanilla head budgets

Fixing the final positions to zero absorbs their positive attention masses
and their numerator contributions into the query constants of each exact
fractional atom.
-/

namespace HeadComplexity

open scoped BigOperators

namespace FracAtom

noncomputable def restrictInputs {n k : ℕ} (a : FracAtom (n + k)) : FracAtom n where
  η := a.η + ∑ j : Fin k, a.ρ (j.natAdd n) * a.m (j.natAdd n)
  δ := a.δ
  γ := a.γ + ∑ j : Fin k, a.ρ (j.natAdd n)
  α := a.α
  ρ i := a.ρ (i.castAdd k)
  m i := a.m (i.castAdd k)
  hγ := add_pos_of_pos_of_nonneg a.hγ (Finset.sum_nonneg fun _ _ ↦ (a.hρ _).le)
  hα := a.hα
  hρ _ := a.hρ _

theorem restrictInputs_eval {n k : ℕ} (a : FracAtom (n + k)) (x : Fin n → Bool) :
    a.restrictInputs.eval x = a.eval (InputPadding.extend x) := by
  simp only [eval, wt, restrictInputs, Fin.sum_univ_add, InputPadding.extend,
    Fin.addCases_left, Fin.addCases_right, Bool.false_eq_true, if_false,
    mul_one, add_zero]
  congr 1 <;> ring

end FracAtom

namespace InputPadding

/-- Restrict arbitrary final positions to zero without increasing the number
of heads in the original shared-embedding vanilla architecture. -/
theorem vanilla_restrict {n k H : ℕ} {g : (Fin (n + k) → Bool) → Bool}
    (hg : computableWithSharedHeadsN (n + k) H g) :
    computableWithSharedHeadsN n H (fun x ↦ g (extend x)) := by
  obtain ⟨a, c, hc⟩ := (computableWithSharedHeadsN_iff_fracComputable H g).mp hg
  apply (computableWithSharedHeadsN_iff_fracComputable H _).mpr
  refine ⟨fun h ↦ (a h).restrictInputs, c, fun x ↦ ?_⟩
  simpa only [FracAtom.restrictInputs_eval] using hc (extend x)

theorem vanilla_of_classifier {n k H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithSharedHeadsN (n + k) H (classifier k f)) :
    computableWithSharedHeadsN n H f := by
  simpa only [classifier, project_extend] using vanilla_restrict hf

theorem not_vanilla_classifier {n k H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : ¬ computableWithSharedHeadsN n H f) :
    ¬ computableWithSharedHeadsN (n + k) H (classifier k f) :=
  fun h ↦ hf (vanilla_of_classifier h)

end InputPadding
end HeadComplexity
