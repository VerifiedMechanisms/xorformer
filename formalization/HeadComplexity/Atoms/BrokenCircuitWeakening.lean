import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card

set_option linter.style.header false

/-!
# Broken circuits under weakening of independence

This is a finite matroid comparison used in the written reciprocal-degree
audit. It is not a theorem about attention-head lower bounds or about the
number of positive real sign regions.
-/

namespace HeadComplexity.BrokenCircuitWeakening

open Set

variable {α : Type*} [LinearOrder α]

/-- A set contains no circuit with its least element removed. -/
def NoBrokenCircuit (M : Matroid α) (I : Set α) : Prop :=
  ∀ (C : Set α), M.IsCircuit C → ∀ e ∈ C,
    (∀ x ∈ C, e ≤ x) → ¬ C \ {e} ⊆ I

/-- Removing the least element respects containment, even when the least
elements of the two sets differ. -/
lemma erase_least_subset {C D : Set α} {c d : α}
    (hDC : D ⊆ C) (hdD : d ∈ D)
    (hc : ∀ x ∈ C, c ≤ x) (hd : ∀ x ∈ D, d ≤ x) :
    D \ {d} ⊆ C \ {c} := by
  intro x hx
  refine ⟨hDC hx.1, ?_⟩
  intro hxc
  have hxc' : x = c := hxc
  have hdc : d ≤ c := hxc' ▸ hd x hx.1
  have hcd : c ≤ d := hc d (hDC hdD)
  have hxd : x = d := hxc'.trans (le_antisymm hcd hdc)
  exact hx.2 hxd

/-- Every no-broken-circuit set for the more dependent matroid is one for
the less dependent matroid. Equal ranks are not needed for this inclusion. -/
theorem noBrokenCircuit_mono {M N : Matroid α}
    [Finite α]
    (hE : M.E = N.E)
    (hInd : ∀ I, N.Indep I → M.Indep I)
    {I : Set α} (hI : NoBrokenCircuit N I) : NoBrokenCircuit M I := by
  intro C hC c hcC hc hCI
  have hCE : C ⊆ N.E := hC.subset_ground.trans_eq hE
  have hDep : N.Dep C := (Matroid.not_indep_iff hCE).mp
    (fun h => hC.not_indep (hInd C h))
  obtain ⟨D, hDC, hD⟩ := hDep.exists_isCircuit_subset
  obtain ⟨d, hdD, hd⟩ := Set.exists_min_image D id (Set.toFinite D) hD.nonempty
  exact hI D hD d hdD hd ((erase_least_subset hDC hdD hc hd).trans hCI)

end HeadComplexity.BrokenCircuitWeakening
