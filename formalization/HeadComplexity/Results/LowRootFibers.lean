import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- Along positive coordinate increments, reaching an affine level forces
at least one new root value for each active coordinate. The finite root
set contains all subset values; it need not be an arithmetic progression.
This is the combinatorial invariant behind the low-root-fiber audit,
not an assertion about universal head complexity. -/
theorem card_add_one_le_affineLevelInterval_card
    {ι : Type*} (S : Finset ι) (w : ι → ℝ) (a : ℝ)
    (Λ : Finset ℝ) (hpos : ∀ i ∈ S, 0 < w i)
    (hvalues : ∀ T : Finset ι, T ⊆ S → a + ∑ i ∈ T, w i ∈ Λ) :
    S.card + 1 ≤
      (Λ.filter fun r => a ≤ r ∧ r ≤ a + ∑ i ∈ S, w i).card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have ha : a ∈ Λ := by simpa using hvalues ∅ (by simp)
    have hmem : a ∈ Λ.filter (fun r => a ≤ r ∧ r ≤ a) := by
      simp [ha]
    simpa using Finset.one_le_card.mpr ⟨a, hmem⟩
  | @insert i S hi ih =>
    have hwi : 0 < w i := hpos i (by simp)
    have hSpos : ∀ j ∈ S, 0 < w j := by
      intro j hj
      exact hpos j (Finset.mem_insert_of_mem hj)
    have hSvalues : ∀ T : Finset ι, T ⊆ S → a + ∑ j ∈ T, w j ∈ Λ := by
      intro T hT
      exact hvalues T (hT.trans (Finset.subset_insert i S))
    have hold := ih hSpos hSvalues
    have hstrict : a + ∑ j ∈ S, w j < a + ∑ j ∈ insert i S, w j := by
      rw [Finset.sum_insert hi]
      linarith
    have hsum_nonneg : 0 ≤ ∑ j ∈ insert i S, w j := by
      exact Finset.sum_nonneg fun j hj => le_of_lt (hpos j hj)
    have htop : a + ∑ j ∈ insert i S, w j ∈ Λ :=
      hvalues (insert i S) (by rfl)
    have hsubset :
        (Λ.filter fun r => a ≤ r ∧ r ≤ a + ∑ j ∈ S, w j) ⊂
          (Λ.filter fun r => a ≤ r ∧ r ≤ a + ∑ j ∈ insert i S, w j) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro r hr
        rcases Finset.mem_filter.mp hr with ⟨hrΛ, har, hrS⟩
        exact Finset.mem_filter.mpr ⟨hrΛ, har, hrS.trans (le_of_lt hstrict)⟩
      · intro heq
        have hm : a + ∑ j ∈ insert i S, w j ∈
            Λ.filter (fun r => a ≤ r ∧ r ≤ a + ∑ j ∈ insert i S, w j) := by
          exact Finset.mem_filter.mpr ⟨htop, by linarith, le_rfl⟩
        rw [← heq] at hm
        have hh := (Finset.mem_filter.mp hm).2.2
        exact (not_le_of_gt hstrict) hh
    have hc := Finset.card_lt_card hsubset
    rw [Finset.card_insert_of_notMem hi]
    omega

/-- If the reached level lies among at most `q` root values above the
minimum, fewer than `q` nonconstant coordinates can be active. -/
theorem activeCoordinates_lt_prefixRootCount
    {ι : Type*} (S : Finset ι) (w : ι → ℝ) (a : ℝ)
    (Λ : Finset ℝ) (q : ℕ) (hpos : ∀ i ∈ S, 0 < w i)
    (hvalues : ∀ T : Finset ι, T ⊆ S → a + ∑ i ∈ T, w i ∈ Λ)
    (hprefix : (Λ.filter fun r => a ≤ r ∧ r ≤ a + ∑ i ∈ S, w i).card ≤ q) :
    S.card < q := by
  have h := card_add_one_le_affineLevelInterval_card S w a Λ hpos hvalues
  omega

end HeadComplexity
