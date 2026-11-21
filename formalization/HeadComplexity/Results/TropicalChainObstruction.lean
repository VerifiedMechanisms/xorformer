import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
A restriction of the dominant-power ansatz: constant numerators and
increasing denominators give capped minimum functions on input subsets.
If one Hamming layer is positive and the next is negative, every positive
head can win at most once on the first layer. This is not a lower bound
for general affine-ratio heads, which permit cancellation and affine
numerators.
-/

namespace HeadComplexity

def tropicalMinHead {ι : Type*} (c : ℝ) (w : ι → ℝ) (S : Finset ι) : ℝ :=
  S.fold min c w

theorem tropicalMinHead_insert {ι : Type*} [DecidableEq ι]
    (c : ℝ) (w : ι → ℝ) (S : Finset ι) (i : ι) :
    tropicalMinHead c w (insert i S) = min (w i) (tropicalMinHead c w S) := by
  exact Finset.fold_insert_idem

theorem le_tropicalMinHead_iff {ι : Type*} (c t : ℝ)
    (w : ι → ℝ) (S : Finset ι) :
    t ≤ tropicalMinHead c w S ↔ t ≤ c ∧ ∀ i ∈ S, t ≤ w i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [tropicalMinHead]
  | @insert i S hi ih =>
    simp only [tropicalMinHead_insert, le_min_iff, ih, Finset.mem_insert,
      forall_eq_or_imp]
    tauto

theorem tropicalMinHead_antitone {ι : Type*} (c : ℝ) (w : ι → ℝ) :
    Antitone (tropicalMinHead c w) := by
  intro S T hST
  rw [le_tropicalMinHead_iff]
  have h := (le_tropicalMinHead_iff c (tropicalMinHead c w T) w T).mp le_rfl
  exact ⟨h.1, fun i hi => h.2 i (hST hi)⟩

theorem winning_tropicalMinHead_strict_prefix {ι : Type*} [DecidableEq ι]
    (c : ℝ) (w : ι → ℝ) (Q : Finset ι → ℝ) (hQ : Antitone Q)
    (S : Finset ι) (hwin : Q S < tropicalMinHead c w S)
    (hflip : ∀ i ∉ S, tropicalMinHead c w (insert i S) ≤ Q (insert i S)) :
    ∀ i ∉ S, w i < tropicalMinHead c w S := by
  intro i hi
  by_contra h
  have hw := le_of_not_gt h
  have hflat : tropicalMinHead c w (insert i S) = tropicalMinHead c w S := by
    rw [tropicalMinHead_insert, min_eq_right hw]
  have hdecrease := hQ (Finset.subset_insert i S)
  have hh := hflip i hi
  rw [hflat] at hh
  linarith

theorem strict_prefix_sets_comparable {ι : Type*}
    (w : ι → ℝ) (S T : Finset ι) (s t : ℝ)
    (hSin : ∀ i ∈ S, s ≤ w i) (hSout : ∀ i ∉ S, w i < s)
    (hTin : ∀ i ∈ T, t ≤ w i) (hTout : ∀ i ∉ T, w i < t) :
    S ⊆ T ∨ T ⊆ S := by
  by_cases hst : s ≤ t
  · right
    intro i hi
    by_contra hn
    have h1 := hSout i hn
    have h2 := hTin i hi
    linarith
  · left
    intro i hi
    by_contra hn
    have h1 := hTout i hn
    have h2 := hSin i hi
    linarith

/-- Alternating adjacent Hamming layers require one distinct capped-minimum
head for every input in the positive layer, against any antitone opponent. -/
theorem choose_le_heads_of_tropical_layer_flip {n H k : ℕ}
    (c : Fin H → ℝ) (w : Fin H → Fin n → ℝ)
    (Q : Finset (Fin n) → ℝ) (hQ : Antitone Q)
    (hwin : ∀ S : Finset (Fin n), S.card = k →
      ∃ h, Q S < tropicalMinHead (c h) (w h) S)
    (hflip : ∀ T : Finset (Fin n), T.card = k + 1 →
      ∀ h, tropicalMinHead (c h) (w h) T ≤ Q T) :
    n.choose k ≤ H := by
  classical
  let layer := (Finset.univ : Finset (Fin n)).powersetCard k
  have hcard (S : layer) : S.val.card = k :=
    (Finset.mem_powersetCard.mp S.property).2
  choose win hwin' using fun S : layer => hwin S.val (hcard S)
  have hprefix (S : layer) :
      ∀ i ∉ S.val, w (win S) i < tropicalMinHead (c (win S)) (w (win S)) S.val := by
    apply winning_tropicalMinHead_strict_prefix _ _ Q hQ _ (hwin' S)
    intro i hi
    apply hflip
    simp [Finset.card_insert_of_notMem hi, hcard S]
  have hinjective : Function.Injective win := by
    intro S T heq
    have hc := strict_prefix_sets_comparable (w (win S)) S.val T.val
      (tropicalMinHead (c (win S)) (w (win S)) S.val)
      (tropicalMinHead (c (win S)) (w (win S)) T.val)
      ((le_tropicalMinHead_iff _ _ _ _).mp le_rfl).2 (hprefix S)
      ((le_tropicalMinHead_iff _ _ _ _).mp le_rfl).2
      (by simpa only [heq] using hprefix T)
    apply Subtype.ext
    rcases hc with hc | hc
    · exact Finset.eq_of_subset_of_card_le hc (by rw [hcard S, hcard T])
    · exact (Finset.eq_of_subset_of_card_le hc (by rw [hcard S, hcard T])).symm
  have h := Fintype.card_le_of_injective win hinjective
  simpa [layer] using h

end HeadComplexity
