import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.style.header false
set_option maxHeartbeats 2000000

/-! A restriction obstruction for sums of real-valued coordinate priority lists.
This is an auxiliary result about a proposed replacement model, not a lower
bound for attention heads. -/
namespace HeadComplexity.PriorityRestriction

variable {ι : Type*} [DecidableEq ι]

structure Subcube (ι : Type*) where
  fixed : Finset ι
  values : ι → Bool

def Subcube.Matches (s : Subcube ι) (x : ι → Bool) : Prop :=
  ∀ i ∈ s.fixed, x i = s.values i

def Subcube.Extends (s t : Subcube ι) : Prop :=
  ∀ x, t.Matches x → s.Matches x

omit [DecidableEq ι] in
theorem Subcube.extends_refl (s : Subcube ι) : s.Extends s := fun _ h ↦ h

omit [DecidableEq ι] in
theorem Subcube.extends_trans {s t u : Subcube ι}
    (hst : s.Extends t) (htu : t.Extends u) : s.Extends u :=
  fun x h ↦ hst x (htu x h)

structure Literal (ι : Type*) where
  coordinate : ι
  value : Bool
  output : ℝ

def evaluate (default : ℝ) : List (Literal ι) → (ι → Bool) → ℝ
  | [], _ => default
  | h :: t, x => if x h.coordinate = h.value then h.output else evaluate default t x

/-- One extra coordinate makes any coordinate priority list constant. -/
theorem freeze_one (default : ℝ) (list : List (Literal ι)) (s : Subcube ι) :
    ∃ t : Subcube ι, s.Extends t ∧ t.fixed.card ≤ s.fixed.card + 1 ∧
      ∃ c : ℝ, ∀ x, t.Matches x → evaluate default list x = c := by
  induction list with
  | nil =>
      exact ⟨s, s.extends_refl, by omega, default, fun _ _ ↦ rfl⟩
  | cons h tail ih =>
      by_cases hi : h.coordinate ∈ s.fixed
      · by_cases hv : s.values h.coordinate = h.value
        · refine ⟨s, s.extends_refl, by omega, h.output, ?_⟩
          intro x hx
          simp [evaluate, hx h.coordinate hi, hv]
        · obtain ⟨t, hst, hcard, c, hc⟩ := ih
          refine ⟨t, hst, hcard, c, ?_⟩
          intro x hx
          have hxi := hst x hx h.coordinate hi
          simp [evaluate, hxi, hv, hc x hx]
      · let t : Subcube ι := ⟨insert h.coordinate s.fixed,
          Function.update s.values h.coordinate h.value⟩
        have hst : s.Extends t := by
          intro x hx i his
          have hine : i ≠ h.coordinate := by
            intro heq
            exact hi (heq ▸ his)
          have hh := hx i (Finset.mem_insert_of_mem his)
          simpa [t, Function.update_of_ne hine] using hh
        refine ⟨t, hst, ?_, h.output, ?_⟩
        · simp [t, Finset.card_insert_of_notMem hi]
        · intro x hx
          have hh := hx h.coordinate (Finset.mem_insert_self _ _)
          have heq : x h.coordinate = h.value := by simpa [t] using hh
          simp [evaluate, heq]

structure PriorityList (ι : Type*) where
  default : ℝ
  literals : List (Literal ι)

def PriorityList.eval (p : PriorityList ι) (x : ι → Bool) : ℝ :=
  evaluate p.default p.literals x

def listSum : List (PriorityList ι) → (ι → Bool) → ℝ
  | [], _ => 0
  | p :: ps, x => p.eval x + listSum ps x

/-- A sum of `H` lists is constant after fixing at most `H` coordinates. -/
theorem freeze_sum (lists : List (PriorityList ι)) (s : Subcube ι) :
    ∃ t : Subcube ι, s.Extends t ∧ t.fixed.card ≤ s.fixed.card + lists.length ∧
      ∃ c : ℝ, ∀ x, t.Matches x → listSum lists x = c := by
  induction lists generalizing s with
  | nil => exact ⟨s, s.extends_refl, by simp, 0, fun _ _ ↦ rfl⟩
  | cons p ps ih =>
      obtain ⟨u, hsu, hucard, a, ha⟩ := freeze_one p.default p.literals s
      obtain ⟨t, hut, htcard, b, hb⟩ := ih u
      refine ⟨t, Subcube.extends_trans hsu hut, ?_, a + b, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro x hx
        simp [listSum, PriorityList.eval, ha x (hut x hx), hb x hx]

def emptySubcube : Subcube ι := ⟨∅, fun _ ↦ false⟩

theorem freeze_sum_from_empty (lists : List (PriorityList ι)) :
    ∃ t : Subcube ι, t.fixed.card ≤ lists.length ∧
      ∃ c : ℝ, ∀ x, t.Matches x → listSum lists x = c := by
  obtain ⟨t, _, hcard, c, hc⟩ := freeze_sum lists emptySubcube
  exact ⟨t, by simpa [emptySubcube] using hcard, c, hc⟩

/-! The blockwise majority-agreement function survives these restrictions. -/

def ones {m : ℕ} (x : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ x i = true).card

def blockFixed {m : ℕ} (s : Subcube (Bool × Fin m)) (b : Bool) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ (b, i) ∈ s.fixed

theorem card_blockFixed_le {m : ℕ} (s : Subcube (Bool × Fin m)) (b : Bool) :
    (blockFixed s b).card ≤ s.fixed.card := by
  apply Finset.card_le_card_of_injOn (fun i ↦ (b, i))
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Prod.mk.inj hij |>.2

def completion {m : ℕ} (s : Subcube (Bool × Fin m)) (modes : Bool → Bool) :
    Bool × Fin m → Bool :=
  fun p ↦ if p ∈ s.fixed then s.values p else modes p.1

theorem completion_matches {m : ℕ} (s : Subcube (Bool × Fin m)) (modes : Bool → Bool) :
    s.Matches (completion s modes) := by
  intro p hp
  simp [completion, hp]

theorem low_ones_le {m : ℕ} (s : Subcube (Bool × Fin m)) (modes : Bool → Bool)
    (b : Bool) (hb : modes b = false) :
    ones (fun i ↦ completion s modes (b, i)) ≤ s.fixed.card := by
  apply le_trans (Finset.card_le_card ?_) (card_blockFixed_le s b)
  intro i hi
  have hval := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hn
  simp [completion, hn, hb] at hval

theorem high_ones_ge {m : ℕ} (s : Subcube (Bool × Fin m)) (modes : Bool → Bool)
    (b : Bool) (hb : modes b = true) :
    m - s.fixed.card ≤ ones (fun i ↦ completion s modes (b, i)) := by
  have hsub : Finset.univ \ blockFixed s b ⊆
      Finset.univ.filter (fun i ↦ completion s modes (b, i) = true) := by
    intro i hi
    have hn : (b, i) ∉ s.fixed := by
      simpa [blockFixed] using (Finset.mem_sdiff.mp hi).2
    simp [completion, hn, hb]
  have hc := Finset.card_le_card hsub
  have hbcard := card_blockFixed_le s b
  simp only [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin] at hc
  exact le_trans (Nat.sub_le_sub_left hbcard m) hc

def agreement (k : ℕ) {m : ℕ} (x : Bool × Fin m → Bool) : Prop :=
  (k < ones (fun i ↦ x (false, i))) ↔ (k < ones (fun i ↦ x (true, i)))

def modes (a b : Bool) : Bool → Bool := fun t ↦ if t then b else a

theorem completion_agreement {k m : ℕ} (hm : 2 * k < m)
    (s : Subcube (Bool × Fin m)) (hs : s.fixed.card ≤ k) (a b : Bool) :
    agreement k (completion s (modes a b)) ↔ a = b := by
  have hh : k < m - s.fixed.card := by omega
  have hiff (t : Bool) :
      (k < ones (fun i ↦ completion s (modes a b) (t, i))) ↔ modes a b t = true := by
    cases heq : modes a b t with
    | false =>
        have hl := low_ones_le s (modes a b) t heq
        simp only [Bool.false_eq_true, iff_false]
        omega
    | true =>
        have hl := high_ones_ge s (modes a b) t heq
        simp only [iff_true]
        omega
  simp only [agreement, hiff]
  cases a <;> cases b <;> decide

def separableScore {m : ℕ} (left right : (Fin m → Bool) → ℝ)
    (x : Bool × Fin m → Bool) : ℝ :=
  left (fun i ↦ x (false, i)) + right (fun i ↦ x (true, i))

/-- Even an arbitrary additive score on the two blocks cannot avoid this lower
bound. In particular, an additional affine score cannot avoid it. -/
theorem majority_agreement_list_lower_bound {k m : ℕ} (hm : 2 * k < m)
    (lists : List (PriorityList (Bool × Fin m)))
    (left right : (Fin m → Bool) → ℝ)
    (hpos : ∀ x, agreement k x → 0 < separableScore left right x + listSum lists x)
    (hneg : ∀ x, ¬agreement k x → separableScore left right x + listSum lists x ≤ 0) :
    k + 1 ≤ lists.length := by
  by_contra hn
  have hlength : lists.length ≤ k := by omega
  obtain ⟨s, hs, c, hc⟩ := freeze_sum_from_empty lists
  have hsk : s.fixed.card ≤ k := hs.trans hlength
  let v (a b : Bool) := completion s (modes a b)
  have hconst (a b : Bool) : listSum lists (v a b) = c :=
    hc _ (completion_matches s _)
  have h00 : agreement k (v false false) :=
    (completion_agreement hm s hsk false false).mpr rfl
  have h11 : agreement k (v true true) :=
    (completion_agreement hm s hsk true true).mpr rfl
  have h01 : ¬agreement k (v false true) := by
    exact fun h ↦ Bool.false_ne_true ((completion_agreement hm s hsk false true).mp h)
  have h10 : ¬agreement k (v true false) := by
    exact fun h ↦ Bool.false_ne_true ((completion_agreement hm s hsk true false).mp h).symm
  have hp00 := hpos _ h00
  have hp11 := hpos _ h11
  have hn01 := hneg _ h01
  have hn10 := hneg _ h10
  rw [hconst] at hp00 hp11 hn01 hn10
  have hrectangle : separableScore left right (v false false) +
      separableScore left right (v true true) =
      separableScore left right (v false true) +
      separableScore left right (v true false) := by
    dsimp [separableScore, v, completion, modes]
    ring
  linarith

/-- The algebraic identity used for the independent two-head construction. -/
theorem two_ratio_product_identity (A D L δ : ℝ) (hD : D ≠ 0)
    (hB : D + δ * L ≠ 0) :
    A / D - A / (D + δ * L) = δ * A * L / (D * (D + δ * L)) := by
  field_simp
  ring

end HeadComplexity.PriorityRestriction
