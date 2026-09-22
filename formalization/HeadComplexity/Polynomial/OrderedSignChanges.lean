import HeadComplexity.Atoms.SignPolynomial
import HeadComplexity.Polynomial.UnivariateSignChanges

set_option linter.style.header false

/-!
# Sign changes on arbitrary ordered real nodes

The symmetric theory uses the equally spaced nodes `0, ..., n`.  Positive
weighted projections instead produce an arbitrary finite increasing sequence
of real nodes.  This file proves the corresponding upper and lower polynomial
statements without referring to attention heads.
-/

namespace HeadComplexity

open Finset Polynomial Set
open scoped BigOperators

/-- Regard `k <= n` as an index of `Fin (n + 1)`. -/
def orderedNodeIndex (n k : ℕ) (hk : k ≤ n) : Fin (n + 1) :=
  ⟨k, Nat.lt_succ_iff.mpr hk⟩

/-- A root strictly between ordered nodes `t` and `t + 1`.
The value outside `t < n` is irrelevant and only makes the definition total. -/
noncomputable def orderedCut {n : ℕ} (τ : Fin (n + 1) → ℝ) (t : ℕ) : ℝ :=
  if ht : t < n then
    (τ (orderedNodeIndex n t ht.le) + τ (orderedNodeIndex n (t + 1) ht)) / 2
  else 0

theorem orderedCut_between {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : StrictMono τ) {t : ℕ} (ht : t < n) :
    τ (orderedNodeIndex n t ht.le) < orderedCut τ t ∧
      orderedCut τ t < τ (orderedNodeIndex n (t + 1) ht) := by
  rw [orderedCut, dif_pos ht]
  have hstep : τ (orderedNodeIndex n t ht.le) <
      τ (orderedNodeIndex n (t + 1) ht) := by
    apply hτ
    simp [orderedNodeIndex]
  constructor <;> linarith

/-- The product of the ordered root factors has sign determined by the number
of remaining label changes. -/
theorem ordered_prod_sign {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : StrictMono τ) (F : ℕ → Bool) (k : ℕ) (hk : k ≤ n) :
    (0 < ∏ t ∈ changeSet F n,
      (τ (orderedNodeIndex n k hk) - orderedCut τ t)) ↔ Even (negCount F n k) := by
  classical
  have hpow : (0 < (-1 : ℝ) ^ negCount F n k) ↔ Even (negCount F n k) := by
    rcases Nat.even_or_odd (negCount F n k) with he | ho
    · rw [he.neg_one_pow]
      simp [he]
    · rw [ho.neg_one_pow]
      constructor
      · intro h
        norm_num at h
      · intro h
        rw [Nat.even_iff] at h
        rw [Nat.odd_iff] at ho
        omega
  rw [← hpow,
    ← Finset.prod_filter_mul_prod_filter_not (changeSet F n) (fun t => k ≤ t)]
  have hge :
      (∏ t ∈ (changeSet F n).filter (fun t => k ≤ t),
          (τ (orderedNodeIndex n k hk) - orderedCut τ t)) =
        (-1) ^ negCount F n k *
          ∏ t ∈ (changeSet F n).filter (fun t => k ≤ t),
            (orderedCut τ t - τ (orderedNodeIndex n k hk)) := by
    rw [show negCount F n k =
      ((changeSet F n).filter (fun t => k ≤ t)).card from rfl, ← Finset.prod_neg]
    exact Finset.prod_congr rfl (fun t _ => by ring)
  have hge_pos : 0 <
      ∏ t ∈ (changeSet F n).filter (fun t => k ≤ t),
        (orderedCut τ t - τ (orderedNodeIndex n k hk)) := by
    apply Finset.prod_pos
    intro t ht
    rw [Finset.mem_filter] at ht
    have htn : t < n := by
      exact Finset.mem_range.mp
        (Finset.mem_filter.mp (show t ∈ changeSet F n from ht.1)).1
    have hmono : τ (orderedNodeIndex n k hk) ≤
        τ (orderedNodeIndex n t htn.le) := by
      exact hτ.monotone (by simpa [orderedNodeIndex] using ht.2)
    exact sub_pos.mpr (hmono.trans_lt (orderedCut_between τ hτ htn).1)
  have hlt_pos : 0 <
      ∏ t ∈ (changeSet F n).filter (fun t => ¬ k ≤ t),
        (τ (orderedNodeIndex n k hk) - orderedCut τ t) := by
    apply Finset.prod_pos
    intro t ht
    rw [Finset.mem_filter] at ht
    have htn : t < n := by
      exact Finset.mem_range.mp
        (Finset.mem_filter.mp (show t ∈ changeSet F n from ht.1)).1
    have htk : t + 1 ≤ k := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge ht.2)
    have hmono : τ (orderedNodeIndex n (t + 1) htn) ≤
        τ (orderedNodeIndex n k hk) := by
      exact hτ.monotone (by simpa [orderedNodeIndex] using htk)
    exact sub_pos.mpr ((orderedCut_between τ hτ htn).2.trans_le hmono)
  rw [hge, mul_assoc, mul_pos_iff_of_pos_right (mul_pos hge_pos hlt_pos)]

/-- A profile on arbitrary strictly increasing real nodes has a sign polynomial
whose degree is at most its number of adjacent label changes. -/
theorem exists_ordered_sign_poly {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hτ : StrictMono τ) (F : ℕ → Bool) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ signChanges n F ∧
      ∀ k : ℕ, ∀ hk : k ≤ n,
        (0 < P.eval (τ (orderedNodeIndex n k hk)) ↔ F k = true) := by
  classical
  let P : Polynomial ℝ :=
    C (if F n then (1 : ℝ) else -1) *
      ∏ t ∈ changeSet F n, (X - C (orderedCut τ t))
  refine ⟨P, ?_, ?_⟩
  · dsimp [P]
    rw [natDegree_C_mul (by split <;> norm_num :
      (if F n then (1 : ℝ) else -1) ≠ 0),
      natDegree_prod _ _ (fun i _ => (monic_X_sub_C _).ne_zero)]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    rw [changeSet_card]
  · intro k hk
    have heval : P.eval (τ (orderedNodeIndex n k hk)) =
        (if F n then (1 : ℝ) else -1) *
          ∏ t ∈ changeSet F n,
            (τ (orderedNodeIndex n k hk) - orderedCut τ t) := by
      dsimp [P]
      rw [eval_mul, eval_C, eval_prod]
      simp
    rw [heval]
    have hpar := eq_Fn_iff_even_negCount F n hk
    have hsgn := ordered_prod_sign τ hτ F k hk
    have hne : (∏ t ∈ changeSet F n,
        (τ (orderedNodeIndex n k hk) - orderedCut τ t)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      have htn : t < n := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      by_cases hkt : k ≤ t
      · have hmono : τ (orderedNodeIndex n k hk) ≤
            τ (orderedNodeIndex n t htn.le) :=
          hτ.monotone (by simpa [orderedNodeIndex] using hkt)
        exact sub_ne_zero.mpr (ne_of_lt
          (hmono.trans_lt (orderedCut_between τ hτ htn).1))
      · have htk' : t + 1 ≤ k := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hkt)
        have hmono : τ (orderedNodeIndex n (t + 1) htn) ≤
            τ (orderedNodeIndex n k hk) :=
          hτ.monotone (by simpa [orderedNodeIndex] using htk')
        exact sub_ne_zero.mpr (ne_of_gt
          ((orderedCut_between τ hτ htn).2.trans_le hmono))
    by_cases hFn : F n = true
    · rw [if_pos hFn, one_mul, hsgn, ← hpar, hFn]
    · have hFn' : F n = false := by
        revert hFn
        cases F n <;> simp
      rw [if_neg hFn, neg_one_mul, neg_pos]
      have hlt :
          ((∏ t ∈ changeSet F n,
              (τ (orderedNodeIndex n k hk) - orderedCut τ t)) < 0) ↔
            ¬ (0 < ∏ t ∈ changeSet F n,
              (τ (orderedNodeIndex n k hk) - orderedCut τ t)) :=
        ⟨fun h => not_lt.mpr (le_of_lt h),
          fun h => lt_of_le_of_ne (not_lt.mp h) hne⟩
      rw [hlt, hsgn, ← hpar, hFn']
      cases F k <;> simp

/-- A polynomial with strict prescribed signs on arbitrary increasing nodes
has degree at least the number of adjacent sign changes. -/
theorem ordered_signChanges_le_natDegree {n : ℕ} (p : ℝ[X])
    (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ) (F : ℕ → Bool)
    (hpos : ∀ k (hk : k ≤ n), F k = true →
      0 < p.eval (τ (orderedNodeIndex n k hk)))
    (hneg : ∀ k (hk : k ≤ n), F k = false →
      p.eval (τ (orderedNodeIndex n k hk)) < 0) :
    signChanges n F ≤ p.natDegree := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    cases hF : F 0 with
    | false => simpa using hneg 0 (Nat.zero_le n) hF
    | true => simpa using hpos 0 (Nat.zero_le n) hF
  have hroot : ∀ (t : ℕ) (ht : t < n), F t ≠ F (t + 1) →
      ∃ c, c ∈ Ioo (τ (orderedNodeIndex n t ht.le))
          (τ (orderedNodeIndex n (t + 1) ht)) ∧ p.eval c = 0 := by
    intro t ht hne
    let it : Fin (n + 1) := orderedNodeIndex n t ht.le
    let its : Fin (n + 1) := orderedNodeIndex n (t + 1) ht
    have hab : τ it ≤ τ its := (hτ (by simp [it, its, orderedNodeIndex])).le
    have hcont : ContinuousOn (fun x => p.eval x) (Icc (τ it) (τ its)) :=
      (Polynomial.continuous p).continuousOn
    cases hFt : F t with
    | false =>
        have hFt1 : F (t + 1) = true := by
          cases hh : F (t + 1) with
          | false => exact absurd (hFt.trans hh.symm) hne
          | true => rfl
        have e1 : p.eval (τ it) < 0 := hneg t ht.le hFt
        have e2 : 0 < p.eval (τ its) := hpos (t + 1) ht hFt1
        obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo hab hcont ⟨e1, e2⟩
        exact ⟨c, hc, hce⟩
    | true =>
        have hFt1 : F (t + 1) = false := by
          cases hh : F (t + 1) with
          | false => rfl
          | true => exact absurd (hFt.trans hh.symm) hne
        have e1 : 0 < p.eval (τ it) := hpos t ht.le hFt
        have e2 : p.eval (τ its) < 0 := hneg (t + 1) ht hFt1
        obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo' hab hcont ⟨e2, e1⟩
        exact ⟨c, hc, hce⟩
  rw [signChanges]
  set S := (Finset.range n).filter (fun t => F t ≠ F (t + 1)) with hSdef
  let g : ℕ → ℝ := fun t =>
    if ht : t < n ∧ F t ≠ F (t + 1) then
      Classical.choose (hroot t ht.1 ht.2)
    else 0
  have hg (t : ℕ) (htS : t ∈ S) :
      g t ∈ Ioo (τ (orderedNodeIndex n t (by
        rw [hSdef, Finset.mem_filter, Finset.mem_range] at htS
        exact htS.1.le)))
        (τ (orderedNodeIndex n (t + 1) (by
          rw [hSdef, Finset.mem_filter, Finset.mem_range] at htS
          exact htS.1))) ∧ p.eval (g t) = 0 := by
    have ht : t < n ∧ F t ≠ F (t + 1) := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at htS
      exact htS
    rw [show g t = Classical.choose (hroot t ht.1 ht.2) by simp [g, ht]]
    exact Classical.choose_spec (hroot t ht.1 ht.2)
  have hinj : Set.InjOn g (S : Set ℕ) := by
    intro a ha b hb hgab
    rw [Finset.mem_coe] at ha hb
    have ha' : a < n ∧ F a ≠ F (a + 1) := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at ha
      exact ha
    have hb' : b < n ∧ F b ≠ F (b + 1) := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at hb
      exact hb
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exfalso
      have hga := (hg a ha).1
      have hgb := (hg b hb).1
      have hstep :
          τ (orderedNodeIndex n (a + 1) ha'.1) ≤
            τ (orderedNodeIndex n b hb'.1.le) := by
        exact hτ.monotone (by simpa [orderedNodeIndex] using hlt)
      have : g a < g b := lt_of_lt_of_le hga.2
        (le_trans hstep (le_of_lt hgb.1))
      exact (ne_of_lt this) hgab
    · exact heq
    · exfalso
      have hga := (hg a ha).1
      have hgb := (hg b hb).1
      have hstep :
          τ (orderedNodeIndex n (b + 1) hb'.1) ≤
            τ (orderedNodeIndex n a ha'.1.le) := by
        exact hτ.monotone (by simpa [orderedNodeIndex] using hlt)
      have : g b < g a := lt_of_lt_of_le hgb.2
        (le_trans hstep (le_of_lt hga.1))
      exact (ne_of_lt this) hgab.symm
  have hmaps : S.image g ⊆ p.roots.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨t, htS, rfl⟩ := hy
    rw [Multiset.mem_toFinset, mem_roots hp0]
    exact (hg t htS).2
  calc
    S.card = (S.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hmaps
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- The usual threshold convention only requires nonpositive values on false
nodes.  On a finite node set a small downward shift makes those values strictly
negative without changing the degree bound. -/
theorem ordered_signChanges_le_of_sign_iff {n : ℕ} (p : ℝ[X])
    (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ) (F : ℕ → Bool)
    (hsign : ∀ k (hk : k ≤ n),
      (0 < p.eval (τ (orderedNodeIndex n k hk)) ↔ F k = true)) :
    signChanges n F ≤ p.natDegree := by
  classical
  let T : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => F i = true)
  by_cases hT : T.Nonempty
  · let V : Finset ℝ := T.image (fun i => p.eval (τ i))
    have hV : V.Nonempty := hT.image _
    let m : ℝ := V.min' hV
    have hmpos : 0 < m := by
      have hmmem : m ∈ V := by
        exact V.min'_mem hV
      rw [Finset.mem_image] at hmmem
      obtain ⟨i, hiT, hi⟩ := hmmem
      rw [← hi]
      have hiF : F i = true := (Finset.mem_filter.mp hiT).2
      have hi_le : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
      simpa [orderedNodeIndex] using (hsign i hi_le).2 hiF
    let ε : ℝ := m / 2
    let q : ℝ[X] := p - C ε
    have hqdeg : q.natDegree ≤ p.natDegree := by
      dsimp [q]
      exact (natDegree_sub_le p (C ε)).trans (by simp)
    refine (ordered_signChanges_le_natDegree q τ hτ F ?_ ?_).trans hqdeg
    · intro k hk hFk
      have hiT : orderedNodeIndex n k hk ∈ T := by
        simp [T, orderedNodeIndex, hFk]
      have hiV : p.eval (τ (orderedNodeIndex n k hk)) ∈ V :=
        Finset.mem_image_of_mem _ hiT
      have hmle : m ≤ p.eval (τ (orderedNodeIndex n k hk)) := by
        exact V.min'_le _ hiV
      simp only [q, eval_sub, eval_C]
      dsimp [ε]
      linarith
    · intro k hk hFk
      have hnpos : ¬ 0 < p.eval (τ (orderedNodeIndex n k hk)) := by
        intro hp
        have : F k = true := (hsign k hk).1 hp
        exact Bool.false_ne_true (hFk.symm.trans this)
      simp only [q, eval_sub, eval_C]
      dsimp [ε]
      linarith
  · have hfalse : ∀ k, k ≤ n → F k = false := by
      intro k hk
      cases hFk : F k with
      | false => rfl
      | true =>
          exfalso
          apply hT
          exact ⟨orderedNodeIndex n k hk, by simp [T, orderedNodeIndex, hFk]⟩
    have hz : signChanges n F = 0 := by
      rw [signChanges, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t ht
      have htn : t < n := Finset.mem_range.mp ht
      simp [hfalse t htn.le, hfalse (t + 1) htn]
    rw [hz]
    exact Nat.zero_le _

end HeadComplexity
