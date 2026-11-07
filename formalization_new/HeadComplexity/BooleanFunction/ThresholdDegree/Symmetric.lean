module

public import HeadComplexity.BooleanFunction.Symmetric
public import HeadComplexity.BooleanFunction.ThresholdDegree.Basic
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Threshold degree of symmetric Boolean functions

The average of a polynomial on a Hamming layer is polynomial in the layer index.
Applied to a strict sign representation, the average retains the profile's signs.
Each sign change then gives a distinct root of the univariate polynomial.
Conversely, a polynomial with a root at each adjacent change gives a sign representation
of the profile.
-/

public section

open scoped BigOperators

namespace MvPolynomial

variable {ι K : Type*} [Field K] [CharZero K]

section

variable [DecidableEq ι]

/-- A uniformly chosen subset of size `k` contains a fixed subset with probability equal to the
ratio of the two binomial coefficients for choosing its size from `k` elements and from the
full set. -/
private theorem expect_subset_powersetCard (s t : Finset ι) (hst : s ⊆ t) {k : ℕ}
    (hk : k ≤ t.card) :
    (𝔼 u ∈ t.powersetCard k, if s ⊆ u then (1 : K) else 0) =
      (k.choose s.card : K) / (t.card.choose s.card : K) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_powersetCard]
  by_cases hsk : s.card ≤ k
  · rw [Finset.card_filter_powersetCard_subset s t k hst hsk]
    apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne')
      (Nat.cast_ne_zero.mpr (Nat.choose_pos (Finset.card_le_card hst)).ne')).2
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact congrArg (Nat.cast : ℕ → K) (by simpa [mul_comm] using (Nat.choose_mul hsk).symm)
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hsk), Nat.cast_zero, zero_div]
    suffices (t.powersetCard k).filter (s ⊆ ·) = ∅ by simp [this]
    exact Finset.filter_eq_empty_iff.mpr fun u hu hsu ↦ hsk
      ((Finset.card_le_card hsu).trans_eq (Finset.mem_powersetCard.mp hu).2)

/-- On a Boolean vertex, a monomial evaluates to one exactly when every variable in its support
is true, and to zero otherwise. -/
private theorem prod_cubePoint_pow (d : ι →₀ ℕ) (s : Finset ι) :
    (∏ i ∈ d.support, Bool.cubePoint K (fun j ↦ if j ∈ s then true else false) i ^ d i) =
      if d.support ⊆ s then 1 else 0 := by
  calc
    _ = ∏ i ∈ d.support, (if i ∈ s then (1 : K) else 0) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i ∈ s <;> simp [h, Finsupp.mem_support_iff.mp hi]
    _ = _ := Finset.prod_boole

/-- Averaging a multivariate polynomial over the Boolean vertices of weight `k`
gives a univariate polynomial in `k`, of degree at most the original total degree. -/
theorem exists_natDegree_le_eval_eqOn_expect_powersetCard [Fintype ι]
    (p : MvPolynomial ι K) :
    ∃ q : Polynomial K, q.natDegree ≤ p.totalDegree ∧
      Set.EqOn (fun k : ℕ ↦ q.eval (k : K))
        (fun k ↦ 𝔼 s ∈ (Finset.univ : Finset ι).powersetCard k,
          eval (Bool.cubePoint K (fun i ↦ if i ∈ s then true else false)) p)
        (Set.Iic (Fintype.card ι)) := by
  classical
  let r (d : ι →₀ ℕ) : Polynomial K := Polynomial.C
    (p.coeff d * (d.support.card.factorial : K)⁻¹ *
      ((Fintype.card ι).choose d.support.card : K)⁻¹) * descPochhammer K d.support.card
  refine ⟨∑ d ∈ p.support, r d, Polynomial.natDegree_sum_le_of_forall_le _ _ ?_, ?_⟩
  · intro d hd
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [descPochhammer_natDegree]
    calc
      d.support.card = ∑ _ ∈ d.support, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i hi ↦
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      _ ≤ p.totalDegree := le_totalDegree hd
  · intro k hk
    simp only [Polynomial.eval_finsetSum]
    simp_rw [eval_eq, prod_cubePoint_pow, Finset.expect_sum_comm, ← Finset.mul_expect]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [expect_subset_powersetCard _ _ (Finset.subset_univ _) (by simpa using hk)]
    simp only [Finset.card_univ, Nat.cast_choose_eq_descPochhammer_div K k, r,
      Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv]
    ac_rfl

end

/-- If a polynomial's values on the Boolean cube depend only on Hamming weight,
they agree with a univariate polynomial of no larger degree. -/
theorem exists_natDegree_le_eval_eq_hammingWeight [Fintype ι] (p : MvPolynomial ι K)
    (hp : (fun x : ι → Bool ↦ eval (Bool.cubePoint K x) p).FactorsThrough Bool.hammingWeight) :
    ∃ q : Polynomial K, q.natDegree ≤ p.totalDegree ∧
      ∀ x : ι → Bool, q.eval (Bool.hammingWeight x : K) = eval (Bool.cubePoint K x) p := by
  classical
  obtain ⟨q, hq, heval⟩ := p.exists_natDegree_le_eval_eqOn_expect_powersetCard
  refine ⟨q, hq, fun x ↦ ?_⟩
  rw [show q.eval (Bool.hammingWeight x : K) = _ from heval (Bool.hammingWeight_le_card x)]
  refine (Finset.expect_congr rfl fun s hs ↦ ?_).trans
    (Finset.expect_const (Finset.powersetCard_nonempty.mpr
      (by simpa using Bool.hammingWeight_le_card x)) _)
  apply hp
  simp [Bool.hammingWeight, (Finset.mem_powersetCard.mp hs).2]

/-- A symmetric polynomial restricts on the Boolean cube to a univariate polynomial
in the Hamming weight of no larger degree. -/
theorem IsSymmetric.exists_natDegree_le_eval_eq_hammingWeight [Fintype ι] {p : MvPolynomial ι K}
    (hp : p.IsSymmetric) :
    ∃ q : Polynomial K, q.natDegree ≤ p.totalDegree ∧
      ∀ x : ι → Bool, q.eval (Bool.hammingWeight x : K) = eval (Bool.cubePoint K x) p := by
  refine p.exists_natDegree_le_eval_eq_hammingWeight fun x y hxy ↦ ?_
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq _ _ hxy
  have hbits (i : ι) : y (σ i) = x i := by
    apply Bool.eq_iff_iff.mpr
    simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.mem_filter,
      Finset.mem_univ, true_and] using (Iff.of_eq (congrArg (σ i ∈ ·) hσ)).symm
  calc
    _ = eval (Bool.cubePoint K y ∘ σ) p := by
      congr 1
      funext i
      simp [hbits]
    _ = _ := by rw [← eval_rename, hp σ]

end MvPolynomial

namespace HeadComplexity.BooleanFunction

variable {n d : ℕ}

/-- A nonzero real polynomial has degree at least the number of unit intervals with integer
endpoints on which its endpoint values have opposite signs. -/
private theorem card_le_natDegree_of_eval_mul_neg (q : Polynomial ℝ) (hq : q ≠ 0)
    (s : Finset (Fin n))
    (hs : ∀ i ∈ s, q.eval (i.val : ℝ) * q.eval ((i.val : ℝ) + 1) < 0) :
    s.card ≤ q.natDegree := by
  classical
  have hroot (i : s) : ∃ r ∈ Set.Ioo (i.val.val : ℝ) ((i.val.val : ℝ) + 1), q.eval r = 0 := by
    have hle : (i.val.val : ℝ) ≤ (i.val.val : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
    rcases mul_neg_iff.mp (hs i.val i.property) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact intermediate_value_Ioo' hle q.continuous.continuousOn ⟨h₂, h₁⟩
    · exact intermediate_value_Ioo hle q.continuous.continuousOn ⟨h₁, h₂⟩
  choose r hr hqr using hroot
  have hmono : StrictMono r := by
    intro i j hij
    have hij' : (i.val.val : ℝ) + 1 ≤ j.val.val := by
      exact_mod_cast (show i.val.val + 1 ≤ j.val.val from hij)
    exact ((hr i).2.trans_le hij').trans (hr j).1
  let g (i : s) : q.roots.toFinset :=
    ⟨r i, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr (hqr i))⟩
  refine le_trans ?_ ((Multiset.toFinset_card_le q.roots).trans (Polynomial.card_roots' q))
  simpa using Fintype.card_le_of_injective g
    (fun _ _ h ↦ hmono.injective (congrArg Subtype.val h))

/-- Each change in a profile strictly represented by a univariate polynomial forces a root
between its two weights, so there are at most as many changes as the polynomial's degree. -/
theorem signChanges_le_natDegree {F : Fin (n + 1) → Bool} {q : Polynomial ℝ}
    (hsign : ∀ k, if F k then 0 < q.eval (k.val : ℝ) else q.eval (k.val : ℝ) < 0) :
    signChanges F ≤ q.natDegree := by
  refine card_le_natDegree_of_eval_mul_neg q ?_ _ ?_
  · rintro rfl
    specialize hsign 0
    cases h : F 0 <;> simp [h] at hsign
  intro i hi
  have hne : F i.castSucc ≠ F i.succ := (Finset.mem_filter.mp hi).2
  have hleft := hsign i.castSucc
  have hright := hsign i.succ
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_succ] at hleft hright
  cases h₀ : F i.castSucc <;> cases h₁ : F i.succ
  · exact (hne (h₀.trans h₁.symm)).elim
  · exact mul_neg_of_neg_of_pos
      (by simpa only [h₀, Bool.false_eq_true, ↓reduceIte] using hleft)
      (by simpa only [h₁, ↓reduceIte] using hright)
  · exact mul_neg_of_pos_of_neg
      (by simpa only [h₀, ↓reduceIte] using hleft)
      (by simpa only [h₁, Bool.false_eq_true, ↓reduceIte] using hright)
  · exact (hne (h₀.trans h₁.symm)).elim

/-- The sign-change count of a symmetric Boolean profile lower-bounds the degree
of any polynomial that sign-represents that profile. -/
theorem signChanges_le_of_thresholdDegreeLE {F : Fin (n + 1) → Bool}
    (h : ThresholdDegreeLE (symmetricFn F) d) : signChanges F ≤ d := by
  classical
  obtain ⟨p, hp, hsign⟩ := h
  obtain ⟨ε, _, hstrict⟩ := hsign.exists_pos_sub_strict
  let P := p - MvPolynomial.C ε
  have hP : P.totalDegree ≤ d := (MvPolynomial.totalDegree_sub _ _).trans (max_le hp (by simp))
  obtain ⟨q, hq, heval⟩ := P.exists_natDegree_le_eval_eqOn_expect_powersetCard
  have hqsign (k : Fin (n + 1)) :
      if F k then 0 < q.eval (k.val : ℝ) else q.eval (k.val : ℝ) < 0 := by
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    let layer := (Finset.univ : Finset (Fin n)).powersetCard k.val
    let x (s : Finset (Fin n)) (i : Fin n) : Bool := if i ∈ s then true else false
    rw [show q.eval (k.val : ℝ) = _ from
      heval (by simpa using hk : k.val ∈ Set.Iic (Fintype.card (Fin n)))]
    have hn : layer.Nonempty := Finset.powersetCard_nonempty.mpr (by simpa using hk)
    have hall (s : Finset (Fin n)) (hs : s ∈ layer) :
        if F k then 0 < MvPolynomial.eval (Bool.cubePoint ℝ (x s)) P
        else MvPolynomial.eval (Bool.cubePoint ℝ (x s)) P < 0 := by
      rw [← symmetricFn_apply_of_hammingWeight_eq F (x := x s) (k := k)
        (by simp [Bool.hammingWeight, x, (Finset.mem_powersetCard.mp hs).2])]
      simpa [P] using hstrict (x s)
    cases hF : F k <;> simp only [hF, Bool.false_eq_true, ↓reduceIte] at hall ⊢
    · obtain ⟨s, hs⟩ := hn
      exact Finset.expect_lt (fun s hs ↦ (hall s hs).le) ⟨s, hs, hall s hs⟩
    · exact Finset.expect_pos hall hn
  exact (signChanges_le_natDegree hqsign).trans (hq.trans hP)

section SignPolynomial

open Polynomial

private def profileTail {n : ℕ} (F : Fin (n + 1) → Bool) (k : ℕ) : Bool :=
  F ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Appending one profile value adds a sign change exactly when the new value differs from the
preceding one. -/
private theorem signChanges_succ {n : ℕ} (F : Fin (n + 2) → Bool) :
    signChanges F = signChanges (F ∘ Fin.castSucc) +
      if F (Fin.last n).castSucc ≠ F (Fin.last (n + 1)) then 1 else 0 := by
  simp only [signChanges, Finset.card_filter, Fin.sum_univ_castSucc, Function.comp_apply,
    Fin.castSucc_succ, Fin.succ_last, Nat.succ_eq_add_one]

/-- A profile extended constantly to the right has a polynomial with the prescribed strict signs
at every natural number and degree at most the original number of flips. -/
private theorem exists_polynomial_sign_profileTail {n : ℕ} (F : Fin (n + 1) → Bool) :
    ∃ p : ℝ[X], p.natDegree ≤ signChanges F ∧ ∀ k : ℕ,
      if profileTail F k then 0 < p.eval (k : ℝ) else p.eval (k : ℝ) < 0 := by
  induction n with
  | zero =>
    refine ⟨C (if F 0 then 1 else -1), by simp, fun k ↦ ?_⟩
    have hk : profileTail F k = F 0 := congrArg F (Fin.ext (Nat.min_zero k))
    cases h : F 0 <;> simp [hk, h]
  | succ n ih =>
    let G : Fin (n + 1) → Bool := F ∘ Fin.castSucc
    obtain ⟨p, hp, hs⟩ := ih G
    have hsame (k : ℕ) (hk : k ≤ n) : profileTail F k = profileTail G k := by
      simp [profileTail, G, min_eq_left hk, min_eq_left (hk.trans (Nat.le_succ n))]
    have htail (k : ℕ) (hk : n < k) : profileTail F k = F (Fin.last (n + 1)) := by
      simp [profileTail, min_eq_right (Nat.succ_le_of_lt hk), Fin.last]
    have htailG (k : ℕ) (hk : n < k) : profileTail G k = F (Fin.last n).castSucc := by
      simp [profileTail, G, min_eq_right hk.le, Fin.last]
    by_cases h : F (Fin.last n).castSucc = F (Fin.last (n + 1))
    · refine ⟨p, by simpa [signChanges_succ, h, G] using hp, fun k ↦ ?_⟩
      by_cases hk : k ≤ n
      · simpa only [hsame k hk] using hs k
      · simpa only [htail k (lt_of_not_ge hk), htailG k (lt_of_not_ge hk), h] using hs k
    · let q : ℝ[X] := C ((n : ℝ) + 1 / 2) - X
      refine ⟨p * q, ?_, fun k ↦ ?_⟩
      · rw [signChanges_succ, ite_eq_left h]
        exact natDegree_mul_le.trans (Nat.add_le_add hp ((natDegree_sub_le _ _).trans (by simp)))
      rw [eval_mul]
      have hsign := hs k
      by_cases hk : k ≤ n
      · have hpos : 0 < q.eval (k : ℝ) := by
          simpa only [q, eval_sub, eval_C, eval_X, sub_pos] using
            (Nat.cast_le.mpr hk).trans_lt (lt_add_of_pos_right (n : ℝ) (half_pos zero_lt_one))
        rw [hsame k hk]
        cases hb : profileTail G k
        · exact mul_neg_of_neg_of_pos
            (by simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hsign) hpos
        · exact mul_pos (by simpa only [hb, ↓reduceIte] using hsign) hpos
      · have hk' : n < k := lt_of_not_ge hk
        have hneg : q.eval (k : ℝ) < 0 := by
          have hk'' : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hk'
          simpa only [q, eval_sub, eval_C, eval_X, sub_neg] using
            (add_lt_add_right (half_lt_self (zero_lt_one : (0 : ℝ) < 1)) (n : ℝ)).trans_le hk''
        have hflip : profileTail G k ≠ profileTail F k := by
          rwa [htailG k hk', htail k hk']
        cases hb : profileTail G k <;> cases hc : profileTail F k
        · exact (hflip (hb.trans hc.symm)).elim
        · exact mul_pos_of_neg_of_neg
            (by simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hsign) hneg
        · exact mul_neg_of_pos_of_neg (by simpa only [hb, ↓reduceIte] using hsign) hneg
        · exact (hflip (hb.trans hc.symm)).elim

/-- A profile has a sign polynomial of degree at most its number of adjacent changes. -/
theorem exists_polynomial_natDegree_le_signChanges {n : ℕ} (F : Fin (n + 1) → Bool) :
    ∃ p : ℝ[X], p.natDegree ≤ signChanges F ∧
      ∀ k : Fin (n + 1), 0 < p.eval (k.val : ℝ) ↔ F k = true := by
  obtain ⟨p, hp, hs⟩ := exists_polynomial_sign_profileTail F
  refine ⟨p, hp, fun k ↦ ?_⟩
  have htail : profileTail F k.val = F k := by
    simp [profileTail, min_eq_left (Nat.le_of_lt_succ k.isLt)]
  have hsign := hs k.val
  rw [htail] at hsign
  cases h : F k
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
    exact iff_false_intro (not_lt.mpr hsign.le)
  · simpa [h] using hsign

end SignPolynomial

/-- Parity on `n` bits has threshold degree `n`. -/
theorem thresholdDegree_parity (n : ℕ) : thresholdDegree (parity n) = n := by
  refine le_antisymm ?_ ?_
  · apply ThresholdDegreeLE.thresholdDegree_le
    refine ⟨-∏ i : Fin n, (1 - MvPolynomial.C 2 * MvPolynomial.X i), ?_, fun x ↦ ?_⟩
    · rw [MvPolynomial.totalDegree_neg]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      calc
        _ ≤ ∑ _ : Fin n, (1 : ℕ) := Finset.sum_le_sum fun i _ ↦ by
          refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
          exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
        _ = n := by simp
    · change 0 < MvPolynomial.eval (Bool.cubePoint ℝ x) _ ↔ _
      rw [map_neg, map_prod]
      simp only [map_sub, map_one, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        Bool.cubePoint_apply, ← Bool.spin_eq_one_sub, parity_apply]
      have hspin : ∏ i : Fin n, Bool.spin ℝ (x i) = (-1 : ℝ) ^ Bool.hammingWeight x := by
        simp only [Bool.spin, ← Finset.prod_filter, Finset.prod_const, Bool.hammingWeight]
      rw [hspin]
      by_cases ho : Odd (Bool.hammingWeight x)
      · simp [ho, ho.neg_one_pow]
      · simp [ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]
  · simpa [parity] using signChanges_le_of_thresholdDegreeLE
      (thresholdDegreeLE_thresholdDegree (symmetricFn (parityProfile n)))

end HeadComplexity.BooleanFunction
