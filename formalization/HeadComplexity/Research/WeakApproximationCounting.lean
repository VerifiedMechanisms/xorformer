import HeadComplexity.Research.ApproximateMarginCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
An arbitrary agreement advantage, not just a fixed small error fraction,
suffices for the comparison-class route. This file proves the finite counting
inequality. It does not assert an approximation theorem for original heads.
-/

noncomputable section
namespace HeadComplexity.WeakApproximationCounting
open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def agreementBall (g : ι → Bool) (epsilon : ℝ) : Finset (ι → Bool) :=
  Finset.univ.filter fun f ↦
    (hammingDist f g : ℝ) ≤ (1 / 2 - epsilon) * Fintype.card ι

def signedAgreement (f g : ι → Bool) : ℝ :=
  ∑ i, if f i = g i then 1 else -1

lemma signedAgreement_eq (f g : ι → Bool) :
    signedAgreement f g = (Fintype.card ι : ℝ) - 2 * hammingDist f g := by
  classical
  have hpoint (i : ι) : (if f i = g i then (1 : ℝ) else -1) =
      1 - 2 * (if f i ≠ g i then 1 else 0) := by
    by_cases h : f i = g i <;> norm_num [h]
  simp_rw [signedAgreement, hpoint, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_boole]
  rfl

lemma sum_exp_signedAgreement (g : ι → Bool) (t : ℝ) :
    ∑ f : ι → Bool, Real.exp (t * signedAgreement f g) =
      (Real.exp t + Real.exp (-t)) ^ Fintype.card ι := by
  classical
  have heq (f : ι → Bool) : Real.exp (t * signedAgreement f g) =
      ∏ i, if f i = g i then Real.exp t else Real.exp (-t) := by
    rw [signedAgreement, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : f i = g i <;> simp [h]
  simp_rw [heq]
  rw [← Fintype.prod_sum (fun i (b : Bool) ↦
    if b = g i then Real.exp t else Real.exp (-t))]
  have hs (i : ι) : (∑ b : Bool,
      if b = g i then Real.exp t else Real.exp (-t)) =
        Real.exp t + Real.exp (-t) := by
    cases g i <;> simp [add_comm]
  simp_rw [hs]
  simp

/-- Finite-cube Hoeffding bound, without a probabilistic representation. -/
theorem card_agreementBall_le (g : ι → Bool) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    ((agreementBall g epsilon).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι *
        Real.exp (-2 * epsilon ^ 2 * Fintype.card ι) := by
  classical
  let t := 2 * epsilon
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsum : ((agreementBall g epsilon).card : ℝ) *
      Real.exp (2 * epsilon * t * Fintype.card ι) ≤
        (Real.exp t + Real.exp (-t)) ^ Fintype.card ι := by
    calc
      _ = ∑ _f ∈ agreementBall g epsilon,
          Real.exp (2 * epsilon * t * Fintype.card ι) := by simp
      _ ≤ ∑ f ∈ agreementBall g epsilon,
          Real.exp (t * signedAgreement f g) := by
        apply Finset.sum_le_sum
        intro f hf
        apply Real.exp_le_exp.mpr
        rw [signedAgreement_eq]
        have hd := (Finset.mem_filter.mp hf).2
        have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * t by positivity)
        nlinarith
      _ ≤ ∑ f : ι → Bool, Real.exp (t * signedAgreement f g) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro f _ _
        exact (Real.exp_pos _).le
      _ = _ := sum_exp_signedAgreement g t
  have hcosh : Real.exp t + Real.exp (-t) ≤ 2 * Real.exp (t ^ 2 / 2) := by
    have h := Real.cosh_le_exp_half_sq t
    rw [Real.cosh_eq] at h
    linarith
  have hexp : (Real.exp t + Real.exp (-t)) ^ Fintype.card ι ≤
      (2 : ℝ) ^ Fintype.card ι *
        Real.exp ((Fintype.card ι : ℝ) * (t ^ 2 / 2)) := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hcosh _
  have hpos := Real.exp_pos (2 * epsilon * t * Fintype.card ι)
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    _ ≤ (2 : ℝ) ^ Fintype.card ι *
        Real.exp ((Fintype.card ι : ℝ) * (t ^ 2 / 2)) :=
      (by simpa only [mul_comm] using hsum.trans hexp)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [t]
      ring

def nearbyTables (G : Finset (ι → Bool)) (epsilon : ℝ) : Finset (ι → Bool) :=
  G.biUnion fun g ↦ agreementBall g epsilon

theorem card_nearbyTables_le (G : Finset (ι → Bool)) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    ((nearbyTables G epsilon).card : ℝ) ≤
      G.card * (2 : ℝ) ^ Fintype.card ι *
        Real.exp (-2 * epsilon ^ 2 * Fintype.card ι) := by
  classical
  calc
    _ ≤ ∑ g ∈ G, ((agreementBall g epsilon).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (nearbyTables G epsilon).card ≤ ∑ g ∈ G, (agreementBall g epsilon).card)
    _ ≤ ∑ _g ∈ G, (2 : ℝ) ^ Fintype.card ι *
        Real.exp (-2 * epsilon ^ 2 * Fintype.card ι) := by
      exact Finset.sum_le_sum fun g _ ↦ card_agreementBall_le g hepsilon
    _ = _ := by simp; ring

/-- The number of centers may use any proved capacity bound. -/
theorem card_nearbyTables_lt (G : Finset (ι → Bool)) {epsilon L : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : (G.card : ℝ) ≤ Real.exp L)
    (hbudget : L < 2 * epsilon ^ 2 * Fintype.card ι) :
    (nearbyTables G epsilon).card < 2 ^ Fintype.card ι := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
  have hsmall : Real.exp (L - 2 * epsilon ^ 2 * Fintype.card ι) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hc : ((nearbyTables G epsilon).card : ℝ) <
      (2 : ℝ) ^ Fintype.card ι := by
    calc
      _ ≤ G.card * (2 : ℝ) ^ Fintype.card ι *
          Real.exp (-2 * epsilon ^ 2 * Fintype.card ι) :=
        card_nearbyTables_le G hepsilon
      _ ≤ Real.exp L * (2 : ℝ) ^ Fintype.card ι *
          Real.exp (-2 * epsilon ^ 2 * Fintype.card ι) := by gcongr
      _ = (2 : ℝ) ^ Fintype.card ι *
          Real.exp (L - 2 * epsilon ^ 2 * Fintype.card ι) := by
        rw [show -2 * epsilon ^ 2 * (Fintype.card ι : ℝ) =
          -(2 * epsilon ^ 2 * Fintype.card ι) by ring,
          Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
        ring
      _ < (2 : ℝ) ^ Fintype.card ι := by nlinarith
  exact_mod_cast hc

/-- The center class is fixed before the original truth table is chosen. -/
def HasWeakApproximation (n H : ℕ)
    (G : Finset ((Fin n → Bool) → Bool)) (epsilon : ℝ) : Prop :=
  ∀ f, computableWithHeadsN n H f → ∃ g ∈ G,
    (hammingDist f g : ℝ) ≤ (1 / 2 - epsilon) * (2 : ℝ) ^ n

theorem worstCase_gt_of_weak_approximation {n H : ℕ}
    (G : Finset ((Fin n → Bool) → Bool)) {epsilon L : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : (G.card : ℝ) ≤ Real.exp L)
    (hbudget : L < 2 * epsilon ^ 2 * (2 : ℝ) ^ n)
    (hrepair : HasWeakApproximation n H G epsilon) :
    H < worstCaseHeadComplexity n := by
  classical
  have hN : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  have hsub : headComputableFunctions n H ⊆
      (nearbyTables G epsilon : Set ((Fin n → Bool) → Bool)) := by
    intro f hf
    obtain ⟨g, hg, hd⟩ := hrepair f hf
    change f ∈ nearbyTables G epsilon
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hg, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [hN, Nat.cast_pow, Nat.cast_ofNat] using hd
  have hc := card_nearbyTables_lt G hepsilon hG
    (by simpa only [hN, Nat.cast_pow, Nat.cast_ofNat] using hbudget)
  have hcount : (headComputableFunctions n H).ncard < 2 ^ (2 ^ n) :=
    (Set.ncard_le_ncard hsub).trans_lt (by simpa only [Set.ncard_coe_finset, hN] using hc)
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt hcount
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

open RelativeMarginQuantifiers

def HasWeakMarginRepair (n H K : ℕ) (epsilon gamma : ℝ) : Prop :=
  ∀ f, computableWithHeadsN n H f → ∃ g,
    HasRelativeMargin n K g gamma ∧
      (hammingDist f g : ℝ) ≤ (1 / 2 - epsilon) * (2 : ℝ) ^ n

def finiteMarginEntropy (n K d : ℕ) : ℝ :=
  (K : ℝ) * (Real.log 2 + (n + 1) * Real.log (n + 1)) +
    (1 + 3 * (n + 1) * K) *
      Real.log (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
        (1 + 3 * (n + 1) * K))

/-- The finite margin-sensitive formula can be combined directly with any
proved advantage over one-half agreement. Every original head remains in scope. -/
theorem worstCase_gt_of_weak_margin_repair {n H K d : ℕ} {epsilon gamma : ℝ}
    (hepsilon : 0 ≤ epsilon) (hgamma : 0 < gamma)
    (hdegree : Real.exp (-((d + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ gamma / 2)
    (hparameters : 1 + 3 * (n + 1) * K ≤ 2 ^ n)
    (hbudget : finiteMarginEntropy n K d < 2 * epsilon ^ 2 * (2 : ℝ) ^ n)
    (hrepair : HasWeakMarginRepair n H K epsilon gamma) :
    H < worstCaseHeadComplexity n := by
  classical
  have hG : (((highMarginFunctions n K gamma).toFinset.card : ℕ) : ℝ) ≤
      Real.exp (finiteMarginEntropy n K d) := by
    simpa only [← Set.ncard_eq_toFinset_card', finiteMarginEntropy] using
      MarginCapacityEstimates.card_highMarginFunctions_le_exp hgamma d hdegree hparameters
  apply worstCase_gt_of_weak_approximation
    (highMarginFunctions n K gamma).toFinset hepsilon hG hbudget
  intro f hf
  obtain ⟨g, hg, hd⟩ := hrepair f hf
  exact ⟨g, Set.mem_toFinset.mpr hg, hd⟩

end HeadComplexity.WeakApproximationCounting
