import HeadComplexity.Research.ConditionalMarginLowerBounds
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
A distributional margin repair suffices for the unrestricted counting route.
The Hamming-ball calculation is unconditional. The existence of an approximate
repair is an explicit hypothesis, not a proved property of xorformer heads.
-/

noncomputable section
namespace HeadComplexity.ApproximateMarginCounting
open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hammingBall (g : ι → Bool) (r : ℕ) : Finset (ι → Bool) :=
  Finset.univ.filter fun f ↦ hammingDist f g ≤ r

def agreementWeight (f g : ι → Bool) : ℕ :=
  ∏ i, if f i = g i then 4 else 1

lemma agreementWeight_eq (f g : ι → Bool) :
    agreementWeight f g = 4 ^ (Fintype.card ι - hammingDist f g) := by
  classical
  rw [agreementWeight, ← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  have h : (Finset.univ.filter fun i ↦ f i = g i).card + hammingDist f g =
      Fintype.card ι := by
    simpa only [hammingDist, ne_eq, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
        (p := fun i ↦ f i = g i))
  omega

lemma sum_agreementWeight (g : ι → Bool) :
    ∑ f : ι → Bool, agreementWeight f g = 5 ^ Fintype.card ι := by
  classical
  unfold agreementWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) ↦ if b = g i then (4 : ℕ) else 1)]
  have h (i : ι) : (∑ b : Bool, if b = g i then (4 : ℕ) else 1) = 5 := by
    cases g i <;> norm_num [Fintype.sum_bool]
  simp_rw [h]
  simp

/-- An integer Chernoff bound, requiring no entropy or asymptotic estimates. -/
theorem card_hammingBall_weighted (g : ι → Bool) (r : ℕ) :
    (hammingBall g r).card * 4 ^ (Fintype.card ι - r) ≤ 5 ^ Fintype.card ι := by
  classical
  calc
    _ = ∑ f ∈ hammingBall g r, 4 ^ (Fintype.card ι - r) := by simp
    _ ≤ ∑ f ∈ hammingBall g r, agreementWeight f g := by
      apply Finset.sum_le_sum
      intro f hf
      rw [agreementWeight_eq]
      apply Nat.pow_le_pow_right (by omega : 0 < 4)
      have hd : hammingDist f g ≤ r := (Finset.mem_filter.mp hf).2
      omega
    _ ≤ ∑ f : ι → Bool, agreementWeight f g :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := sum_agreementWeight g

/-- Fewer than half-exponentially many words lie within one-sixteenth errors. -/
theorem card_hammingBall_lt_half {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card ι = 16 * m) (g : ι → Bool) :
    (hammingBall g m).card < 2 ^ (8 * m) := by
  have h := card_hammingBall_weighted g m
  rw [hcard, show 16 * m - m = 15 * m by omega] at h
  have hstrict : (5 : ℕ) ^ (16 * m) < 2 ^ (38 * m) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hid : 2 ^ (8 * m) * 4 ^ (15 * m) = (2 : ℕ) ^ (38 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  by_contra hn
  have hle := Nat.mul_le_mul_right (4 ^ (15 * m)) (Nat.le_of_not_gt hn)
  rw [hid] at hle
  omega

def nearbyTables (G : Finset (ι → Bool)) (r : ℕ) : Finset (ι → Bool) :=
  G.biUnion fun g ↦ hammingBall g r

/-- Half-exponentially many centers cannot cover the cube by these balls. -/
theorem card_nearbyTables_lt {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card ι = 16 * m) (G : Finset (ι → Bool))
    (hG : G.card ≤ 2 ^ (8 * m)) :
    (nearbyTables G m).card < 2 ^ (16 * m) := by
  classical
  have hB : 0 < (2 : ℕ) ^ (8 * m) := by positivity
  have hsmall : (2 : ℕ) ^ (8 * m) - 1 < 2 ^ (8 * m) := Nat.sub_lt hB (by omega)
  calc
    _ ≤ ∑ g ∈ G, (hammingBall g m).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ G, (2 ^ (8 * m) - 1) := by
      apply Finset.sum_le_sum
      intro g _
      exact Nat.le_sub_one_of_lt (card_hammingBall_lt_half hm hcard g)
    _ = G.card * (2 ^ (8 * m) - 1) := by simp
    _ ≤ 2 ^ (8 * m) * (2 ^ (8 * m) - 1) := Nat.mul_le_mul_right _ hG
    _ < 2 ^ (8 * m) * 2 ^ (8 * m) := Nat.mul_lt_mul_of_pos_left hsmall hB
    _ = 2 ^ (16 * m) := by rw [← pow_add]; congr 1; omega

open RelativeMarginQuantifiers MarginCapacityEstimates

/-- The approximation is of truth tables, and its center is an actual genuine
comparison-width representation satisfying the full-cube relative-margin bound. -/
def HasApproximateMarginRepair (n H K r : ℕ) (gamma : ℝ) : Prop :=
  ∀ f, computableWithHeadsN n H f → ∃ g,
    HasRelativeMargin n K g gamma ∧ hammingDist f g ≤ r

/-- Unrestricted lower-bound interface requiring only 15/16 agreement. -/
theorem worstCase_gt_of_approximate_repair {n H K : ℕ} {gamma : ℝ}
    (hn : 4 ≤ n)
    (hhigh : (highMarginFunctions n K gamma).ncard ≤ 2 ^ (2 ^ (n - 1)))
    (hrepair : HasApproximateMarginRepair n H K (2 ^ (n - 4)) gamma) :
    H < worstCaseHeadComplexity n := by
  classical
  let G := (highMarginFunctions n K gamma).toFinset
  have hm : 0 < (2 : ℕ) ^ (n - 4) := by positivity
  have hN : (2 : ℕ) ^ n = 16 * 2 ^ (n - 4) := by
    rw [show n = 4 + (n - 4) by omega, pow_add]
    norm_num
  have hhalf : (2 : ℕ) ^ (n - 1) = 8 * 2 ^ (n - 4) := by
    rw [show n - 1 = 3 + (n - 4) by omega, pow_add]
    norm_num
  have hG : G.card ≤ 2 ^ (8 * 2 ^ (n - 4)) := by
    simpa only [G, ← Set.ncard_eq_toFinset_card', hhalf] using hhigh
  have hc : (nearbyTables G (2 ^ (n - 4))).card < 2 ^ (2 ^ n) := by
    rw [hN]
    apply card_nearbyTables_lt hm _ G hG
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hN
  have hsub : headComputableFunctions n H ⊆
      (nearbyTables G (2 ^ (n - 4)) : Set ((Fin n → Bool) → Bool)) := by
    intro f hf
    obtain ⟨g, hg, hdist⟩ := hrepair f hf
    change f ∈ nearbyTables G (2 ^ (n - 4))
    simp only [nearbyTables, Finset.mem_biUnion]
    refine ⟨g, ?_, ?_⟩
    · change g ∈ (highMarginFunctions n K gamma).toFinset
      exact Set.mem_toFinset.mpr hg
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩
  have hcount : (headComputableFunctions n H).ncard < 2 ^ (2 ^ n) := by
    exact (Set.ncard_le_ncard hsub).trans_lt (by simpa using hc)
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt hcount
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

/-- Square-root scale, with the same audited constant and width overhead. -/
theorem worstCase_gt_sqrt_of_approximate_repair {n H B : ℕ} {C : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n))
    (hrepair : HasApproximateMarginRepair n H (⌈C * (H : ℝ)⌉₊ + B)
      (2 ^ (n - 4)) (Real.exp (-Real.exp (Real.sqrt n)))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_approximate_repair (by omega)
    (card_highMargin_sqrt_overhead hn hC hoverhead hwidth) hrepair

/-- Logarithmic fallback scale, with the corresponding double exponential. -/
theorem worstCase_gt_logarithmic_of_approximate_repair {n H B : ℕ} {C : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2))
    (hrepair : HasApproximateMarginRepair n H (⌈C * (H : ℝ)⌉₊ + B)
      (2 ^ (n - 4)) (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_approximate_repair (by omega)
    (card_highMargin_logarithmic_overhead hn hC hoverhead hwidth) hrepair

theorem real_sqrt_bound_of_approximate_repair {n B : ℕ} {C : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hrepair : HasApproximateMarginRepair n
      ⌊(2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)⌋₊
      (⌈C * (⌊(2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)⌋₊ : ℝ)⌉₊ + B)
      (2 ^ (n - 4)) (Real.exp (-Real.exp (Real.sqrt n)))) :
    (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n) < worstCaseHeadComplexity n := by
  apply Nat.lt_of_floor_lt
  apply worstCase_gt_sqrt_of_approximate_repair hn hC hoverhead _ hrepair
  apply Nat.floor_le
  positivity

theorem real_logarithmic_bound_of_approximate_repair {n B : ℕ} {C : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hrepair : HasApproximateMarginRepair n
      ⌊(2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)⌋₊
      (⌈C * (⌊(2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)⌋₊ : ℝ)⌉₊ + B)
      (2 ^ (n - 4)) (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))) :
    (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2) < worstCaseHeadComplexity n := by
  apply Nat.lt_of_floor_lt
  apply worstCase_gt_logarithmic_of_approximate_repair hn hC hoverhead _ hrepair
  apply Nat.floor_le
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  positivity

end HeadComplexity.ApproximateMarginCounting
