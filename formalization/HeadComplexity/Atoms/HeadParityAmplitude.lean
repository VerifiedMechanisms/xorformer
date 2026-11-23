import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option linter.style.header false

/-! Exact alternating-sum bounds for bounded coherent affine ratios.
This is an amplitude obstruction, not a head-count lower bound. -/
noncomputable section

namespace HeadComplexity.HeadParityAmplitude
open scoped BigOperators
open MeasureTheory Set
variable {I : Type*} [DecidableEq I]

def moment (w : I → ℝ) (s : Finset I) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ)^t.card / (1+∑ i ∈ t, w i)

def kernel (w : I → ℝ) (s : Finset I) (x : ℝ) : ℝ :=
  ∏ i ∈ s, (1-x^(w i))

lemma kernel_continuous (w : I → ℝ) (s : Finset I)
    (hw : ∀ i, 0 ≤ w i) : Continuous (kernel w s) := by
  unfold kernel
  exact continuous_finsetProd _ fun i _ ↦
    continuous_const.sub (Real.continuous_rpow_const (hw i))

lemma kernel_bounds (w : I → ℝ) (s : Finset I)
    (hw : ∀ i, 0 ≤ w i) {x : ℝ} (hx : x ∈ Icc 0 1) :
    0 ≤ kernel w s x ∧ kernel w s x ≤ 1 := by
  have hi (i : I) : 0 ≤ 1-x^(w i) ∧ 1-x^(w i) ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.rpow_le_one hx.1 hx.2 (hw i))
    · linarith [Real.rpow_nonneg hx.1 (w i)]
  constructor
  · exact Finset.prod_nonneg fun i _ ↦ (hi i).1
  · exact Finset.prod_le_one₀ (fun i _ ↦ (hi i).1) (fun i _ ↦ (hi i).2)

lemma kernel_expand (w : I → ℝ) (s : Finset I)
    (hw : ∀ i, 0 ≤ w i) {x : ℝ} (hx : 0 ≤ x) :
    kernel w s x = ∑ t ∈ s.powerset, (-1 : ℝ)^t.card * x^(∑ i ∈ t, w i) := by
  unfold kernel
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.prod_const_one, mul_one]
  rw [Real.rpow_sum_of_nonneg hx (fun i _ ↦ hw i)]

lemma moment_integral (w : I → ℝ) (s : Finset I)
    (hw : ∀ i, 0 ≤ w i) :
    moment w s = ∫ x in (0 : ℝ)..1, kernel w s x := by
  have hint (t : Finset I) : IntervalIntegrable
      (fun x : ℝ ↦ (-1 : ℝ)^t.card * x^(∑ i ∈ t, w i)) volume 0 1 :=
    (continuous_const.mul (Real.continuous_rpow_const
      (Finset.sum_nonneg fun i _ ↦ hw i))).intervalIntegrable _ _
  have heq : (∫ x in (0 : ℝ)..1, kernel w s x) =
      ∫ x in (0 : ℝ)..1, ∑ t ∈ s.powerset, (-1 : ℝ)^t.card * x^(∑ i ∈ t, w i) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact kernel_expand w s hw (by simpa using hx.1)
  rw [heq, intervalIntegral.integral_finsetSum (fun t _ ↦ hint t)]
  unfold moment
  apply Finset.sum_congr rfl
  intro t ht
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (show (-1 : ℝ) < ∑ i ∈ t, w i from by
      have := Finset.sum_nonneg (s := t) (fun i _ ↦ hw i)
      linarith))]
  have hp : (∑ i ∈ t, w i)+1 ≠ 0 := by
    have := Finset.sum_nonneg (s := t) (fun i _ ↦ hw i)
    linarith
  simp [Real.zero_rpow hp, add_comm, div_eq_mul_inv]

lemma moment_bounds (w : I → ℝ) (s : Finset I)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ moment w s ∧ moment w s ≤ 1 := by
  rw [moment_integral w s hw]
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx ↦ (kernel_bounds w s hw hx).1)
  · calc
      _ ≤ ∫ _x in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          ((kernel_continuous w s hw).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1)
          (fun x hx ↦ (kernel_bounds w s hw hx).2)
      _ = 1 := by norm_num

lemma moment_le_erase (w : I → ℝ) (s : Finset I)
    (hw : ∀ i, 0 ≤ w i) (i : I) : moment w s ≤ moment w (s.erase i) := by
  by_cases hi : i ∈ s
  · rw [moment_integral w s hw, moment_integral w (s.erase i) hw]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((kernel_continuous w s hw).intervalIntegrable 0 1)
      ((kernel_continuous w (s.erase i) hw).intervalIntegrable 0 1)
    intro x hx
    have hprod : kernel w s x = (1-x^(w i))*kernel w (s.erase i) x := by
      unfold kernel
      exact (Finset.mul_prod_erase _ _ hi).symm
    rw [hprod]
    have hnon := (kernel_bounds w (s.erase i) hw hx).1
    have hp := Real.rpow_nonneg hx.1 (w i)
    nlinarith
  · simp [Finset.erase_eq_of_notMem hi]

def alternatingRatio (w a : I → ℝ) (a₀ : ℝ) (s : Finset I) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
    ((a₀+∑ i ∈ t, a i)/(1+∑ i ∈ t, w i))

lemma absent_powerset (s : Finset I) (i : I) :
    s.powerset.filter (fun t ↦ i ∉ t) = (s.erase i).powerset := by
  ext t
  simp [Finset.subset_erase]

lemma present_moment (w : I → ℝ) (s : Finset I) (i : I) :
    (∑ t ∈ s.powerset.filter (fun t ↦ i ∈ t),
      (-1 : ℝ)^t.card/(1+∑ j ∈ t, w j)) = moment w s-moment w (s.erase i) := by
  have h := Finset.sum_filter_add_sum_filter_not s.powerset (fun t ↦ i ∈ t)
    (fun t ↦ (-1 : ℝ)^t.card/(1+∑ j ∈ t, w j))
  rw [absent_powerset] at h
  unfold moment
  linarith

lemma powerset_weighted_sum (s : Finset I) (a : I → ℝ) (v : Finset I → ℝ) :
    (∑ t ∈ s.powerset, v t * ∑ i ∈ t, a i) =
      ∑ i ∈ s, a i * ∑ t ∈ s.powerset.filter (fun t ↦ i ∈ t), v t := by
  have ht (t : Finset I) (h : t ∈ s.powerset) :
      (∑ i ∈ t, a i) = ∑ i ∈ s, if i ∈ t then a i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    have hsub := Finset.mem_powerset.mp h
    simp only [Finset.mem_filter]
    exact ⟨fun hi ↦ ⟨hsub hi, hi⟩, fun hi ↦ hi.2⟩
  calc
    _ = ∑ t ∈ s.powerset, v t * ∑ i ∈ s, if i ∈ t then a i else 0 := by
      apply Finset.sum_congr rfl
      intro t ht'
      rw [ht t ht']
    _ = ∑ i ∈ s, ∑ t ∈ s.powerset, v t * (if i ∈ t then a i else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht'
      split_ifs <;> ring

lemma alternatingRatio_eq (w a : I → ℝ) (a₀ : ℝ) (s : Finset I) :
    alternatingRatio w a a₀ s = a₀*moment w s-
      ∑ i ∈ s, a i*(moment w (s.erase i)-moment w s) := by
  unfold alternatingRatio
  have hex (t : Finset I) : (-1 : ℝ)^t.card *
      ((a₀+∑ i ∈ t, a i)/(1+∑ i ∈ t, w i)) =
        a₀*((-1 : ℝ)^t.card/(1+∑ i ∈ t, w i))+
        ((-1 : ℝ)^t.card/(1+∑ i ∈ t, w i))*(∑ i ∈ t, a i) := by ring
  simp_rw [hex]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, powerset_weighted_sum]
  simp_rw [present_moment]
  change a₀*moment w s + _ = _
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma moment_balance (w : I → ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s, w i*(moment w (s.erase i)-moment w s)) = moment w s := by
  have hz : alternatingRatio w w 1 s = 0 := by
    unfold alternatingRatio
    have hD (t : Finset I) : 1+∑ i ∈ t, w i ≠ 0 := by
      have := Finset.sum_nonneg (s := t) (fun i _ ↦ hw i)
      linarith
    simp only [div_self (hD _), mul_one]
    exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
  rw [alternatingRatio_eq, one_mul] at hz
  linarith

theorem moment_lt_one (w : I → ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i) : moment w s < 1 := by
  by_contra h
  have he : moment w s = 1 := le_antisymm (moment_bounds w s hw).2 (le_of_not_gt h)
  have hd (i : I) : moment w (s.erase i)-moment w s = 0 := by
    have hu := (moment_bounds w (s.erase i) hw).2
    have hl := moment_le_erase w s hw i
    linarith
  have hb := moment_balance w s hs hw
  simp only [hd, mul_zero, Finset.sum_const_zero] at hb
  rw [he] at hb
  norm_num at hb

def meanPoint (w : I → ℝ) (s : Finset I) (i : I) : ℝ :=
  (moment w (s.erase i)-moment w s)/(1-moment w s)

theorem meanPoint_bounds (w : I → ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i) (i : I) :
    0 ≤ meanPoint w s i ∧ meanPoint w s i ≤ 1 := by
  have hp : 0 < 1-moment w s := sub_pos.mpr (moment_lt_one w s hs hw)
  unfold meanPoint
  constructor
  · exact div_nonneg (sub_nonneg.mpr (moment_le_erase w s hw i)) hp.le
  · apply (div_le_one hp).mpr
    have := (moment_bounds w (s.erase i) hw).2
    linarith

/-- Exact finite mean-value identity; the cube point depends only on the denominator. -/
theorem alternatingRatio_mean_value (w a : I → ℝ) (a₀ : ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i) :
    alternatingRatio w a a₀ s = a₀-
      (a₀+∑ i ∈ s, a i*meanPoint w s i)/(1+∑ i ∈ s, w i*meanPoint w s i) := by
  let K := moment w s
  let B := ∑ i ∈ s, a i*(moment w (s.erase i)-K)
  have hp : 0 < 1-K := sub_pos.mpr (moment_lt_one w s hs hw)
  have hwz : (∑ i ∈ s, w i*meanPoint w s i) = K/(1-K) := by
    unfold meanPoint
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, moment_balance w s hs hw]
  have haz : (∑ i ∈ s, a i*meanPoint w s i) = B/(1-K) := by
    unfold meanPoint
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
  rw [alternatingRatio_eq, hwz, haz]
  change a₀*K-B = a₀-(a₀+B/(1-K))/(1+K/(1-K))
  have hd : 1+K/(1-K) = 1/(1-K) := by field_simp; ring
  rw [hd]
  field_simp
  ring

/-- A lower bound on the ratio controls its alternating sum from above. -/
theorem alternatingRatio_upper (w a : I → ℝ) (a₀ : ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i)
    (hlo : ∀ t ⊆ s, -(1+∑ i ∈ t, w i) ≤ a₀+∑ i ∈ t, a i) :
    alternatingRatio w a a₀ s ≤ a₀+1 := by
  let q : I → ℝ := fun i ↦ max (-a i-w i) 0
  let bad := s.filter (fun i ↦ a i+w i < 0)
  have hq (i : I) : 0 ≤ q i := le_max_right _ _
  have hqsum : (∑ i ∈ s, q i) ≤ a₀+1 := by
    have hb := hlo bad (Finset.filter_subset _ _)
    have he : (∑ i ∈ s, q i) = -(∑ i ∈ bad, (a i+w i)) := by
      rw [← Finset.sum_neg_distrib]
      dsimp [bad]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : a i+w i < 0
      · simp only [h, if_true, q]
        rw [max_eq_left (by linarith)]
        ring
      · simp only [h, if_false, q]
        rw [max_eq_right (by linarith)]
    rw [he, Finset.sum_add_distrib]
    linarith
  let K := moment w s
  let d : I → ℝ := fun i ↦ moment w (s.erase i)-K
  have hK : 0 ≤ K ∧ K ≤ 1 := moment_bounds w s hw
  have hd (i : I) : 0 ≤ d i := sub_nonneg.mpr (moment_le_erase w s hw i)
  have hdu (i : I) : d i ≤ 1-K := by
    have := (moment_bounds w (s.erase i) hw).2
    dsimp [d]
    linarith
  have hbalance : (∑ i ∈ s, w i*d i) = K := moment_balance w s hs hw
  have hlterm (i : I) : -(a i*d i) ≤ w i*d i+q i*d i := by
    have hm := le_max_left (-a i-w i) 0
    have hp := mul_le_mul_of_nonneg_right hm (hd i)
    dsimp [q]
    nlinarith
  have hl := Finset.sum_le_sum (s := s) (fun i _ ↦ hlterm i)
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, hbalance] at hl
  have hqterm : (∑ i ∈ s, q i*d i) ≤ (1-K)*(∑ i ∈ s, q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have := mul_le_mul_of_nonneg_left (hdu i) (hq i)
    nlinarith
  have hqs := mul_le_mul_of_nonneg_left hqsum (sub_nonneg.mpr hK.2)
  rw [alternatingRatio_eq]
  change a₀*K-∑ i ∈ s, a i*d i ≤ a₀+1
  nlinarith

/-- The alternating sum differs from the origin value by at most one. -/
theorem alternatingRatio_centered_bound (w a : I → ℝ) (a₀ : ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i)
    (hbound : ∀ t ⊆ s, |a₀+∑ i ∈ t, a i| ≤ 1+∑ i ∈ t, w i) :
    |alternatingRatio w a a₀ s-a₀| ≤ 1 := by
  have hu := alternatingRatio_upper w a a₀ s hs hw
    (fun t ht ↦ (abs_le.mp (hbound t ht)).1)
  have hn := alternatingRatio_upper w (fun i ↦ -a i) (-a₀) s hs hw
    (fun t ht ↦ by
      rw [Finset.sum_neg_distrib]
      have := (abs_le.mp (hbound t ht)).2
      linarith)
  have he : alternatingRatio w (fun i ↦ -a i) (-a₀) s =
      -alternatingRatio w a a₀ s := by
    unfold alternatingRatio
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_neg_distrib]
    ring
  rw [he] at hn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A bounded coherent affine ratio has unnormalized full parity coefficient at most two. -/
theorem alternatingRatio_abs_le_two (w a : I → ℝ) (a₀ : ℝ) (s : Finset I)
    (hs : s.Nonempty) (hw : ∀ i, 0 ≤ w i)
    (hbound : ∀ t ⊆ s, |a₀+∑ i ∈ t, a i| ≤ 1+∑ i ∈ t, w i) :
    |alternatingRatio w a a₀ s| ≤ 2 := by
  have hc := alternatingRatio_centered_bound w a a₀ s hs hw hbound
  have hzero : |a₀| ≤ 1 := by simpa using hbound ∅ (Finset.empty_subset s)
  calc
    _ = |(alternatingRatio w a a₀ s-a₀)+a₀| := by ring_nf
    _ ≤ |alternatingRatio w a a₀ s-a₀|+|a₀| := abs_add_le _ _
    _ ≤ 2 := by linarith

theorem positive_affine_ratio_bound (w a : I → ℝ) (c a₀ : ℝ) (s : Finset I)
    (hs : s.Nonempty) (hc : 0 < c) (hw : ∀ i, 0 ≤ w i)
    (hbound : ∀ t ⊆ s, |(a₀+∑ i ∈ t, a i)/(c+∑ i ∈ t, w i)| ≤ 1) :
    |∑ t ∈ s.powerset, (-1 : ℝ)^t.card *
      ((a₀+∑ i ∈ t, a i)/(c+∑ i ∈ t, w i))| ≤ 2 := by
  let w' : I → ℝ := fun i ↦ w i/c
  let a' : I → ℝ := fun i ↦ a i/c
  have hw' (i : I) : 0 ≤ w' i := div_nonneg (hw i) hc.le
  have hd (t : Finset I) : 0 < 1+∑ i ∈ t, w' i := by
    have := Finset.sum_nonneg (s := t) (fun i _ ↦ hw' i)
    linarith
  have he (t : Finset I) : (a₀/c+∑ i ∈ t, a' i)/(1+∑ i ∈ t, w' i) =
      (a₀+∑ i ∈ t, a i)/(c+∑ i ∈ t, w i) := by
    dsimp [a', w']
    rw [← Finset.sum_div, ← Finset.sum_div]
    field_simp
  have hb : ∀ t ⊆ s, |a₀/c+∑ i ∈ t, a' i| ≤ 1+∑ i ∈ t, w' i := by
    intro t ht
    have h := hbound t ht
    rw [← he t, abs_div, abs_of_pos (hd t)] at h
    exact (div_le_one (hd t)).mp h
  have h := alternatingRatio_abs_le_two w' a' (a₀/c) s hs hw' hb
  unfold alternatingRatio at h
  simp_rw [he] at h
  exact h

#print axioms moment_integral
#print axioms moment_bounds
#print axioms moment_le_erase
#print axioms alternatingRatio_eq
#print axioms moment_balance
#print axioms alternatingRatio_upper
#print axioms alternatingRatio_centered_bound
#print axioms alternatingRatio_abs_le_two
#print axioms positive_affine_ratio_bound
#print axioms moment_lt_one
#print axioms meanPoint_bounds
#print axioms alternatingRatio_mean_value
end HeadComplexity.HeadParityAmplitude
