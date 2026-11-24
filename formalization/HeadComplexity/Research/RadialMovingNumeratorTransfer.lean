import HeadComplexity.Research.RadialMomentTransfer
import HeadComplexity.Research.RadialJetAlgebra

set_option linter.style.header false

/-!
Bounded polynomial numerator motion in fixed radial denominator directions.
This is an auxiliary transfer theorem; it supplies no reduction of arbitrary
original-model representations to this class.
-/
noncomputable section
namespace HeadComplexity.RadialMovingNumeratorTransfer

open Filter Finset
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι]

def polynomialTail (d : ℕ → ℝ) (r : ℕ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∑ j ∈ range r, d j * t^j) + t^r * g t

lemma polynomialTail_scaled_limit (d : ℕ → ℝ) (r k : ℕ) (g : ℝ → ℝ)
    (hk : k < r) (hz : ∀ j < k, d j = 0) (hg : ContinuousAt g 0) :
    Tendsto (fun t : ℝ => polynomialTail d r g t / t^k) (𝓝[>] 0) (𝓝 (d k)) := by
  let q : ℝ → ℝ := fun t => (∑ j ∈ range r, d j * t^(j-k)) + t^(r-k) * g t
  have hq : ContinuousAt q 0 := by
    dsimp [q]
    fun_prop
  have hq0 : q 0 = d k := by
    dsimp [q]
    have hrk : r-k ≠ 0 := by omega
    rw [zero_pow hrk, zero_mul, add_zero]
    rw [sum_eq_single k]
    · simp
    · intro j hj hne
      by_cases hjk : j < k
      · simp [hz j hjk]
      · have hkj : k < j := by omega
        simp [zero_pow (show j-k ≠ 0 by omega)]
    · intro h
      exact (h (mem_range.mpr hk)).elim
  have ht := hq.tendsto
  rw [hq0] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t htp
  have ht0 : t ≠ 0 := ne_of_gt htp
  dsimp [q, polynomialTail]
  rw [add_div, sum_div]
  congr 1
  · apply sum_congr rfl
    intro j hj
    by_cases hjk : j < k
    · simp [hz j hjk]
    · rw [mul_div_assoc, pow_sub₀ t ht0 (by omega : k ≤ j), div_eq_mul_inv]
  · rw [show t^r * g t / t^k = (t^r/t^k)*g t by ring,
      pow_sub₀ t ht0 (by omega : k ≤ r), div_eq_mul_inv]

lemma lowPart_eq_sum (a : ℕ → ℝ) (B C t : ℝ) (r : ℕ) :
    RadialJetAlgebra.lowPart a B C t r =
      ∑ j ∈ range r, B^(r-1-j) * RadialJetAlgebra.moment a B C j * t^j := by
  induction r with
  | zero => simp [RadialJetAlgebra.lowPart]
  | succ r ih =>
      rw [RadialJetAlgebra.lowPart, ih, sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j hj
        have hjr : j < r := mem_range.mp hj
        rw [show r-j = (r-1-j)+1 by omega, pow_succ]
        ring
      · ring

def jetScore (a : ι → ℕ → ℝ) (C : ι → ℝ) (B t : ℝ) (r : ℕ) : ℝ :=
  ∑ h, RadialJetAlgebra.numerator (a h) t r / (B+t*C h)

def jetMoment (a : ι → ℕ → ℝ) (C : ι → ℝ) (B : ℝ) (k : ℕ) : ℝ :=
  ∑ h, RadialJetAlgebra.moment (a h) B (C h) k

def tailWeight (a : ι → ℕ → ℝ) (C : ι → ℝ) (B : ℝ) (r : ℕ) : ι → ℝ :=
  fun h => RadialJetAlgebra.moment (a h) B (C h) r

/-- One polynomial-exponential score, retaining the finite low-order part. -/
def transferScore (a : ι → ℕ → ℝ) (C : ι → ℝ) (B t : ℝ) (r : ℕ) : ℝ :=
  polynomialTail (jetMoment a C B) r
    (RadialMomentTransfer.exponential (tailWeight a C B r) (fun h => -C h)) t

lemma jetScore_decomposition (a : ι → ℕ → ℝ) (C : ι → ℝ) (B t : ℝ) (r : ℕ)
    (hB : B ≠ 0) (hD : ∀ h, B + t * C h ≠ 0) :
    jetScore a C B t r = polynomialTail
      (fun j => jetMoment a C B j / B^(j+1)) r
      (fun t => RadialMomentTransfer.reciprocal (tailWeight a C B r)
        (fun h => -C h) B t / B^r) t := by
  have hh (h : ι) : RadialJetAlgebra.numerator (a h) t r / (B+t*C h) =
      RadialJetAlgebra.lowPart (a h) B (C h) t r / B^r +
      t^r * (RadialJetAlgebra.moment (a h) B (C h) r / (B+t*C h)) / B^r := by
    have hi := RadialJetAlgebra.tail_identity (a h) B (C h) t r
    have hBr : B^r ≠ 0 := pow_ne_zero _ hB
    field_simp [hD h]
    nlinarith [hi]
  unfold jetScore
  simp_rw [hh, lowPart_eq_sum]
  rw [sum_add_distrib]
  unfold polynomialTail
  congr 1
  · simp_rw [sum_div]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    have hjr : j < r := mem_range.mp hj
    unfold jetMoment
    rw [sum_div, sum_mul]
    apply sum_congr rfl
    intro h hh
    have he : r = (r-1-j)+(j+1) := by omega
    rw [show B^r = B^(r-1-j) * B^(j+1) by rw [← pow_add, ← he]]
    have hp : B^(r-1-j) ≠ 0 := pow_ne_zero _ hB
    field_simp
  · simp only [RadialMomentTransfer.reciprocal, tailWeight, mul_neg, sub_neg_eq_add,
      sum_div, mul_sum]
    apply sum_congr rfl
    intro h hh
    ring


lemma jetScore_scaled_limit (a : ι → ℕ → ℝ) (C : ι → ℝ) (B : ℝ) (r k : ℕ)
    (hB : B ≠ 0) (hk : k < r) (hz : ∀ j < k, jetMoment a C B j = 0) :
    Tendsto (fun t : ℝ => jetScore a C B t r / t^k) (𝓝[>] 0)
      (𝓝 (jetMoment a C B k / B^(k+1))) := by
  have hg : ContinuousAt (fun t => RadialMomentTransfer.reciprocal (tailWeight a C B r)
      (fun h => -C h) B t / B^r) 0 := by
    unfold RadialMomentTransfer.reciprocal
    fun_prop (disch := simpa using hB)
  have hlim := polynomialTail_scaled_limit (fun j => jetMoment a C B j / B^(j+1))
    r k _ hk (fun j hj => by rw [hz j hj]; simp) hg
  apply hlim.congr'
  have hd : ∀ᶠ t : ℝ in 𝓝 0, ∀ h, B+t*C h ≠ 0 := by
    rw [Filter.eventually_all]
    intro h
    have hc : ContinuousAt (fun t : ℝ => B+t*C h) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hB)
  filter_upwards [hd.filter_mono nhdsWithin_le_nhds] with t ht
  rw [jetScore_decomposition a C B t r hB ht]

lemma transferScore_scaled_limit (a : ι → ℕ → ℝ) (C : ι → ℝ) (B : ℝ) (r k : ℕ)
    (hk : k < r) (hz : ∀ j < k, jetMoment a C B j = 0) :
    Tendsto (fun t : ℝ => transferScore a C B t r / t^k) (𝓝[>] 0)
      (𝓝 (jetMoment a C B k)) := by
  unfold transferScore
  apply polynomialTail_scaled_limit _ _ _ _ hk hz
  unfold RadialMomentTransfer.exponential
  fun_prop

lemma eventually_product_pos_of_low_moment (a : ι → ℕ → ℝ) (C : ι → ℝ)
    (B : ℝ) (r k : ℕ) (hB : 0 < B) (hk : k < r)
    (hz : ∀ j < k, jetMoment a C B j = 0) (hne : jetMoment a C B k ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < jetScore a C B t r * transferScore a C B t r := by
  have hr := jetScore_scaled_limit a C B r k (ne_of_gt hB) hk hz
  have he := transferScore_scaled_limit a C B r k hk hz
  have hp : 0 < (jetMoment a C B k/B^(k+1))*jetMoment a C B k := by
    rw [div_mul_eq_mul_div]
    exact div_pos (mul_self_pos.mpr hne) (pow_pos hB _)
  have ht := (hr.mul he).eventually_const_lt hp
  filter_upwards [ht, self_mem_nhdsWithin] with t ht htp
  have ht0 : t ≠ 0 := ne_of_gt htp
  have h := mul_pos ht (mul_pos (pow_pos htp k) (pow_pos htp k))
  convert h using 1
  field_simp

lemma eventually_transfer_same_sign_of_low_zero (a : ι → ℕ → ℝ) (C : ι → ℝ)
    (B : ℝ) (r : ℕ) (hB : 0 < B) (hz : ∀ j < r, jetMoment a C B j = 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      SignType.sign (jetScore a C B t r) = SignType.sign (transferScore a C B t r) := by
  have hd : ∀ᶠ t : ℝ in 𝓝 0, ∀ h, B+t*C h ≠ 0 := by
    rw [Filter.eventually_all]
    intro h
    have hc : ContinuousAt (fun t : ℝ => B+t*C h) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using ne_of_gt hB)
  have hs := RadialMomentTransfer.eventually_same_sign_or_zero (tailWeight a C B r)
    (fun h => -C h) B hB
  filter_upwards [hd.filter_mono nhdsWithin_le_nhds, hs, self_mem_nhdsWithin] with t hd hs htp
  have hlow : (∑ j ∈ range r, jetMoment a C B j * t^j) = 0 := by
    apply sum_eq_zero
    intro j hj
    simp [hz j (mem_range.mp hj)]
  have hlow' : (∑ j ∈ range r, (jetMoment a C B j/B^(j+1))*t^j) = 0 := by
    apply sum_eq_zero
    intro j hj
    simp [hz j (mem_range.mp hj)]
  rw [jetScore_decomposition a C B t r (ne_of_gt hB) hd]
  unfold transferScore polynomialTail
  rw [hlow, hlow', zero_add, zero_add]
  rcases hs with hs | ⟨hr, he⟩
  · apply RadialMomentTransfer.sign_eq_of_product_pos
    have hm : 0 < t^r * t^r / B^r := div_pos
      (mul_pos (pow_pos htp _) (pow_pos htp _)) (pow_pos hB _)
    convert mul_pos hm hs using 1; ring
  · simp [hr, he]

/-- Fixed radial directions and any fixed finite numerator polynomial degree.
All cancellation orders in the remaining exponential tail are allowed. -/
theorem eventually_transfer_same_sign (a : ι → ℕ → ℝ) (C : ι → ℝ)
    (B : ℝ) (r : ℕ) (hB : 0 < B) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      SignType.sign (jetScore a C B t r) = SignType.sign (transferScore a C B t r) := by
  classical
  by_cases hex : ∃ k, k < r ∧ jetMoment a C B k ≠ 0
  · let k := Nat.find hex
    have hk : k < r := (Nat.find_spec hex).1
    have hn : jetMoment a C B k ≠ 0 := (Nat.find_spec hex).2
    have hz : ∀ j < k, jetMoment a C B j = 0 := by
      intro j hj
      have hjr : j < r := lt_trans hj hk
      have hm := Nat.find_min hex hj
      exact not_ne_iff.mp (fun h => hm ⟨hjr, h⟩)
    exact (eventually_product_pos_of_low_moment a C B r k hB hk hz hn).mono
      (fun _ h => RadialMomentTransfer.sign_eq_of_product_pos h)
  · have hz : ∀ j < r, jetMoment a C B j = 0 := by
      intro j hj
      exact not_ne_iff.mp (fun h => hex ⟨j, hj, h⟩)
    exact eventually_transfer_same_sign_of_low_zero a C B r hB hz

/-- One positive scale interval works on every point of a finite query set. -/
theorem uniform_moving_numerator_sign_transfer {X : Type*} [Finite X]
    (a : X → ι → ℕ → ℝ) (C : X → ι → ℝ) (B : X → ℝ) (r : ℕ)
    (hB : ∀ x, 0 < B x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → ∀ x,
      (∀ h, 0 < B x+t*C x h) ∧
      SignType.sign (jetScore (a x) (C x) (B x) t r) =
        SignType.sign (transferScore (a x) (C x) (B x) t r) := by
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x,
      (∀ h, 0 < B x+t*C x h) ∧
      SignType.sign (jetScore (a x) (C x) (B x) t r) =
        SignType.sign (transferScore (a x) (C x) (B x) t r) := by
    rw [Filter.eventually_all]
    intro x
    have hd : ∀ᶠ t : ℝ in 𝓝 0, ∀ h, 0 < B x+t*C x h := by
      rw [Filter.eventually_all]
      intro h
      have hc : ContinuousAt (fun t : ℝ => B x+t*C x h) 0 := by fun_prop
      exact hc.tendsto.eventually_const_lt (by simpa using hB x)
    filter_upwards [hd.filter_mono nhdsWithin_le_nhds,
      eventually_transfer_same_sign (a x) (C x) (B x) r (hB x)] with t ht hs
    exact ⟨ht, hs⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨ε, hε, fun t ht hte => hsub ⟨?_, ht⟩⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hte

#print axioms uniform_moving_numerator_sign_transfer
end HeadComplexity.RadialMovingNumeratorTransfer
