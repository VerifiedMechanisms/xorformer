import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Lagrange

set_option linter.style.header false

/-!
Analytic verification of the fixed-radial moment comparison.
This file concerns fixed coefficients only. It makes no assertion that an
arbitrary original-model representation has a sign-preserving radial reduction.
-/
noncomputable section

namespace HeadComplexity.RadialMomentTransfer

open Filter Finset Asymptotics
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι]

def moment (a C : ι → ℝ) (k : ℕ) : ℝ := ∑ h, a h * C h ^ k

def reciprocal (a C : ι → ℝ) (B t : ℝ) : ℝ := ∑ h, a h / (B - t * C h)

def exponential (a C : ι → ℝ) (t : ℝ) : ℝ := ∑ h, a h * Real.exp (t * C h)

/-- Exact geometric remainder, with no asymptotic interchange. -/
lemma reciprocal_remainder (B C t : ℝ) (k : ℕ) (hB : B ≠ 0)
    (hD : B - t * C ≠ 0) :
    1/(B-t*C) = (∑ j ∈ range k, C^j/B^(j+1)*t^j) +
      t^k * (C^k/B^k) / (B-t*C) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, ih, pow_succ]
      have hBk : B^k ≠ 0 := pow_ne_zero _ hB
      field_simp
      ring

lemma reciprocal_moment_remainder (a C : ι → ℝ) (B t : ℝ) (k : ℕ)
    (hB : B ≠ 0) (hD : ∀ h, B - t * C h ≠ 0) :
    reciprocal a C B t =
      (∑ j ∈ range k, moment a C j / B^(j+1)*t^j) +
      t^k * ∑ h, (a h * C h^k / B^k)/(B-t*C h) := by
  unfold reciprocal moment
  simp_rw [show ∀ h, a h / (B-t*C h) = a h * (1/(B-t*C h)) by
    intro h; ring, reciprocal_remainder B _ t k hB (hD _), mul_add]
  rw [sum_add_distrib]
  congr 1
  · simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [sum_div, sum_mul]
    apply sum_congr rfl
    intro h hh
    ring
  · rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    ring

lemma exponential_remainder (C : ℝ) (k : ℕ) :
    (fun t : ℝ => Real.exp (t*C) -
      ∑ j ∈ range (k+1), (t*C)^j/(j.factorial : ℝ)) =o[𝓝 0] (fun t => t^k) := by
  have hcomp : Tendsto (fun t : ℝ => t*C) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.mul_const C : Tendsto (fun t : ℝ => t*C) (𝓝 0) (𝓝 (0*C)))
  have h := (Real.exp_sub_sum_range_succ_isLittleO_pow k).comp_tendsto hcomp
  have hb : (fun t : ℝ => (t*C)^k) =O[𝓝 0] (fun t => t^k) := by
    simpa [mul_pow, mul_comm] using (isBigO_refl (fun t : ℝ => t^k) (𝓝 0)).const_mul_left (C^k)
  exact h.trans_isBigO hb

lemma exponential_moment_remainder (a C : ι → ℝ) (k : ℕ) :
    (fun t : ℝ => exponential a C t -
      ∑ j ∈ range (k+1), moment a C j/(j.factorial : ℝ)*t^j) =o[𝓝 0] (fun t => t^k) := by
  have hh : ∀ h ∈ (univ : Finset ι),
      (fun t : ℝ => a h * (Real.exp (t*C h) -
        ∑ j ∈ range (k+1), (t*C h)^j/(j.factorial : ℝ))) =o[𝓝 0] (fun t => t^k) := by
    intro h _
    exact (exponential_remainder (C h) k).const_mul_left (a h)
  have hs := IsLittleO.sum hh
  convert hs using 1
  funext t
  simp only [Finset.sum_apply, mul_sub, sum_sub_distrib, exponential]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  simp only [moment, sum_div, sum_mul, mul_pow]
  apply sum_congr rfl
  intro h hh
  ring


lemma reciprocal_scaled_limit (a C : ι → ℝ) (B : ℝ) (k : ℕ) (hB : B ≠ 0)
    (hzero : ∀ j < k, moment a C j = 0) :
    Tendsto (fun t : ℝ => reciprocal a C B t / t^k) (𝓝[>] 0)
      (𝓝 (moment a C k / B^(k+1))) := by
  have hden : ∀ᶠ t : ℝ in 𝓝 0, ∀ h, B-t*C h ≠ 0 := by
    rw [Filter.eventually_all]
    intro h
    have hc : ContinuousAt (fun t : ℝ => B-t*C h) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hB)
  have hlim : Tendsto (fun t : ℝ => ∑ h, (a h*C h^k/B^k)/(B-t*C h))
      (𝓝 0) (𝓝 (moment a C k/B^(k+1))) := by
    have ht (h : ι) : Tendsto (fun t : ℝ => (a h*C h^k/B^k)/(B-t*C h))
        (𝓝 0) (𝓝 ((a h*C h^k/B^k)/B)) := by
      have hc : ContinuousAt (fun t : ℝ => (a h*C h^k/B^k)/(B-t*C h)) 0 := by
        apply ContinuousAt.div continuousAt_const
        · fun_prop
        · simpa using hB
      simpa using hc.tendsto
    convert tendsto_finsetSum univ (fun h _ => ht h) using 1
    simp only [moment, sum_div, pow_succ]
    congr 1
    apply sum_congr rfl
    intro h hh
    ring
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hden.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht hpos
  have ht0 : t ≠ 0 := ne_of_gt hpos
  rw [reciprocal_moment_remainder a C B t k hB ht]
  have hz : (∑ j ∈ range k, moment a C j / B^(j+1)*t^j) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [hzero j (mem_range.mp hj)]
    simp
  rw [hz, zero_add]
  field_simp

lemma exponential_scaled_limit (a C : ι → ℝ) (k : ℕ)
    (hzero : ∀ j < k, moment a C j = 0) :
    Tendsto (fun t : ℝ => exponential a C t / t^k) (𝓝[>] 0)
      (𝓝 (moment a C k/(k.factorial : ℝ))) := by
  have h := (exponential_moment_remainder a C k).tendsto_div_nhds_zero
  have heq : ∀ t : ℝ, (∑ j ∈ range (k+1), moment a C j/(j.factorial : ℝ)*t^j) =
      moment a C k/(k.factorial : ℝ)*t^k := by
    intro t
    rw [sum_range_succ]
    have hz : (∑ j ∈ range k, moment a C j/(j.factorial : ℝ)*t^j) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [hzero j (mem_range.mp hj)]
      simp
    rw [hz, zero_add]
  simp_rw [heq] at h
  have h' := (h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).add_const
    (moment a C k/(k.factorial : ℝ))
  simp only [zero_add] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t hpos
  have ht0 : t ≠ 0 := ne_of_gt hpos
  field_simp
  ring


/-- Vanishing of all moments annihilates every function of the fixed shifts.
Repeated shifts are allowed; polynomial interpolation merges them automatically. -/
lemma sum_kernel_eq_zero_of_moments (a C : ι → ℝ)
    (hz : ∀ k, moment a C k = 0) (φ : ℝ → ℝ) :
    ∑ h, a h * φ (C h) = 0 := by
  classical
  obtain ⟨P, hP⟩ := (Polynomial.exists_eval_eq_iff C (fun h => φ (C h))).mpr
    (fun i j hij => congrArg φ hij)
  simp_rw [← hP, Polynomial.eval_eq_sum, Polynomial.sum_def, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro k hk
  calc
    (∑ h, a h * (P.coeff k * C h^k)) = P.coeff k * moment a C k := by
      unfold moment
      rw [mul_sum]
      apply sum_congr rfl
      intro h hh
      ring
    _ = 0 := by rw [hz, mul_zero]

/-- If the fixed mixture has a first nonzero moment, both kernels have the
same strict sign for all sufficiently small positive scales. -/
theorem eventually_product_pos (a C : ι → ℝ) (B : ℝ) (hB : 0 < B)
    (k : ℕ) (hzero : ∀ j < k, moment a C j = 0) (hne : moment a C k ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < reciprocal a C B t * exponential a C t := by
  have hr := reciprocal_scaled_limit a C B k (ne_of_gt hB) hzero
  have he := exponential_scaled_limit a C k hzero
  have hpos : 0 < (moment a C k/B^(k+1))*(moment a C k/(k.factorial : ℝ)) := by
    rw [div_mul_div_comm]
    exact div_pos (mul_self_pos.mpr hne)
      (mul_pos (pow_pos hB _) (Nat.cast_pos.mpr (Nat.factorial_pos k)))
  have hp := (hr.mul he).eventually_const_lt hpos
  filter_upwards [hp, self_mem_nhdsWithin] with t ht htp
  have ht0 : t ≠ 0 := ne_of_gt htp
  have hk : 0 < t^k := pow_pos htp k
  have h := mul_pos ht (mul_pos hk hk)
  convert h using 1
  field_simp

/-- Cancellation-robust fixed-radial comparison, including mixtures which
vanish identically. The coefficients cannot depend on the scale. -/
theorem eventually_same_sign_or_zero (a C : ι → ℝ) (B : ℝ) (hB : 0 < B) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (0 < reciprocal a C B t * exponential a C t) ∨
      (reciprocal a C B t = 0 ∧ exponential a C t = 0) := by
  classical
  by_cases hz : ∀ k, moment a C k = 0
  · apply Eventually.of_forall
    intro t
    right
    constructor
    · simpa [reciprocal, div_eq_mul_inv] using
        sum_kernel_eq_zero_of_moments a C hz (fun z => (B-t*z)⁻¹)
    · exact sum_kernel_eq_zero_of_moments a C hz (fun z => Real.exp (t*z))
  · push Not at hz
    let k := Nat.find hz
    have hn : moment a C k ≠ 0 := Nat.find_spec hz
    have hl : ∀ j < k, moment a C j = 0 := by
      intro j hj
      exact not_ne_iff.mp (Nat.find_min hz hj)
    exact (eventually_product_pos a C B hB k hl hn).mono (fun _ h => Or.inl h)


lemma sign_eq_of_product_pos {u v : ℝ} (h : 0 < u * v) :
    SignType.sign u = SignType.sign v := by
  rcases mul_pos_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [sign_pos hu, sign_pos hv]
  · rw [sign_neg hu, sign_neg hv]

/-- One scale works on an arbitrary finite set, at every cancellation order. -/
theorem uniform_kernel_sign_transfer {X : Type*} [Finite X]
    (a C : X → ι → ℝ) (B : X → ℝ) (hB : ∀ x, 0 < B x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → ∀ x,
      (∀ h, 0 < B x-t*C x h) ∧
      SignType.sign (reciprocal (a x) (C x) (B x) t) =
        SignType.sign (exponential (a x) (C x) t) := by
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x,
      (∀ h, 0 < B x-t*C x h) ∧
      SignType.sign (reciprocal (a x) (C x) (B x) t) =
        SignType.sign (exponential (a x) (C x) t) := by
    rw [Filter.eventually_all]
    intro x
    have hd : ∀ᶠ t : ℝ in 𝓝 0, ∀ h, 0 < B x-t*C x h := by
      rw [Filter.eventually_all]
      intro h
      have hc : ContinuousAt (fun t : ℝ => B x-t*C x h) 0 := by fun_prop
      exact hc.tendsto.eventually_const_lt (by simpa using hB x)
    filter_upwards [hd.filter_mono nhdsWithin_le_nhds,
      eventually_same_sign_or_zero (a x) (C x) (B x) (hB x)] with t ht hs
    refine ⟨ht, ?_⟩
    rcases hs with h | ⟨hr, he⟩
    · exact sign_eq_of_product_pos h
    · rw [hr, he]
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨ε, hε, fun t ht hte => hsub ⟨?_, ht⟩⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hte

/-- The written fixed-radial theorem, including its arbitrary fixed bias.
There are no coherence, distinctness, margin, or noncancellation assumptions.
All numerator and shift functions are fixed independently of the scale. -/
theorem uniform_radial_sign_transfer {X : Type*} [Finite X]
    (A C : X → ι → ℝ) (B : X → ℝ) (c : ℝ) (hB : ∀ x, 0 < B x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → ∀ x,
      (∀ h, 0 < B x+t*C x h) ∧
      SignType.sign (c + ∑ h, A x h / (B x+t*C x h)) =
        SignType.sign (c*B x + ∑ h, A x h * Real.exp (-t*C x h)) := by
  let a' : X → Option ι → ℝ := fun x h =>
    match h with | none => c*B x | some i => A x i
  let C' : X → Option ι → ℝ := fun x h =>
    match h with | none => 0 | some i => -C x i
  obtain ⟨ε, hε, he⟩ := uniform_kernel_sign_transfer a' C' B hB
  refine ⟨ε, hε, fun t ht hte x => ?_⟩
  obtain ⟨hd, hs⟩ := he t ht hte x
  constructor
  · intro h
    simpa [C'] using hd (some h)
  · simpa [reciprocal, exponential, a', C', Fintype.sum_option,
      ne_of_gt (hB x), mul_neg, neg_mul, add_comm] using hs

#print axioms uniform_radial_sign_transfer
end HeadComplexity.RadialMomentTransfer
