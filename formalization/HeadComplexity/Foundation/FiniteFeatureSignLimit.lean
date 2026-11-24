import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Limits of finite-dimensional sign representations

These analytic lemmas isolate the coefficient compactness and dense-grid
sign-limit steps in the three-head separation argument. Polynomial
irreducibility and the construction of the averaged polynomial remain
separate mathematical obligations.
-/

namespace HeadComplexity

open scoped BigOperators Topology
open Filter

/-- Unit-normalized coefficient vectors have a convergent subsequence whose
limit is still nonzero. -/
theorem normalized_coefficients_subsequence {ι : Type*} [Fintype ι]
    (a : ℕ → (ι → ℝ)) (ha : ∀ m, ‖a m‖ = 1) :
    ∃ (c : ι → ℝ) (φ : ℕ → ℕ),
      ‖c‖ = 1 ∧ c ≠ 0 ∧ StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 c) := by
  obtain ⟨c, hc, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ι → ℝ) 1).tendsto_subseq
    (fun m ↦ by simpa only [Metric.mem_sphere, dist_zero_right] using ha m)
  have hnorm : ‖c‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hc
  refine ⟨c, φ, hnorm, ?_, hφ, hlim⟩
  intro hz
  simp [hz] at hnorm

/-- A point of the centered Hamming grid with m+1 replicas. -/
noncomputable def centeredGridApprox (m : ℕ) (q : ℝ) : ℝ :=
  2 * (⌊((m : ℝ) + 1) * (q + 1) / 2⌋₊ : ℝ) / ((m : ℝ) + 1) - 1

theorem centeredGridApprox_mem (m : ℕ) (q : ℝ) (_hqlo : -1 ≤ q) (hqhi : q ≤ 1) :
    ∃ k : ℕ, k ≤ m + 1 ∧ centeredGridApprox m q = 2 * (k : ℝ) / (m + 1) - 1 := by
  refine ⟨⌊((m : ℝ) + 1) * (q + 1) / 2⌋₊, ?_, rfl⟩
  apply Nat.floor_le_of_le
  have hm : 0 ≤ (m : ℝ) + 1 := by positivity
  push_cast
  nlinarith

theorem centeredGridApprox_error (m : ℕ) (q : ℝ) (hq : -1 ≤ q) :
    0 ≤ q - centeredGridApprox m q ∧
      q - centeredGridApprox m q < 2 / ((m : ℝ) + 1) := by
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hqp : 0 ≤ q + 1 := by linarith
  have ha : 0 ≤ ((m : ℝ) + 1) * (q + 1) / 2 := by positivity
  have hfloor := Nat.floor_le ha
  have hlt := Nat.lt_floor_add_one (((m : ℝ) + 1) * (q + 1) / 2)
  unfold centeredGridApprox
  constructor
  · rw [sub_nonneg, sub_le_iff_le_add, div_le_iff₀ hm]
    nlinarith
  · rw [lt_div_iff₀ hm]
    simp only [sub_mul, div_mul_cancel₀ _ hm.ne', one_mul]
    nlinarith

theorem centeredGridApprox_tendsto (q : ℝ) (hq : -1 ≤ q) :
    Tendsto (fun m ↦ centeredGridApprox m q) atTop (𝓝 q) := by
  have hzero : Tendsto (fun m ↦ q - centeredGridApprox m q) atTop (𝓝 0) := by
    apply squeeze_zero (fun m ↦ (centeredGridApprox_error m q hq).1)
      (fun m ↦ (centeredGridApprox_error m q hq).2.le)
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [sub_zero, sub_sub_cancel] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ q) atTop (𝓝 q)).sub hzero

theorem centeredGridApprox_pi_tendsto {ι : Type*} (q : ι → ℝ)
    (hq : ∀ i, -1 ≤ q i) :
    Tendsto (fun m i ↦ centeredGridApprox m (q i)) atTop (𝓝 q) := by
  exact tendsto_pi_nhds.mpr fun i ↦ centeredGridApprox_tendsto (q i) (hq i)

/-- Convergent coefficients and moving evaluation points give convergent
scores for any finite family of continuous features. -/
theorem tendsto_finite_feature_eval {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (F : ι → X → ℝ) (a : ℕ → (ι → ℝ)) (c : ι → ℝ)
    (x : ℕ → X) (y : X)
    (hF : ∀ i, ContinuousAt (F i) y)
    (ha : Tendsto a atTop (𝓝 c)) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun m ↦ ∑ i, a m i * F i (x m)) atTop
      (𝓝 (∑ i, c i * F i y)) := by
  apply tendsto_finsetSum
  intro i _
  exact ((continuous_apply i).continuousAt.tendsto.comp ha).mul
    ((hF i).tendsto.comp hx)

/-- Strict sign agreement along convergent scalar sequences implies weak
sign agreement at every nonzero limit of the reference sequence. -/
theorem weak_sign_of_sequence_limit (p q : ℕ → ℝ) (a b : ℝ)
    (hp : Tendsto p atTop (𝓝 a)) (hq : Tendsto q atTop (𝓝 b))
    (hsign : ∀ m, 0 < q m ↔ 0 < p m) :
    (0 < a → 0 ≤ b) ∧ (a < 0 → b ≤ 0) := by
  constructor
  · intro ha
    have he : ∀ᶠ m in atTop, 0 ≤ q m :=
      (hp.eventually_const_lt ha).mono fun m hm ↦ (hsign m).mpr hm |>.le
    exact ge_of_tendsto hq he
  · intro ha
    have he : ∀ᶠ m in atTop, q m ≤ 0 :=
      (hp.eventually_lt_const ha).mono fun m hm ↦
        le_of_not_gt (fun h ↦ (not_lt_of_gt hm) ((hsign m).mp h))
    exact le_of_tendsto hq he

/-- Dense moving grids, continuous features, and convergent coefficients give
weak sign agreement with the continuous reference score. -/
theorem weak_sign_finite_feature_limit {ι X : Type*} [Fintype ι]
    [TopologicalSpace X]
    (P : X → ℝ) (F : ι → X → ℝ) (a : ℕ → (ι → ℝ)) (c : ι → ℝ)
    (x : ℕ → X) (y : X)
    (hP : ContinuousAt P y) (hF : ∀ i, ContinuousAt (F i) y)
    (ha : Tendsto a atTop (𝓝 c)) (hx : Tendsto x atTop (𝓝 y))
    (hsign : ∀ m, (0 < ∑ i, a m i * F i (x m)) ↔ 0 < P (x m)) :
    (0 < P y → 0 ≤ ∑ i, c i * F i y) ∧
      (P y < 0 → (∑ i, c i * F i y) ≤ 0) :=
  weak_sign_of_sequence_limit (fun m ↦ P (x m))
    (fun m ↦ ∑ i, a m i * F i (x m)) (P y) (∑ i, c i * F i y)
    (hP.tendsto.comp hx) (tendsto_finite_feature_eval F a c x y hF ha hx) hsign

/-- A continuous weak sign representative vanishes wherever positive and
negative reference values both accumulate. -/
theorem zero_on_two_sided_sign_boundary {X : Type*} [TopologicalSpace X]
    (P Q : X → ℝ) (hQ : Continuous Q)
    (hpos : ∀ x, 0 < P x → 0 ≤ Q x)
    (hneg : ∀ x, P x < 0 → Q x ≤ 0)
    (x : X) (hxpos : x ∈ closure {y | 0 < P y})
    (hxneg : x ∈ closure {y | P y < 0}) : Q x = 0 := by
  have hp : 0 ≤ Q x :=
    (closure_minimal (fun y hy ↦ hpos y hy) (isClosed_le continuous_const hQ)) hxpos
  have hn : Q x ≤ 0 :=
    (closure_minimal (fun y hy ↦ hneg y hy) (isClosed_le hQ continuous_const)) hxneg
  exact le_antisymm hn hp

end HeadComplexity
