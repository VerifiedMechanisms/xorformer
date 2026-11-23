import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Penalty minimization near strict constrained minima

A nonnegative penalty plus a sufficiently small objective has a strict
boundary gap whenever the objective has a gap on the penalty's zero set.
-/

namespace HeadComplexity.PolynomialRootCount

open Set Filter Metric
open scoped Topology

/-- Compactness makes the penalty boundary gap uniform in a small positive
coefficient of the objective. -/
theorem compact_penalty_positive {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {F G : E → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (hn : ∀ x ∈ K, 0 ≤ F x) (hz : ∀ x ∈ K, F x = 0 → 0 < G x) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ x ∈ K, 0 < F x + t * G x := by
  let B := K ∩ {x | G x ≤ 0}
  have hB : IsCompact B := hK.inter_right (isClosed_le hG continuous_const)
  have hp : ∀ x ∈ B, 0 < F x := by
    intro x hx
    by_contra h
    have hfz : F x = 0 := le_antisymm (not_lt.mp h) (hn x hx.1)
    exact (hz x hx.1 hfz).not_ge hx.2
  obtain ⟨δ, hδ, hδF⟩ := hB.exists_forall_le' hF.continuousOn hp
  obtain ⟨L, hL⟩ := hK.bddBelow_image hG.continuousOn
  let M := |L| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨δ / (2 * M), by positivity, fun t ht htle x hx ↦ ?_⟩
  by_cases hGx : 0 < G x
  · exact add_pos_of_nonneg_of_pos (hn x hx) (mul_pos ht hGx)
  have hFx := hδF x ⟨hx, not_lt.mp hGx⟩
  have hGbound : -M ≤ G x := by
    have hg := hL (mem_image_of_mem G hx)
    have hl := neg_abs_le L
    dsimp [M]
    linarith
  have htM : t * (2 * M) ≤ δ := (le_div_iff₀ (by positivity)).mp htle
  have hprod : t * (-M) ≤ t * G x := mul_le_mul_of_nonneg_left hGbound ht.le
  nlinarith

/-- A finite family of positive bounds has a common positive smaller number. -/
theorem exists_pos_lt_finite {I : Type*} [Finite I] (r : I → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, t < r i := by
  have hb : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, t < r i :=
    Filter.eventually_all.mpr fun i ↦ eventually_lt_nhds (hr i)
  have hp : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  exact (hp.and (hb.filter_mono nhdsWithin_le_nhds)).exists

/-- Finitely many distinct centers have uniformly small separated balls inside
prescribed neighborhoods. -/
theorem exists_separated_radius {E I : Type*} [MetricSpace E] [Finite I]
    (x : I → E) (hx : Function.Injective x) (U : I → Set E)
    (hU : ∀ i, U i ∈ 𝓝 (x i)) :
    ∃ r : ℝ, 0 < r ∧ (∀ i, closedBall (x i) r ⊆ U i) ∧
      ∀ i j, i ≠ j → 2 * r < dist (x i) (x j) := by
  choose R hR hRU using fun i ↦ Metric.mem_nhds_iff.mp (hU i)
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i, r < R i :=
    Filter.eventually_all.mpr fun i ↦ eventually_lt_nhds (hR i)
  have hsep (i j : I) : ∀ᶠ r in 𝓝 (0 : ℝ), i ≠ j → 2 * r < dist (x i) (x j) := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hij).elim
    have hd : 0 < dist (x i) (x j) / 2 :=
      div_pos (dist_pos.mpr (fun h ↦ hij (hx h))) (by norm_num)
    filter_upwards [eventually_lt_nhds hd] with r hr _
    linarith
  have hs : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i j, i ≠ j → 2 * r < dist (x i) (x j) :=
    Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr (hsep i)
  have hp : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hsmall, hs⟩ := (hp.and ((hsmall.and hs).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨r, hr, fun i ↦ (closedBall_subset_ball (hsmall i)).trans (hRU i), hs⟩

/-- A strict boundary gap forces a local minimum in the open ball. -/
theorem exists_localMin_of_boundary_lt {E : Type*} [MetricSpace E] [ProperSpace E]
    (x : E) {r : ℝ} (hr : 0 < r) {f : E → ℝ} (hf : Continuous f)
    (hbd : ∀ y ∈ sphere x r, f x < f y) :
    ∃ y ∈ ball x r, IsLocalMin f y := by
  obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
    ⟨x, mem_closedBall_self hr.le⟩ hf.continuousOn
  have hyball : y ∈ ball x r := by
    change dist y x < r
    apply lt_of_le_of_ne (mem_closedBall.mp hy)
    intro heq
    exact (hbd y (mem_sphere.mpr heq)).not_ge (hmin (mem_closedBall_self hr.le))
  exact ⟨y, hyball, hmin.isLocalMin
    (mem_of_superset (isOpen_ball.mem_nhds hyball) ball_subset_closedBall)⟩

/-- A strict gap on a compact set persists uniformly under continuous perturbations. -/
theorem compact_gap_eventually {T E : Type*} [TopologicalSpace T] [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) (f : T × E → ℝ) (hf : Continuous f)
    (t : T) (x : E) (hgap : ∀ y ∈ K, f (t, x) < f (t, y)) :
    ∀ᶠ u in 𝓝 t, ∀ y ∈ K, f (u, x) < f (u, y) := by
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hc : Continuous (fun z : T × E ↦ f (z.1, z.2) - f (z.1, x)) :=
    hf.sub (hf.comp (continuous_fst.prodMk continuous_const))
  have hpos : 0 < f (t, y) - f (t, x) := sub_pos.mpr (hgap y hy)
  filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hpos)] with z hz
  exact sub_pos.mp hz

end HeadComplexity.PolynomialRootCount
