import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Generic uniqueness of closest points

Differentiability of the distance function forces uniqueness of a closest
point. Rademacher's theorem supplies a common center for finitely many closed
sets. No convexity assumption is made on those sets.
-/

namespace HeadComplexity.PolynomialRootCount

open Metric Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A differentiable distance function determines every closest point uniquely. -/
theorem closestPoint_unique_of_differentiable {s : Set E} {b x y : E}
    (hd : DifferentiableAt ℝ (fun z ↦ infDist z s) b)
    (hx : x ∈ s) (hy : y ∈ s)
    (hxd : infDist b s = dist b x) (hyd : infDist b s = dist b y) : x = y := by
  have hder (a : E) (ha : a ∈ s) (had : infDist b s = dist b a) :
      (2 : ℝ) • innerSL ℝ (b - a) = fderiv ℝ (fun z ↦ infDist z s ^ 2) b := by
    have hmin : IsLocalMin (fun z ↦ ‖z - a‖ ^ 2 - infDist z s ^ 2) b := by
      apply Filter.Eventually.of_forall
      intro z
      have hle := infDist_le_dist_of_mem (x := z) ha
      have hn := infDist_nonneg (x := z) (s := s)
      dsimp only
      rw [had, dist_eq_norm]
      rw [dist_eq_norm] at hle
      nlinarith [sq_nonneg (‖z - a‖ - infDist z s)]
    have hnorm := ((hasFDerivAt_id b).sub_const a).norm_sq
    have hinf : HasFDerivAt (fun z ↦ infDist z s ^ 2)
        (fderiv ℝ (fun z ↦ infDist z s ^ 2) b) b := by
      exact (hd.fun_pow 2).hasFDerivAt
    have heq := hmin.hasFDerivAt_eq_zero (hnorm.sub hinf)
    simpa only [ContinuousLinearMap.comp_id, sub_eq_zero, id_eq, two_smul] using heq
  have heq := (hder x hx hxd).trans (hder y hy hyd).symm
  have heq' : innerSL ℝ (b - x) = innerSL ℝ (b - y) := by
    exact (smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) heq
  have hxy : b - x = b - y := innerSL_inj.mp heq'
  exact sub_right_injective hxy

/-- Finitely many nonempty closed sets have a common center with a unique
closest point in each set. -/
theorem exists_common_unique_closestPoint [FiniteDimensional ℝ E] [CompleteSpace E]
    {I : Type*} [Finite I] (s : I → Set E)
    (hs : ∀ i, IsClosed (s i)) (hne : ∀ i, (s i).Nonempty) :
    ∃ b : E, ∀ i, ∃! x, x ∈ s i ∧ infDist b (s i) = dist b x := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let μ := (Module.Basis.ofVectorSpace ℝ E).addHaar
  have ha (i : I) : ∀ᵐ b ∂μ, DifferentiableAt ℝ (fun z ↦ infDist z (s i)) b :=
    (lipschitz_infDist_pt (s i)).ae_differentiableAt
  have hall : ∀ᵐ b ∂μ, ∀ i, DifferentiableAt ℝ (fun z ↦ infDist z (s i)) b :=
    Filter.eventually_all.mpr ha
  obtain ⟨b, hb⟩ := hall.exists
  refine ⟨b, fun i ↦ ?_⟩
  obtain ⟨x, hx, hxd⟩ := (hs i).exists_infDist_eq_dist (hne i) b
  refine ⟨x, ⟨hx, hxd⟩, fun y hy ↦ ?_⟩
  exact closestPoint_unique_of_differentiable (hb i) hy.1 hx hy.2 hxd

end HeadComplexity.PolynomialRootCount
