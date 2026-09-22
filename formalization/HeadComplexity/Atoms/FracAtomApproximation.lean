import HeadComplexity.Atoms.FracAtomDummy

set_option linter.style.header false

/-!
# Uniform dummy-coordinate approximation

The sign-preserving dummy lift is sufficient for complexity invariance.  Score
composition needs the stronger quantitative form: a whole finite family of
atoms can be lifted so that its summed scalar output stays uniformly close to
the original score.  This module packages that consequence of the same
zero-weight continuity argument.
-/

namespace HeadComplexity

open Finset Filter
open scoped BigOperators Topology

variable {m n H : ℕ}

/-- A finite family of fractional atoms admits one common positive dummy weight
whose ambient summed score is uniformly within any prescribed tolerance of
the original score. -/
theorem exists_liftDummyAlong_uniform
    (phi : Fin H → FracAtom m) (c : ℝ) (e : Fin m ↪ Fin n)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon), ∀ y : Fin n → Bool,
      |(c + ∑ h, ((phi h).liftDummy e epsilon hepsilon).eval y) -
        (c + ∑ h, (phi h).eval (pullBitsAlong e y))| < tolerance := by
  classical
  let scoreAt : ℝ → (Fin n → Bool) → ℝ := fun epsilon y ↦
    c + ∑ h, FracAtom.dummyEvalAt (phi h) e epsilon y
  have hcontinuous : ∀ y,
      ContinuousAt (fun epsilon ↦ scoreAt epsilon y) 0 := by
    intro y
    dsimp [scoreAt]
    apply continuousAt_const.add
    have hsum : ∀ s : Finset (Fin H),
        ContinuousAt
          (fun epsilon ↦ ∑ h ∈ s,
            FracAtom.dummyEvalAt (phi h) e epsilon y) 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0)
      | @insert a s ha ih =>
          rw [show (fun epsilon ↦ ∑ h ∈ insert a s,
              FracAtom.dummyEvalAt (phi h) e epsilon y) =
              (fun epsilon ↦ FracAtom.dummyEvalAt (phi a) e epsilon y +
                ∑ h ∈ s, FracAtom.dummyEvalAt (phi h) e epsilon y) by
            funext epsilon
            rw [Finset.sum_insert ha]]
          exact (FracAtom.continuousAt_dummyEvalAt (phi a) e y).add ih
    exact hsum Finset.univ
  have hone : ∀ y, ∀ᶠ epsilon in nhds (0 : ℝ),
      |scoreAt epsilon y - scoreAt 0 y| < tolerance := by
    intro y
    have hball := hcontinuous y
      (Metric.ball_mem_nhds (scoreAt 0 y) htolerance)
    filter_upwards [hball] with epsilon hepsilon
    simpa [Real.dist_eq] using hepsilon
  have hall : ∀ᶠ epsilon in nhds (0 : ℝ),
      ∀ y, |scoreAt epsilon y - scoreAt 0 y| < tolerance :=
    Filter.eventually_all.mpr hone
  change {epsilon : ℝ |
    ∀ y, |scoreAt epsilon y - scoreAt 0 y| < tolerance} ∈ nhds 0 at hall
  rcases Metric.mem_nhds_iff.mp hall with ⟨radius, hradius, hball⟩
  let epsilon := radius / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  refine ⟨epsilon, hepsilon, fun y ↦ ?_⟩
  simp_rw [FracAtom.liftDummy_eval]
  change |scoreAt epsilon y - (c + ∑ h, (phi h).eval (pullBitsAlong e y))| < tolerance
  have hzero : scoreAt 0 y =
      c + ∑ h, (phi h).eval (pullBitsAlong e y) := by
    simp [scoreAt]
  rw [← hzero]
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  rw [sub_zero, abs_of_pos hepsilon]
  dsimp [epsilon]
  linarith

end HeadComplexity
