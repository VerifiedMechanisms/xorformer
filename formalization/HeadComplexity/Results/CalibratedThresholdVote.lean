import HeadComplexity.Atoms.AtomicMargin
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Calibrated threshold-vote upper bound

A weighted threshold vote of Boolean features costs one head per feature when
each feature is supplied with a one-atom approximation whose weighted total
error is smaller than the strict vote margin.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n s : ℕ}

/-- The real score of a weighted vote of Boolean features. -/
noncomputable def thresholdVoteScore
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ)
    (bits : Fin n → Bool) : ℝ :=
  c₀ + ∑ j, c j * boolToReal (T j bits)

/-- The Boolean predicate selected by a positive weighted vote score. -/
noncomputable def thresholdVote
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ) :
    (Fin n → Bool) → Bool :=
  fun bits ↦ decide (0 < thresholdVoteScore T c₀ c bits)

/-- The minimum absolute vote score on the finite Boolean cube. -/
noncomputable def thresholdVoteMargin
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).inf' Finset.univ_nonempty
    (fun bits ↦ |thresholdVoteScore T c₀ c bits|)

theorem thresholdVoteMargin_le_abs_score
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ)
    (bits : Fin n → Bool) :
    thresholdVoteMargin T c₀ c ≤ |thresholdVoteScore T c₀ c bits| := by
  exact Finset.inf'_le _ (Finset.mem_univ bits)

/-- **Calibrated threshold-vote theorem.** Fixed one-atom approximations whose
weighted error budget is below the vote margin give an `s`-head model. -/
theorem calibratedThresholdVote_computable
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ)
    (phi : Fin s → FracAtom n) (epsilon : Fin s → ℝ)
    (hmargin : 0 < thresholdVoteMargin T c₀ c)
    (happrox : ∀ j bits,
      |(phi j).eval bits - boolToReal (T j bits)| ≤ epsilon j)
    (hbudget : ∑ j, |c j| * epsilon j < thresholdVoteMargin T c₀ c) :
    computableWithHeadsN n s (thresholdVote T c₀ c) := by
  apply computable_of_fracComputable
  refine ⟨fun j ↦ (phi j).scale (c j), c₀, fun bits ↦ ?_⟩
  let actual : ℝ := c₀ + ∑ j, c j * (phi j).eval bits
  let target : ℝ := thresholdVoteScore T c₀ c bits
  have hactual : c₀ + ∑ j, ((phi j).scale (c j)).eval bits = actual := by
    dsimp [actual]
    simp_rw [FracAtom.scale_eval]
  rw [hactual]
  have hdiff : actual - target =
      ∑ j, c j * ((phi j).eval bits - boolToReal (T j bits)) := by
    dsimp [actual, target, thresholdVoteScore]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have herr : |actual - target| < thresholdVoteMargin T c₀ c := by
    calc
      |actual - target| =
          |∑ j, c j * ((phi j).eval bits - boolToReal (T j bits))| := by
            rw [hdiff]
      _ ≤ ∑ j, |c j * ((phi j).eval bits - boolToReal (T j bits))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |c j| * |(phi j).eval bits - boolToReal (T j bits)| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
      _ ≤ ∑ j, |c j| * epsilon j := by
        exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (happrox j bits) (abs_nonneg (c j))
      _ < thresholdVoteMargin T c₀ c := hbudget
  have htarget_abs : thresholdVoteMargin T c₀ c ≤ |target| := by
    exact thresholdVoteMargin_le_abs_score T c₀ c bits
  have htarget_ne : target ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at htarget_abs
    linarith
  change 0 < actual ↔ decide (0 < target) = true
  simp only [decide_eq_true_eq]
  constructor
  · intro hactual_pos
    by_contra htarget_pos
    have htarget_neg : target < 0 := lt_of_le_of_ne (le_of_not_gt htarget_pos) htarget_ne
    have hupper : actual - target < |target| :=
      (abs_lt.mp (herr.trans_le htarget_abs)).2
    rw [abs_of_neg htarget_neg] at hupper
    linarith
  · intro htarget_pos
    have hlower : -|target| < actual - target :=
      (abs_lt.mp (herr.trans_le htarget_abs)).1
    rw [abs_of_pos htarget_pos] at hlower
    linarith

/-- Head-complexity form of the calibrated threshold-vote theorem. -/
theorem HStar_thresholdVote_le
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ)
    (phi : Fin s → FracAtom n) (epsilon : Fin s → ℝ)
    (hmargin : 0 < thresholdVoteMargin T c₀ c)
    (happrox : ∀ j bits,
      |(phi j).eval bits - boolToReal (T j bits)| ≤ epsilon j)
    (hbudget : ∑ j, |c j| * epsilon j < thresholdVoteMargin T c₀ c) :
    HStar n (thresholdVote T c₀ c) ≤ s :=
  HStar_le_of_computableWithHeadsN
    (calibratedThresholdVote_computable T c₀ c phi epsilon
      hmargin happrox hbudget)

end HeadComplexity
