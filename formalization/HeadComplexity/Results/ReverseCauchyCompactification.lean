import HeadComplexity.Results.ReverseMaskedCauchy

set_option linter.style.header false

/-!
# Compactifying masked exterior Cauchy queries

A common fractional-linear change of all poles and query times combines
with the exact paired-axis construction. The grid score changes by one
positive scalar, with no extra heads. The aggregate cube budget remains
an explicit hypothesis; no universal sign decoder is assumed.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators
open Filter Topology

theorem compactified_cauchy_difference (ε p t : ℝ)
    (hp : p + ε ≠ 0) (ht : t + ε ≠ 0) :
    t / (t + ε) - p / (p + ε) =
      ε * (t - p) / ((t + ε) * (p + ε)) := by
  field_simp
  ring

/-- The column scaling from compactification cancels the column scaling
from exact axis pairing. The resulting factor is independent of the query. -/
theorem compactified_paired_cauchy_identity (ε p t a : ℝ)
    (hε : ε ≠ 0) (hp : p + ε ≠ 0) (ht : t + ε ≠ 0)
    (hpt : t - p ≠ 0) :
    (1 - t / (t + ε)) *
      ((ε * a / (p + ε)) / (t / (t + ε) - p / (p + ε))) =
      ε * (a / (t - p)) := by
  rw [compactified_cauchy_difference ε p t hp ht]
  field_simp
  ring

/-- Any finite masked exterior family satisfying the transformed aggregate
budget has an exact two-head-per-pole, strict, whole-cube axis realization.
The query times need not be clustered near a common constant. -/
theorem exists_compactified_maskedCauchy_reverseAxisData {r s H : ℕ}
    (ε : ℝ) (p a : Fin H → Fin r → ℝ) (t : Fin s → ℝ)
    (mask : Fin H → Fin s → Bool)
    (hε : 0 < ε) (hp : ∀ h i, 0 < p h i) (ht : ∀ j, 0 < t j)
    (hpt : ∀ h i j, p h i < t j)
    (hbudget : ∀ h,
      (∑ i, p h i / (p h i + ε)) +
        (∑ j, if mask h j then ε / (t j + ε) else 0) < 1) :
    ∃ L : ReverseAxisData r s (H + H), ∀ i j,
      L.score (localGrid i j) =
        ε * ∑ h, if mask h j then a h i / (t j - p h i) else 0 := by
  let p' := fun h i ↦ p h i / (p h i + ε)
  let a' := fun h i ↦ ε * a h i / (p h i + ε)
  let t' := fun j ↦ t j / (t j + ε)
  have hd (j : Fin s) : 1 - t' j = ε / (t j + ε) := by
    dsimp [t']
    have he : t j + ε ≠ 0 := ne_of_gt (add_pos (ht j) hε)
    field_simp
    ring
  have hp' : ∀ h i, 0 < p' h i := by
    intro h i
    exact div_pos (hp h i) (add_pos (hp h i) hε)
  have ht' : ∀ j, t' j < 1 := by
    intro j
    exact (div_lt_one (add_pos (ht j) hε)).mpr (by linarith)
  have hp1 : ∀ h i, p' h i < 1 := by
    intro h i
    exact (div_lt_one (add_pos (hp h i) hε)).mpr (by linarith)
  have hpt' : ∀ h i j, p' h i < t' j := by
    intro h i j
    apply (div_lt_div_iff₀ (add_pos (hp h i) hε)
      (add_pos (ht j) hε)).mpr
    nlinarith [mul_pos hε (sub_pos.mpr (hpt h i j))]
  have hη : ∀ᶠ η : ℝ in 𝓝 0, ∀ h,
      (∑ i, p' h i) + (s : ℝ) * η +
        (∑ j, if mask h j then 1 - t' j else 0) < 1 + η := by
    apply Filter.eventually_all.mpr
    intro h
    apply (show Continuous (fun η : ℝ ↦
      (∑ i, p' h i) + (s : ℝ) * η +
        (∑ j, if mask h j then 1 - t' j else 0)) from by fun_prop).continuousAt.eventually_lt
      (show ContinuousAt (fun η : ℝ ↦ 1 + η) 0 from by fun_prop)
    simpa only [mul_zero, add_zero, hd] using hbudget h
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hη
  have hηpos : 0 < radius / 2 := by positivity
  have hηbudget := hball (show radius / 2 ∈ Metric.ball (0 : ℝ) radius from by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hηpos]
    linarith)
  obtain ⟨L, hL⟩ := exists_maskedCauchy_reverseAxisData 1 (radius / 2)
    p' a' t' mask (by norm_num) hηpos hp' ht' hpt' hp1
    (fun h ↦ by simpa only [one_mul] using hηbudget h)
  refine ⟨L, ?_⟩
  intro i j
  rw [hL, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  cases hm : mask h j
  · simp
  · simp only [↓reduceIte]
    exact compactified_paired_cauchy_identity ε (p h i) (t j) (a h i)
      (ne_of_gt hε) (ne_of_gt (add_pos (hp h i) hε))
      (ne_of_gt (add_pos (ht j) hε)) (ne_of_gt (sub_pos.mpr (hpt h i j)))

/-- Poles of quadratic size and queries bounded away from zero satisfy
the transformed cube budget. This permits arbitrary fixed positive
query centers, rather than queries clustered near one. -/
theorem exists_compactified_maskedCauchy_of_small_poles {r s H : ℕ}
    (ε C b : ℝ) (p a : Fin H → Fin r → ℝ) (t : Fin s → ℝ)
    (mask : Fin H → Fin s → Bool)
    (hε : 0 < ε) (hC : 0 < C) (hb : 0 < b)
    (hp : ∀ h i, 0 < p h i) (hpC : ∀ h i, p h i ≤ ε ^ 2 * C)
    (ht : ∀ j, b ≤ t j) (hsep : ε ^ 2 * C < b)
    (hsize : ε * ((r : ℝ) * C + (s : ℝ) / b) < 1) :
    ∃ L : ReverseAxisData r s (H + H), ∀ i j,
      L.score (localGrid i j) =
        ε * ∑ h, if mask h j then a h i / (t j - p h i) else 0 := by
  apply exists_compactified_maskedCauchy_reverseAxisData ε p a t mask hε hp
    (fun j ↦ lt_of_lt_of_le hb (ht j))
    (fun h i j ↦ lt_of_le_of_lt (hpC h i) (lt_of_lt_of_le hsep (ht j)))
  intro h
  have hrow (i : Fin r) : p h i / (p h i + ε) ≤ ε * C := by
    apply (div_le_iff₀ (add_pos (hp h i) hε)).mpr
    nlinarith [hpC h i,
      mul_nonneg (le_of_lt (mul_pos hε hC)) (le_of_lt (hp h i))]
  have hcol (j : Fin s) :
      (if mask h j then ε / (t j + ε) else 0) ≤ ε / b := by
    split
    · apply div_le_div_of_nonneg_left (le_of_lt hε) hb
      linarith [ht j]
    · positivity
  have hr := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hrow i)
  have hc := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hcol j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hr hc
  calc
    _ ≤ (r : ℝ) * (ε * C) + (s : ℝ) * (ε / b) := add_le_add hr hc
    _ = ε * ((r : ℝ) * C + (s : ℝ) / b) := by ring
    _ < 1 := hsize

end HeadComplexity.AxisZeroGluing
