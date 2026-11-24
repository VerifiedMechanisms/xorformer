import HeadComplexity.Results.ReverseMaskedCauchy
import HeadComplexity.Results.ReverseCauchyCompactification

set_option linter.style.header false

/-!
# Signed query masks at two heads per moving Cauchy pole

The two masks may overlap. Their overlap cancels exactly. In particular,
disjoint positive and negative masks implement Haar profiles without
doubling the number of heads. The full Boolean cube budget is explicit.
This is an implementation theorem, not a shattering theorem.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators
open Filter Topology

/-- Positive and negative query masks share the same pair of heads.
All slopes are strictly negative and both Boolean axes vanish exactly. -/
theorem exists_signedMaskedCauchy_reverseAxisData {r s H : ℕ}
    (D η : ℝ) (p a : Fin H → Fin r → ℝ) (t : Fin s → ℝ)
    (positiveMask negativeMask : Fin H → Fin s → Bool)
    (hD : 0 < D) (hη : 0 < η) (hp : ∀ h i, 0 < p h i)
    (ht : ∀ j, t j < 1) (hpt : ∀ h i j, p h i < t j)
    (hp1 : ∀ h i, p h i < 1)
    (hbudget : ∀ h : Fin H,
      D * (∑ i, p h i) + (s : ℝ) * η +
        D * (∑ j : Fin s, (1 - t j)) < D + η) :
    ∃ L : ReverseAxisData r s (H + H), ∀ i j,
      L.score (localGrid i j) = (1 - t j) *
        ∑ h, ((if positiveMask h j then a h i / (t j - p h i) else 0) -
          (if negativeMask h j then a h i / (t j - p h i) else 0)) := by
  let P := fun h i ↦ D * p h i
  let A := fun h i ↦ D * (1 - p h i) * a h i
  let slope := fun (mask : Fin H → Fin s → Bool) h j ↦
    η + D * (if mask h j then 1 - t j else 0)
  have hP : ∀ h i, 0 < P h i := fun h i ↦ mul_pos hD (hp h i)
  have hslope (mask : Fin H → Fin s → Bool) : ∀ h j, 0 < slope mask h j := by
    intro h j
    cases hm : mask h j <;> simp only [slope, hm, ↓reduceIte]
    · simpa using hη
    · exact add_pos hη (mul_pos hD (sub_pos.mpr (ht j)))
  have hC (mask : Fin H → Fin s → Bool) :
      ∀ h, (∑ i, P h i) + (∑ j, slope mask h j) < D + η := by
    intro h
    have hsum : (∑ j, if mask h j then 1 - t j else 0) ≤ ∑ j, (1 - t j) := by
      apply Finset.sum_le_sum
      intro j _
      cases mask h j <;> simp [(sub_pos.mpr (ht j)).le]
    have hle := mul_le_mul_of_nonneg_left hsum hD.le
    have hb := hbudget h
    simp only [P, slope, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  refine ⟨pairedRowsAxisData (D + η) P A
    (slope positiveMask) (slope negativeMask) hP
    (hslope positiveMask) (hslope negativeMask)
    (hC positiveMask) (hC negativeMask), ?_⟩
  intro i j
  rw [pairedRowsAxisData_grid, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hid := paired_cauchy_identity D (p h i) (t j) (a h i)
    (ne_of_gt hD) (ne_of_gt (sub_pos.mpr (hp1 h i)))
    (ne_of_gt (sub_pos.mpr (hpt h i j)))
  have h₁ : D + η - D * p h i - (η + D * (1 - t j)) =
      D - D * p h i - D * (1 - t j) := by ring
  have h₂ : D + η - D * p h i - (η + D * 0) = D - D * p h i := by ring
  dsimp [P, A, slope]
  cases hm : positiveMask h j <;> cases hn : negativeMask h j <;>
    (try simp only [Bool.false_eq_true, ↓reduceIte, h₁, h₂])
  · ring
  · rw [zero_sub, mul_neg, ← mul_div_assoc]
    linarith
  · simpa only [sub_zero, mul_div_assoc] using hid
  · ring

/-- A common projective change removes the query-dependent factor in the
paired construction. Signed profiles still cost exactly two heads per pole. -/
theorem exists_compactified_signedCauchy_reverseAxisData {r s H : ℕ}
    (ε : ℝ) (p a : Fin H → Fin r → ℝ) (t : Fin s → ℝ)
    (positiveMask negativeMask : Fin H → Fin s → Bool)
    (hε : 0 < ε) (hp : ∀ h i, 0 < p h i) (ht : ∀ j, 0 < t j)
    (hpt : ∀ h i j, p h i < t j)
    (hbudget : ∀ h,
      (∑ i, p h i / (p h i + ε)) + (∑ j, ε / (t j + ε)) < 1) :
    ∃ L : ReverseAxisData r s (H + H), ∀ i j,
      L.score (localGrid i j) = ε *
        ∑ h, ((if positiveMask h j then a h i / (t j - p h i) else 0) -
          (if negativeMask h j then a h i / (t j - p h i) else 0)) := by
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
      (∑ i, p' h i) + (s : ℝ) * η + (∑ j, (1 - t' j)) < 1 + η := by
    apply Filter.eventually_all.mpr
    intro h
    apply (show Continuous (fun η : ℝ ↦
      (∑ i, p' h i) + (s : ℝ) * η + (∑ j, (1 - t' j))) from by fun_prop
      ).continuousAt.eventually_lt
      (show ContinuousAt (fun η : ℝ ↦ 1 + η) 0 from by fun_prop)
    simpa only [mul_zero, add_zero, hd] using hbudget h
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hη
  have hηpos : 0 < radius / 2 := by positivity
  have hηbudget := hball (show radius / 2 ∈ Metric.ball (0 : ℝ) radius from by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hηpos]
    linarith)
  obtain ⟨L, hL⟩ := exists_signedMaskedCauchy_reverseAxisData 1 (radius / 2)
    p' a' t' positiveMask negativeMask (by norm_num) hηpos hp' ht' hpt' hp1
    (fun h ↦ by simpa only [one_mul] using hηbudget h)
  refine ⟨L, ?_⟩
  intro i j
  rw [hL, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hid := compactified_paired_cauchy_identity ε (p h i) (t j) (a h i)
    (ne_of_gt hε) (ne_of_gt (add_pos (hp h i) hε))
    (ne_of_gt (add_pos (ht j) hε)) (ne_of_gt (sub_pos.mpr (hpt h i j)))
  dsimp [a', p', t']
  cases positiveMask h j <;> cases negativeMask h j <;>
    simp only [Bool.false_eq_true, ↓reduceIte, sub_self, mul_zero, sub_zero,
      zero_sub, mul_neg]
  · exact congrArg Neg.neg hid
  · exact hid

end HeadComplexity.AxisZeroGluing
