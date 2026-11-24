import HeadComplexity.Atoms.RoPE

set_option linter.style.header false

/-!
# A positive direction in the pencil of a pure rotary head

This records the original centered-coordinate reorientation step. The stronger
`Results/RoPETwoHeads` theorem uses token endpoints and removes complement
invariance; the architectural bridge is formalized separately.
-/

namespace HeadComplexity
namespace RoPEReorientation

open scoped BigOperators

variable {n : ℕ}

/-- A pure-head numerator direction, together with its denominator direction,
meets the positive open simplex after one of the two orientations of the latter.
The scalar `k` is the (nonzero, positively oriented) token-value difference. -/
theorem exists_positive_direction (s b u : Fin n → ℝ) (k l : ℝ)
    (hk : 0 < k) (hs : ∀ i, |b i| < s i) (hS : ∑ i, s i < 1)
    (hu : ∀ i, u i = k * s i + l * b i) :
    ∃ (e t : ℝ) (c : Fin n → ℝ),
      (e = 1 ∨ e = -1) ∧ (∀ i, 0 < c i) ∧ (∑ i, c i < 1) ∧
      ∀ i, c i = e * b i + t * u i := by
  let S := ∑ i, s i
  let B := ∑ i, b i
  have hminus : 0 ≤ S - B := by
    rw [sub_nonneg]
    exact Finset.sum_le_sum fun i _ ↦ (le_abs_self (b i)).trans (hs i).le
  have hplus : 0 ≤ S + B := by
    have h : -B ≤ S := by
      dsimp [B, S]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun i _ ↦ (neg_le_abs (b i)).trans (hs i).le
    linarith
  by_cases hl : k * (S - B - 1) < l
  · have hr : 0 < k + l := by nlinarith
    let c : Fin n → ℝ := fun i ↦ k * (s i - b i) / (k + l)
    refine ⟨-1, 1 / (k + l), c, Or.inr rfl, ?_, ?_, ?_⟩
    · intro i
      apply div_pos (mul_pos hk _) hr
      have := hs i
      have := le_abs_self (b i)
      linarith
    · have heq : ∑ i, c i = k * (S - B) / (k + l) := by
        dsimp [c]
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib]
      rw [heq, div_lt_one hr]
      nlinarith
    · intro i
      dsimp [c]
      rw [hu i]
      field_simp
      ring
  · have hl' : l < k * (1 - S - B) := by
      have hSk : S < 1 := hS
      nlinarith
    have hr : 0 < k - l := by nlinarith
    let c : Fin n → ℝ := fun i ↦ k * (s i + b i) / (k - l)
    refine ⟨1, 1 / (k - l), c, Or.inl rfl, ?_, ?_, ?_⟩
    · intro i
      apply div_pos (mul_pos hk _) hr
      have := hs i
      have := neg_le_abs (b i)
      linarith
    · have heq : ∑ i, c i = k * (S + B) / (k - l) := by
        dsimp [c]
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
      rw [heq, div_lt_one hr]
      nlinarith
    · intro i
      dsimp [c]
      rw [hu i]
      field_simp
      ring

/-- The sign of the token-value difference does not affect the conclusion. -/
theorem exists_positive_direction_of_ne_zero (s b u : Fin n → ℝ) (k l : ℝ)
    (hk : k ≠ 0) (hs : ∀ i, |b i| < s i) (hS : ∑ i, s i < 1)
    (hu : ∀ i, u i = k * s i + l * b i) :
    ∃ (e t : ℝ) (c : Fin n → ℝ),
      (e = 1 ∨ e = -1) ∧ (∀ i, 0 < c i) ∧ (∑ i, c i < 1) ∧
      ∀ i, c i = e * b i + t * u i := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · obtain ⟨e, t, c, he, hc, hcs, hcu⟩ :=
      exists_positive_direction s b (fun i ↦ -u i) (-k) (-l)
        (neg_pos.mpr hk) hs hS (fun i ↦ by rw [hu i]; ring)
    exact ⟨e, -t, c, he, hc, hcs, fun i ↦ by rw [hcu i]; ring⟩
  · exact exists_positive_direction s b u k l hk hs hS hu

/-- Reorienting the distinguished direction preserves the whole quadric after
changing the second linear factor. -/
theorem quadric_reorientation (T b u v e t : ℝ) (he : e = 1 ∨ e = -1) :
    T * (1 - (e * b + t * u) ^ 2) +
      u * (v + T * (2 * e * t * b + t ^ 2 * u)) =
        T * (1 - b ^ 2) + u * v := by
  rcases he with rfl | rfl <;> ring

/-- The weighted antipodal average used in the complement-invariant argument. -/
theorem weighted_antipodal_average (T b d u w : ℝ) :
    ((1 - b) * (T * (1 + b) * (1 + d) + u * (1 + d) + w * (1 + b)) +
      (1 + b) * (T * (1 - b) * (1 - d) - u * (1 - d) - w * (1 - b))) / 2 =
        T * (1 - b ^ 2) + u * (d - b) := by
  ring

end RoPEReorientation

namespace PureRoPEAtom

variable {n : ℕ}

/-- The denominator constant after passing to centered Boolean coordinates. -/
noncomputable def centerScale (p : PureRoPEAtom n) : ℝ :=
  p.γ + ∑ i, (p.a i + p.b i) / 2

noncomputable def centerMass (p : PureRoPEAtom n) (i : Fin n) : ℝ :=
  (p.a i + p.b i) / (2 * p.centerScale)

noncomputable def centerBias (p : PureRoPEAtom n) (i : Fin n) : ℝ :=
  (p.b i - p.a i) / (2 * p.centerScale)

noncomputable def centerSlope (p : PureRoPEAtom n) (i : Fin n) : ℝ :=
  (p.b i * p.v₁ - p.a i * p.v₀) / (2 * p.centerScale)

theorem centerScale_pos (p : PureRoPEAtom n) : 0 < p.centerScale := by
  apply add_pos_of_pos_of_nonneg p.hγ
  exact Finset.sum_nonneg fun i _ ↦ (div_pos (add_pos (p.ha i) (p.hb i)) two_pos).le

theorem abs_centerBias_lt_centerMass (p : PureRoPEAtom n) (i : Fin n) :
    |p.centerBias i| < p.centerMass i := by
  have hD : 0 < 2 * p.centerScale := mul_pos two_pos p.centerScale_pos
  simp only [centerBias, centerMass, abs_div, abs_of_pos hD]
  apply (div_lt_div_iff_of_pos_right hD).mpr
  apply abs_lt.mpr
  constructor <;> linarith [p.ha i, p.hb i]

theorem sum_centerMass_lt_one (p : PureRoPEAtom n) :
    ∑ i, p.centerMass i < 1 := by
  unfold centerMass
  rw [← Finset.sum_div, div_lt_one (mul_pos two_pos p.centerScale_pos)]
  have heq : 2 * p.centerScale = 2 * p.γ + ∑ i, (p.a i + p.b i) := by
    unfold centerScale
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [heq]
  linarith [p.hγ]

/-- The centered pure-head numerator belongs to the pencil used above. -/
theorem centerSlope_eq (p : PureRoPEAtom n) (i : Fin n) :
    p.centerSlope i = (p.v₁ - p.v₀) / 2 * p.centerMass i +
      (p.v₁ + p.v₀) / 2 * p.centerBias i := by
  unfold centerSlope centerMass centerBias
  ring

/-- Removing the numerator constant preserves the special pencil relation. -/
theorem centerSlope_sub_eq (p : PureRoPEAtom n) (N : ℝ) (i : Fin n) :
    p.centerSlope i - N * p.centerBias i =
      (p.v₁ - p.v₀) / 2 * p.centerMass i +
        ((p.v₁ + p.v₀) / 2 - N) * p.centerBias i := by
  rw [centerSlope_eq]
  ring

end PureRoPEAtom
end HeadComplexity
