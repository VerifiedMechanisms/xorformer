import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Affine slabs use at most two heads

For an arbitrary affine statistic on the Boolean cube, membership in a closed
interval has head complexity at most two. Finiteness of the cube lets us move
the closed boundary slightly outward, after which an explicit sum of two
positive-affine ratios has cleared numerator `1 - M^2`.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- The center of the interval `[lo, hi]`. -/
noncomputable def slabCenter (lo hi : ℝ) : ℝ := (lo + hi) / 2

/-- The radius of the interval `[lo, hi]`. -/
noncomputable def slabRadius (lo hi : ℝ) : ℝ := (hi - lo) / 2

/-- The closed affine-slab predicate. -/
noncomputable def affineSlab (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ)
    (bits : Fin n → Bool) : Bool :=
  decide (lo ≤ affineValue c cs bits ∧ affineValue c cs bits ≤ hi)

private theorem interval_iff_abs_sub_center_le {lo hi t : ℝ} :
    (lo ≤ t ∧ t ≤ hi) ↔ |t - slabCenter lo hi| ≤ slabRadius lo hi := by
  unfold slabCenter slabRadius
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem affineSlab_eq_true_iff (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ)
    (bits : Fin n → Bool) :
    affineSlab c cs lo hi bits = true ↔
      |affineValue c cs bits - slabCenter lo hi| ≤ slabRadius lo hi := by
  simp only [affineSlab, decide_eq_true_eq]
  exact interval_iff_abs_sub_center_le

private theorem slabRadius_nonneg {lo hi : ℝ} (hlohi : lo ≤ hi) :
    0 ≤ slabRadius lo hi := by
  unfold slabRadius
  linarith

/-- If some cube point lies outside the slab, the finite gap to the closest
outside point gives a strict-radius representation of the closed predicate. -/
private theorem exists_strict_slab_radius
    (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (hout : ∃ bits, affineSlab c cs lo hi bits = false) :
    ∃ r : ℝ, 0 < r ∧ ∀ bits,
      (affineSlab c cs lo hi bits = true ↔
        |affineValue c cs bits - slabCenter lo hi| < r) := by
  classical
  let outside : Finset (Fin n → Bool) :=
    Finset.univ.filter fun bits ↦ affineSlab c cs lo hi bits = false
  have houtside : outside.Nonempty := by
    obtain ⟨bits, hbits⟩ := hout
    exact ⟨bits, by simp [outside, hbits]⟩
  let dist : (Fin n → Bool) → ℝ :=
    fun bits ↦ |affineValue c cs bits - slabCenter lo hi|
  obtain ⟨nearest, hnearest, hmin⟩ := outside.exists_min_image dist houtside
  have hnearest_false : affineSlab c cs lo hi nearest = false :=
    (Finset.mem_filter.mp hnearest).2
  have hradius_lt : slabRadius lo hi < dist nearest := by
    apply lt_of_not_ge
    intro hle
    have htrue := (affineSlab_eq_true_iff c cs lo hi nearest).mpr hle
    simp [hnearest_false] at htrue
  let r : ℝ := (slabRadius lo hi + dist nearest) / 2
  have hradius_r : slabRadius lo hi < r := by
    dsimp [r]
    linarith
  have hr_nearest : r < dist nearest := by
    dsimp [r]
    linarith
  have hr : 0 < r := (slabRadius_nonneg hlohi).trans_lt hradius_r
  refine ⟨r, hr, fun bits ↦ ?_⟩
  constructor
  · intro hbits
    exact ((affineSlab_eq_true_iff c cs lo hi bits).mp hbits).trans_lt hradius_r
  · intro hdist
    cases hbits : affineSlab c cs lo hi bits with
    | false =>
        have hmem : bits ∈ outside := by simp [outside, hbits]
        have hleast : dist nearest ≤ dist bits := hmin bits hmem
        exact (not_lt_of_ge (hr_nearest.le.trans hleast) hdist).elim
    | true => rfl

/-! ## The explicit two-atom construction -/

/-- The sign of `1 - M^2`, for an arbitrary affine `M`, is realized by two
positive-affine ratios. -/
private theorem strictAffineUnitBand_computable
    (m₀ : ℝ) (m : Fin n → ℝ) (f : (Fin n → Bool) → Bool)
    (hf : ∀ bits, (f bits = true ↔ |affineValue m₀ m bits| < 1)) :
    computableWithHeadsN n 2 f := by
  let q₀ : ℝ := 1 + |m₀|
  let q : Fin n → ℝ := fun i ↦ 1 + |m i|
  let p₀ : ℝ := q₀ + m₀
  let p : Fin n → ℝ := fun i ↦ q i + m i
  have hq₀ : 0 < q₀ := by dsimp [q₀]; positivity
  have hq : ∀ i, 0 < q i := fun i ↦ by dsimp [q]; positivity
  have hp₀ : 0 < p₀ := by
    dsimp [p₀, q₀]
    linarith [neg_abs_le m₀]
  have hp : ∀ i, 0 < p i := fun i ↦ by
    dsimp [p, q]
    linarith [neg_abs_le (m i)]
  let b₁₀ : ℝ := 1 + p₀ + q₀
  let b₁ : Fin n → ℝ := fun i ↦ p i + q i
  let b₂₀ : ℝ := 1 + p₀ + 2 * q₀
  let b₂ : Fin n → ℝ := fun i ↦ p i + 2 * q i
  have hb₁₀ : 0 < b₁₀ := by dsimp [b₁₀]; positivity
  have hb₁ : ∀ i, 0 < b₁ i := fun i ↦ by
    dsimp [b₁]
    exact add_pos (hp i) (hq i)
  have hb₂₀ : 0 < b₂₀ := by dsimp [b₂₀]; positivity
  have hb₂ : ∀ i, 0 < b₂ i := fun i ↦ by
    dsimp [b₂]
    exact add_pos (hp i) (mul_pos (by norm_num) (hq i))
  let a₁₀ : ℝ := 4 * p₀
  let a₁ : Fin n → ℝ := fun i ↦ 4 * p i
  let a₂₀ : ℝ := 1 - 5 * p₀ - q₀
  let a₂ : Fin n → ℝ := fun i ↦ -5 * p i - q i
  let φ₁ : FracAtom n :=
    FracAtom.ofPositiveAffineRatio a₁₀ a₁ b₁₀ b₁ hb₁₀ hb₁
  let φ₂ : FracAtom n :=
    FracAtom.ofPositiveAffineRatio a₂₀ a₂ b₂₀ b₂ hb₂₀ hb₂
  apply computable_of_fracComputable
  refine ⟨![φ₁, φ₂], 0, fun bits ↦ ?_⟩
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
  change 0 < φ₁.eval bits + φ₂.eval bits ↔ f bits = true
  rw [show φ₁.eval bits = affineValue a₁₀ a₁ bits / affineValue b₁₀ b₁ bits by
      exact FracAtom.ofPositiveAffineRatio_eval a₁₀ a₁ b₁₀ b₁ hb₁₀ hb₁ bits,
    show φ₂.eval bits = affineValue a₂₀ a₂ bits / affineValue b₂₀ b₂ bits by
      exact FracAtom.ofPositiveAffineRatio_eval a₂₀ a₂ b₂₀ b₂ hb₂₀ hb₂ bits]
  let M : ℝ := affineValue m₀ m bits
  let P : ℝ := affineValue p₀ p bits
  let Q : ℝ := affineValue q₀ q bits
  have hP : P = Q + M := by
    dsimp [P, Q, M, p₀, p]
    simpa using affineValue_linearCombination 0 1 1 q₀ m₀ q m bits
  have hA₁ : affineValue a₁₀ a₁ bits = 4 * P := by
    dsimp [a₁₀, a₁, P]
    exact affineValue_smul 4 p₀ p bits
  have hA₂ : affineValue a₂₀ a₂ bits = 1 - 5 * P - Q := by
    dsimp [a₂₀, a₂, P, Q]
    simpa [sub_eq_add_neg] using
      affineValue_linearCombination 1 (-5) (-1) p₀ q₀ p q bits
  have hB₁ : affineValue b₁₀ b₁ bits = 1 + P + Q := by
    dsimp [b₁₀, b₁, P, Q]
    simpa using affineValue_linearCombination 1 1 1 p₀ q₀ p q bits
  have hB₂ : affineValue b₂₀ b₂ bits = 1 + P + 2 * Q := by
    dsimp [b₂₀, b₂, P, Q]
    simpa using affineValue_linearCombination 1 1 2 p₀ q₀ p q bits
  have hden₁ : 0 < affineValue b₁₀ b₁ bits :=
    affineValue_pos b₁₀ b₁ hb₁₀ hb₁ bits
  have hden₂ : 0 < affineValue b₂₀ b₂ bits :=
    affineValue_pos b₂₀ b₂ hb₂₀ hb₂ bits
  have hD₁ : 0 < 1 + P + Q := hB₁ ▸ hden₁
  have hD₂ : 0 < 1 + P + 2 * Q := hB₂ ▸ hden₂
  rw [hA₁, hA₂, hB₁, hB₂]
  have hscore :
      4 * P / (1 + P + Q) + (1 - 5 * P - Q) / (1 + P + 2 * Q) =
        (1 - M ^ 2) / ((1 + P + Q) * (1 + P + 2 * Q)) := by
    rw [div_add_div _ _ hD₁.ne' hD₂.ne']
    congr 1
    rw [hP]
    ring
  rw [hscore, div_pos_iff_of_pos_right (mul_pos hD₁ hD₂)]
  rw [show 0 < 1 - M ^ 2 ↔ |M| < 1 by
    rw [show 0 < 1 - M ^ 2 ↔ M ^ 2 < 1 by
      constructor <;> intro h <;> linarith, sq_lt_one_iff_abs_lt_one]]
  exact (hf bits).symm

/-! ## Affine slabs -/

/-- Every closed slab of an arbitrary affine statistic is computable with two
heads. No sign condition is imposed on the affine coefficients. -/
theorem affineSlab_computable (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ)
    (hlohi : lo ≤ hi) :
    computableWithHeadsN n 2 (affineSlab c cs lo hi) := by
  classical
  by_cases hout : ∃ bits, affineSlab c cs lo hi bits = false
  · obtain ⟨r, hr, hstrict⟩ := exists_strict_slab_radius c cs lo hi hlohi hout
    let m₀ : ℝ := (c - slabCenter lo hi) / r
    let m : Fin n → ℝ := fun i ↦ cs i / r
    apply strictAffineUnitBand_computable m₀ m (affineSlab c cs lo hi)
    intro bits
    rw [hstrict bits]
    have hsum :
        (∑ i, (cs i / r) * boolToReal (bits i)) =
          (∑ i, cs i * boolToReal (bits i)) / r := by
      calc
        (∑ i, (cs i / r) * boolToReal (bits i)) =
            ∑ i, (cs i * boolToReal (bits i)) / r := by
              refine Finset.sum_congr rfl (fun i _ ↦ ?_)
              ring
        _ = (∑ i, cs i * boolToReal (bits i)) / r := by
              rw [← Finset.sum_div]
    have hM : affineValue m₀ m bits =
        (affineValue c cs bits - slabCenter lo hi) / r := by
      unfold affineValue
      dsimp [m₀, m]
      rw [hsum]
      ring
    rw [hM, abs_div, abs_of_pos hr, div_lt_one hr]
  · apply strictAffineUnitBand_computable 0 (fun _ ↦ 0) (affineSlab c cs lo hi)
    intro bits
    have htrue : affineSlab c cs lo hi bits = true := by
      cases hbits : affineSlab c cs lo hi bits with
      | false => exact (hout ⟨bits, hbits⟩).elim
      | true => rfl
    rw [htrue]
    norm_num [affineValue]

/-- **Affine slab upper bound.** Every closed affine slab has head complexity
at most two. -/
theorem HStar_affineSlab_le_two (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ)
    (hlohi : lo ≤ hi) :
    HStar n (affineSlab c cs lo hi) ≤ 2 :=
  HStar_le_of_computableWithHeadsN (affineSlab_computable c cs lo hi hlohi)

/-- An affine slab has complexity zero exactly when it is constant. -/
theorem HStar_affineSlab_eq_zero_iff (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ) :
    HStar n (affineSlab c cs lo hi) = 0 ↔
      ∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y :=
  HStar_eq_zero_iff (affineSlab c cs lo hi)

/-- An affine slab has complexity one exactly when it is a nonconstant linear
threshold function. -/
theorem HStar_affineSlab_eq_one_iff (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ) :
    HStar n (affineSlab c cs lo hi) = 1 ↔
      (¬ (∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y) ∧
        isLTF (affineSlab c cs lo hi)) :=
  HStar_eq_one_iff (affineSlab c cs lo hi)

/-- A nonconstant affine slab which is not itself an LTF has exact complexity
two. -/
theorem HStar_affineSlab_eq_two (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ)
    (hlohi : lo ≤ hi)
    (hnconst : ¬ (∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y))
    (hnLTF : ¬ isLTF (affineSlab c cs lo hi)) :
    HStar n (affineSlab c cs lo hi) = 2 := by
  have hle := HStar_affineSlab_le_two c cs lo hi hlohi
  have hne₀ : HStar n (affineSlab c cs lo hi) ≠ 0 :=
    fun hzero ↦ hnconst ((HStar_eq_zero_iff _).mp hzero)
  have hne₁ : HStar n (affineSlab c cs lo hi) ≠ 1 :=
    fun hone ↦ hnLTF ((HStar_eq_one_iff _).mp hone).2
  omega

/-- The exact `0/1/2` classification of closed affine slabs. -/
theorem HStar_affineSlab_classification (c : ℝ) (cs : Fin n → ℝ) (lo hi : ℝ)
    (hlohi : lo ≤ hi) :
    (HStar n (affineSlab c cs lo hi) = 0 ↔
      ∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y) ∧
    (HStar n (affineSlab c cs lo hi) = 1 ↔
      (¬ (∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y) ∧
        isLTF (affineSlab c cs lo hi))) ∧
    (HStar n (affineSlab c cs lo hi) = 2 ↔
      (¬ (∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y) ∧
        ¬ isLTF (affineSlab c cs lo hi))) := by
  classical
  refine ⟨HStar_affineSlab_eq_zero_iff c cs lo hi,
    HStar_affineSlab_eq_one_iff c cs lo hi, ?_⟩
  constructor
  · intro htwo
    constructor
    · intro hconst
      have hzero := (HStar_eq_zero_iff _).mpr hconst
      omega
    · intro hLTF
      by_cases hconst : ∀ x y, affineSlab c cs lo hi x = affineSlab c cs lo hi y
      · have hzero := (HStar_eq_zero_iff _).mpr hconst
        omega
      · have hone := (HStar_eq_one_iff _).mpr ⟨hconst, hLTF⟩
        omega
  · rintro ⟨hnconst, hnLTF⟩
    exact HStar_affineSlab_eq_two c cs lo hi hlohi hnconst hnLTF

/-- Exact affine level sets are the zero-width special case. -/
theorem HStar_affineLevelSet_le_two (c : ℝ) (cs : Fin n → ℝ) (t : ℝ) :
    HStar n (affineSlab c cs t t) ≤ 2 :=
  HStar_affineSlab_le_two c cs t t le_rfl

end HeadComplexity
