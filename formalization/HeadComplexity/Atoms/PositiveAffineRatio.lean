import HeadComplexity.Atoms.FracAtomHead

set_option linter.style.header false

/-!
# Affine ratios with positive affine denominators

Every ratio whose numerator is affine and whose denominator has a positive
constant coefficient and positive variable coefficients is a `FracAtom`.
This is the reusable converse to the affine presentation of fractional atoms.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- Evaluation of an affine functional on the Boolean cube. -/
noncomputable def affineValue (c : ℝ) (cs : Fin n → ℝ)
    (bits : Fin n → Bool) : ℝ :=
  c + ∑ i, cs i * boolToReal (bits i)

/-- A positive affine functional is positive everywhere on the Boolean cube. -/
theorem affineValue_pos (c : ℝ) (cs : Fin n → ℝ)
    (hc : 0 < c) (hcs : ∀ i, 0 < cs i) (bits : Fin n → Bool) :
    0 < affineValue c cs bits := by
  unfold affineValue
  exact add_pos_of_pos_of_nonneg hc
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hcs i).le (by
      cases bits i <;> simp [boolToReal]))

theorem affineValue_add (c d : ℝ) (cs ds : Fin n → ℝ) (bits : Fin n → Bool) :
    affineValue (c + d) (fun i ↦ cs i + ds i) bits =
      affineValue c cs bits + affineValue d ds bits := by
  simp only [affineValue, add_mul, Finset.sum_add_distrib]
  ring

theorem affineValue_smul (r c : ℝ) (cs : Fin n → ℝ) (bits : Fin n → Bool) :
    affineValue (r * c) (fun i ↦ r * cs i) bits = r * affineValue c cs bits := by
  unfold affineValue
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem affineValue_const_add (r c : ℝ) (cs : Fin n → ℝ) (bits : Fin n → Bool) :
    affineValue (r + c) cs bits = r + affineValue c cs bits := by
  unfold affineValue
  ring

/-- Evaluation commutes with an affine combination of two affine forms. -/
theorem affineValue_linearCombination
    (k r s c d : ℝ) (cs ds : Fin n → ℝ) (bits : Fin n → Bool) :
    affineValue (k + r * c + s * d) (fun i ↦ r * cs i + s * ds i) bits =
      k + r * affineValue c cs bits + s * affineValue d ds bits := by
  calc
    affineValue (k + r * c + s * d) (fun i ↦ r * cs i + s * ds i) bits =
        k + affineValue (r * c + s * d) (fun i ↦ r * cs i + s * ds i) bits := by
          rw [show k + r * c + s * d = k + (r * c + s * d) by ring]
          exact affineValue_const_add k (r * c + s * d)
            (fun i ↦ r * cs i + s * ds i) bits
    _ = k + (affineValue (r * c) (fun i ↦ r * cs i) bits +
          affineValue (s * d) (fun i ↦ s * ds i) bits) := by
          rw [affineValue_add]
    _ = k + (r * affineValue c cs bits + s * affineValue d ds bits) := by
          rw [affineValue_smul, affineValue_smul]
    _ = k + r * affineValue c cs bits + s * affineValue d ds bits := by ring

namespace FracAtom

/-- Scale used to encode a positive affine denominator as an atom denominator. -/
noncomputable def positiveAffineScale (b₀ : ℝ) (b : Fin n → ℝ) : ℝ :=
  1 + (∑ i, b i) / b₀

theorem positiveAffineScale_pos (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) :
    0 < positiveAffineScale b₀ b := by
  unfold positiveAffineScale
  have hsum : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ ↦ (hb i).le
  positivity

/-- The fractional atom realizing `affineValue a₀ a / affineValue b₀ b`.
The denominator coefficients are required to be strictly positive. -/
noncomputable def ofPositiveAffineRatio
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) : FracAtom n := by
  let s := positiveAffineScale b₀ b
  have hs : 0 < s := positiveAffineScale_pos b₀ b hb₀ hb
  have hsum : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ ↦ (hb i).le
  have hscale : ∑ i, b i < b₀ * s := by
    rw [show b₀ * s = b₀ + ∑ i, b i by
      dsimp [s, positiveAffineScale]
      field_simp]
    linarith
  exact
    { η := a₀ - ∑ i, (b i / s) * (a i / b i)
      δ := 0
      γ := b₀ - (∑ i, b i) / s
      α := 1 + s
      ρ := fun i ↦ b i / s
      m := fun i ↦ a i / b i
      hγ := sub_pos.mpr ((div_lt_iff₀ hs).mpr hscale)
      hα := by linarith
      hρ := fun i ↦ div_pos (hb i) hs }

private theorem ofPositiveAffineRatio_wt
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i)
    (bits : Fin n → Bool) (i : Fin n) :
    (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).wt bits i =
      b i / positiveAffineScale b₀ b + b i * boolToReal (bits i) := by
  have hs := positiveAffineScale_pos b₀ b hb₀ hb
  unfold wt ofPositiveAffineRatio
  dsimp
  cases bits i
  · simp [boolToReal]
  · simp [boolToReal]
    field_simp [hs.ne']

/-- The atom denominator is exactly the prescribed positive affine functional. -/
theorem ofPositiveAffineRatio_denom
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) (bits : Fin n → Bool) :
    (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).γ +
        ∑ i, (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).wt bits i =
      affineValue b₀ b bits := by
  simp_rw [ofPositiveAffineRatio_wt a₀ a b₀ b hb₀ hb bits]
  rw [Finset.sum_add_distrib]
  unfold affineValue ofPositiveAffineRatio
  dsimp
  rw [← Finset.sum_div]
  ring

/-- The atom numerator is exactly the prescribed affine functional. -/
theorem ofPositiveAffineRatio_num
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) (bits : Fin n → Bool) :
    (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).η +
        ∑ i, (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).wt bits i *
          ((ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).m i +
            if bits i then (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).δ else 0) =
      affineValue a₀ a bits := by
  have hs := positiveAffineScale_pos b₀ b hb₀ hb
  unfold affineValue
  simp_rw [ofPositiveAffineRatio_wt a₀ a b₀ b hb₀ hb bits]
  unfold ofPositiveAffineRatio
  dsimp
  simp only [ite_self, add_zero]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hcancel :
      (∑ i, b i * boolToReal (bits i) * (a i / b i)) =
        ∑ i, a i * boolToReal (bits i) := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    field_simp [(hb i).ne']
  rw [hcancel]
  ring

/-- **Positive-affine-ratio atom lemma.** An arbitrary affine numerator over
a strictly coefficient-positive affine denominator is exactly one atom. -/
theorem ofPositiveAffineRatio_eval
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) (bits : Fin n → Bool) :
    (ofPositiveAffineRatio a₀ a b₀ b hb₀ hb).eval bits =
      affineValue a₀ a bits / affineValue b₀ b bits := by
  unfold eval
  rw [ofPositiveAffineRatio_num, ofPositiveAffineRatio_denom]

/-! ## The opposite denominator orientation -/

/-- Scale used for a denominator with strictly negative variable coefficients.
The hypothesis `sum (-b i) < b₀` says that the denominator remains positive at
the all-true cube point. -/
noncomputable def negativeAffineScale (b₀ : ℝ) (b : Fin n → ℝ) : ℝ :=
  (1 + (∑ i, -b i) / b₀) / 2

theorem negativeAffineScale_pos_lt_one
    (b₀ : ℝ) (b : Fin n → ℝ) (hb₀ : 0 < b₀)
    (hb : ∀ i, b i < 0) (hmargin : ∑ i, -b i < b₀) :
    0 < negativeAffineScale b₀ b ∧ negativeAffineScale b₀ b < 1 := by
  unfold negativeAffineScale
  have hratio : (∑ i, -b i) / b₀ < 1 := (div_lt_one hb₀).mpr hmargin
  have hsum_nonneg : 0 ≤ ∑ i, -b i := by
    exact Finset.sum_nonneg fun i _ ↦ neg_nonneg.mpr (hb i).le
  constructor
  · have : 0 ≤ (∑ i, -b i) / b₀ := div_nonneg hsum_nonneg hb₀.le
    linarith
  · linarith

/-- The atom realizing an affine ratio whose denominator coefficients are all
strictly negative and whose denominator remains positive on the cube. -/
noncomputable def ofNegativeAffineRatio
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, b i < 0) (hmargin : ∑ i, -b i < b₀) : FracAtom n := by
  let s := negativeAffineScale b₀ b
  have hs : 0 < s := (negativeAffineScale_pos_lt_one b₀ b hb₀ hb hmargin).1
  have hsone : s < 1 := (negativeAffineScale_pos_lt_one b₀ b hb₀ hb hmargin).2
  have hscale : ∑ i, -b i < b₀ * s := by
    rw [show b₀ * s = (b₀ + ∑ i, -b i) / 2 by
      dsimp [s, negativeAffineScale]
      field_simp]
    linarith
  exact
    { η := a₀ - ∑ i, ((-b i) / s) * (a i / b i)
      δ := 0
      γ := b₀ - (∑ i, -b i) / s
      α := 1 - s
      ρ := fun i ↦ (-b i) / s
      m := fun i ↦ a i / b i
      hγ := sub_pos.mpr ((div_lt_iff₀ hs).mpr hscale)
      hα := sub_pos.mpr hsone
      hρ := fun i ↦ div_pos (neg_pos.mpr (hb i)) hs }

private theorem ofNegativeAffineRatio_wt
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, b i < 0) (hmargin : ∑ i, -b i < b₀)
    (bits : Fin n → Bool) (i : Fin n) :
    (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).wt bits i =
      (-b i) / negativeAffineScale b₀ b + b i * boolToReal (bits i) := by
  have hs := (negativeAffineScale_pos_lt_one b₀ b hb₀ hb hmargin).1
  unfold wt ofNegativeAffineRatio
  dsimp
  cases bits i
  · simp [boolToReal]
  · simp [boolToReal]
    field_simp [hs.ne']
    ring

/-- The denominator of the negative-orientation atom is the prescribed affine
functional. -/
theorem ofNegativeAffineRatio_denom
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, b i < 0) (hmargin : ∑ i, -b i < b₀)
    (bits : Fin n → Bool) :
    (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).γ +
        ∑ i, (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).wt bits i =
      affineValue b₀ b bits := by
  simp_rw [ofNegativeAffineRatio_wt a₀ a b₀ b hb₀ hb hmargin bits]
  rw [Finset.sum_add_distrib]
  unfold affineValue ofNegativeAffineRatio
  dsimp
  rw [← Finset.sum_div]
  ring

/-- The numerator of the negative-orientation atom is the prescribed affine
functional. -/
theorem ofNegativeAffineRatio_num
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, b i < 0) (hmargin : ∑ i, -b i < b₀)
    (bits : Fin n → Bool) :
    (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).η +
        ∑ i, (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).wt bits i *
          ((ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).m i +
            if bits i then (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).δ else 0) =
      affineValue a₀ a bits := by
  unfold affineValue
  simp_rw [ofNegativeAffineRatio_wt a₀ a b₀ b hb₀ hb hmargin bits]
  unfold ofNegativeAffineRatio
  dsimp
  simp only [ite_self, add_zero]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hcancel :
      (∑ i, b i * boolToReal (bits i) * (a i / b i)) =
        ∑ i, a i * boolToReal (bits i) := by
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    field_simp [(hb i).ne]
  rw [hcancel]
  ring

/-- Negative-orientation affine-ratio atom lemma. -/
theorem ofNegativeAffineRatio_eval
    (a₀ : ℝ) (a : Fin n → ℝ) (b₀ : ℝ) (b : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, b i < 0) (hmargin : ∑ i, -b i < b₀)
    (bits : Fin n → Bool) :
    (ofNegativeAffineRatio a₀ a b₀ b hb₀ hb hmargin).eval bits =
      affineValue a₀ a bits / affineValue b₀ b bits := by
  unfold eval
  rw [ofNegativeAffineRatio_num, ofNegativeAffineRatio_denom]

end FracAtom

/-- A finite sign-separating sum of positive-affine ratios is computable with
one head per ratio. -/
theorem computableWithHeadsN_of_positiveAffineRatios
    {H : ℕ} {f : (Fin n → Bool) → Bool}
    (a₀ : Fin H → ℝ) (a : Fin H → Fin n → ℝ)
    (b₀ : Fin H → ℝ) (b : Fin H → Fin n → ℝ)
    (hb₀ : ∀ h, 0 < b₀ h) (hb : ∀ h i, 0 < b h i) (bias : ℝ)
    (hsign : ∀ bits, (0 < bias + ∑ h, affineValue (a₀ h) (a h) bits /
      affineValue (b₀ h) (b h) bits) ↔ f bits = true) :
    computableWithHeadsN n H f := by
  apply computable_of_fracComputable
  refine ⟨fun h ↦ FracAtom.ofPositiveAffineRatio
      (a₀ h) (a h) (b₀ h) (b h) (hb₀ h) (hb h), bias, ?_⟩
  intro bits
  simpa only [FracAtom.ofPositiveAffineRatio_eval] using hsign bits

end HeadComplexity
