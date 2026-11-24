import HeadComplexity.Atoms.OrientedAtomTangent
import HeadComplexity.Atoms.FracAtomSymmetry

set_option linter.style.header false

/-!
# Positive denominator kernels for odd Boolean targets

Every original representation of an antipodally odd target yields a strict
sum of odd kernels, with the same number of summands and positive simplex
denominator parameters. This is a normalization, not a head-count bound.
-/

namespace HeadComplexity
namespace OddKernel

open scoped BigOperators

variable {n H : ℕ}

noncomputable def literal (x : Fin n → Bool) (i : Fin n) : ℝ :=
  if x i then 1 else -1

noncomputable def dot (v : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, v i * literal x i

@[simp] theorem literal_flip (x : Fin n → Bool) (i : Fin n) :
    literal (flipBits x) i = -literal x i := by
  cases h : x i <;> simp [literal, flipBits, h]

@[simp] theorem dot_flip (v : Fin n → ℝ) (x : Fin n → Bool) :
    dot v (flipBits x) = -dot v x := by
  simp [dot, Finset.sum_neg_distrib]

@[simp] theorem dot_true (v : Fin n → ℝ) : dot v (fun _ ↦ true) = ∑ i, v i := by
  simp [dot, literal]

@[simp] theorem dot_false (v : Fin n → ℝ) : dot v (fun _ ↦ false) = -(∑ i, v i) := by
  simp [dot, literal, Finset.sum_neg_distrib]

theorem affine_center (c : ℝ) (cs : Fin n → ℝ) (x : Fin n → Bool) :
    affineValue c cs x = c + (∑ i, cs i) / 2 + dot (fun i ↦ cs i / 2) x := by
  have ht (i : Fin n) : cs i * boolToReal (x i) =
      cs i / 2 + cs i / 2 * literal x i := by
    cases h : x i <;> simp [boolToReal, literal, h]
  simp only [affineValue, ht, Finset.sum_add_distrib, dot, Finset.sum_div]
  ring

noncomputable def centerDen (phi : FracAtom n) : ℝ :=
  phi.tangentDenConst + (∑ i, phi.tangentDenCoeff i) / 2

noncomputable def centerNum (phi : FracAtom n) : ℝ :=
  (phi.tangentNumConst + (∑ i, phi.tangentNumCoeff i) / 2) / centerDen phi

noncomputable def denVector (phi : FracAtom n) (i : Fin n) : ℝ :=
  phi.tangentDenCoeff i / (2 * centerDen phi)

noncomputable def numVector (phi : FracAtom n) (i : Fin n) : ℝ :=
  phi.tangentNumCoeff i / (2 * centerDen phi)

theorem centerDen_pos (phi : FracAtom n) : 0 < centerDen phi := by
  have h0 := phi.denom_pos (fun _ ↦ false)
  have h1 := phi.denom_pos (fun _ ↦ true)
  rw [← phi.tangentDen_affineValue] at h0 h1
  simp only [affineValue, boolToReal, Bool.false_eq_true, ite_false,
    mul_zero, Finset.sum_const_zero, add_zero] at h0
  simp only [affineValue, boolToReal, ite_true, mul_one] at h1
  unfold centerDen
  linarith

theorem den_center_factor (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue phi.tangentDenConst phi.tangentDenCoeff x =
      centerDen phi * (1 + dot (denVector phi) x) := by
  rw [affine_center]
  change centerDen phi + dot (fun i ↦ phi.tangentDenCoeff i / 2) x = _
  simp only [denVector, dot]
  have hd := (centerDen_pos phi).ne'
  have he (i : Fin n) : phi.tangentDenCoeff i / 2 * literal x i =
      centerDen phi * (phi.tangentDenCoeff i / (2 * centerDen phi) * literal x i) := by
    field_simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

theorem normalized_den_pos (phi : FracAtom n) (x : Fin n → Bool) :
    0 < 1 + dot (denVector phi) x := by
  have hp := phi.denom_pos x
  rw [← phi.tangentDen_affineValue, den_center_factor] at hp
  exact (mul_pos_iff_of_pos_left (centerDen_pos phi)).mp hp

theorem num_center_factor (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue phi.tangentNumConst phi.tangentNumCoeff x =
      centerDen phi * (centerNum phi + dot (numVector phi) x) := by
  rw [affine_center]
  have hd := (centerDen_pos phi).ne'
  have he (i : Fin n) : phi.tangentNumCoeff i / 2 * literal x i =
      centerDen phi * (phi.tangentNumCoeff i / (2 * centerDen phi) * literal x i) := by
    field_simp
  simp only [dot, numVector]
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold centerNum
  field_simp

theorem eval_center (phi : FracAtom n) (x : Fin n → Bool) :
    phi.eval x = (centerNum phi + dot (numVector phi) x) /
      (1 + dot (denVector phi) x) := by
  unfold FracAtom.eval
  rw [← phi.tangentNum_affineValue, ← phi.tangentDen_affineValue,
    num_center_factor, den_center_factor]
  exact mul_div_mul_left _ _ (centerDen_pos phi).ne'

theorem denVector_nonneg (phi : FracAtom n) (ha : 1 ≤ phi.α) (i : Fin n) :
    0 ≤ denVector phi i := by
  exact div_nonneg (mul_nonneg (phi.hρ i).le (sub_nonneg.mpr ha))
    (mul_pos (by norm_num) (centerDen_pos phi)).le

theorem denVector_nonpos (phi : FracAtom n) (ha : phi.α ≤ 1) (i : Fin n) :
    denVector phi i ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (phi.hρ i).le (sub_nonpos.mpr ha))
    (mul_pos (by norm_num) (centerDen_pos phi)).le

noncomputable def positiveVector (phi : FracAtom n) (i : Fin n) : ℝ :=
  |denVector phi i|

theorem positiveVector_nonneg (phi : FracAtom n) (i : Fin n) :
    0 ≤ positiveVector phi i := abs_nonneg _

theorem positiveVector_sum_lt (phi : FracAtom n) :
    (∑ i, positiveVector phi i) < 1 := by
  by_cases ha : 1 ≤ phi.α
  · have he (i : Fin n) : positiveVector phi i = denVector phi i :=
      abs_of_nonneg (denVector_nonneg phi ha i)
    simp_rw [he]
    have hp := normalized_den_pos phi (fun _ ↦ false)
    simp only [dot_false] at hp
    linarith
  · have he (i : Fin n) : positiveVector phi i = -denVector phi i :=
      abs_of_nonpos (denVector_nonpos phi (le_of_lt (lt_of_not_ge ha)) i)
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
    have hp := normalized_den_pos phi (fun _ ↦ true)
    simp only [dot_true] at hp
    linarith

theorem positiveVector_dot_sq (phi : FracAtom n) (x : Fin n → Bool) :
    (dot (positiveVector phi) x) ^ 2 = (dot (denVector phi) x) ^ 2 := by
  by_cases ha : 1 ≤ phi.α
  · have he (i : Fin n) : positiveVector phi i = denVector phi i :=
      abs_of_nonneg (denVector_nonneg phi ha i)
    simp only [dot, he]
  · have he (i : Fin n) : positiveVector phi i = -denVector phi i :=
      abs_of_nonpos (denVector_nonpos phi (le_of_lt (lt_of_not_ge ha)) i)
    simp only [dot, he, neg_mul, Finset.sum_neg_distrib, neg_sq]

noncomputable def oddVector (phi : FracAtom n) (i : Fin n) : ℝ :=
  numVector phi i - centerNum phi * denVector phi i

noncomputable def value (u w : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  dot u x / (1 - (dot w x) ^ 2)

theorem abs_dot_le_sum (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : Fin n → Bool) : |dot w x| ≤ ∑ i, w i := by
  calc
    |dot w x| ≤ ∑ i, |w i * literal x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : x i <;> simp [literal, h, abs_of_nonneg (hw i)]

theorem value_den_pos (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : (∑ i, w i) < 1) (x : Fin n → Bool) :
    0 < 1 - (dot w x) ^ 2 := by
  have hd := abs_lt.mp ((abs_dot_le_sum w hw x).trans_lt hs)
  have hp : 0 < (1 - dot w x) * (1 + dot w x) :=
    mul_pos (by linarith [hd.2]) (by linarith [hd.1])
  nlinarith

@[simp] theorem value_flip (u w : Fin n → ℝ) (x : Fin n → Bool) :
    value u w (flipBits x) = -value u w x := by
  simp [value, dot_flip]
  ring

theorem scalar_odd_identity (a b v : ℝ) (hp : 1 + v ≠ 0) (hm : 1 - v ≠ 0) :
    ((a + b) / (1 + v) - (a - b) / (1 - v)) / 2 =
      (b - a * v) / (1 - v ^ 2) := by
  have hs : 1 - v ^ 2 ≠ 0 := by
    rw [show 1 - v ^ 2 = (1 + v) * (1 - v) by ring]
    exact mul_ne_zero hp hm
  field_simp
  ring

theorem atom_odd_identity (phi : FracAtom n) (x : Fin n → Bool) :
    (phi.eval x - phi.eval (flipBits x)) / 2 =
      value (oddVector phi) (positiveVector phi) x := by
  rw [eval_center, eval_center]
  simp only [dot_flip]
  have hp := (normalized_den_pos phi x).ne'
  have hm : 1 - dot (denVector phi) x ≠ 0 := by
    have h := (normalized_den_pos phi (flipBits x)).ne'
    simpa only [dot_flip, sub_eq_add_neg] using h
  rw [show centerNum phi + -dot (numVector phi) x =
      centerNum phi - dot (numVector phi) x by ring,
    show 1 + -dot (denVector phi) x = 1 - dot (denVector phi) x by ring,
    scalar_odd_identity _ _ _ hp hm]
  unfold value
  rw [positiveVector_dot_sq]
  simp only [oddVector, dot,
    sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

/-- Antipodal oddness turns the original one-sided sign convention into
strict signs, without any preliminary perturbation or added summand. -/
theorem strict_odd_part (f : (Fin n → Bool) → Bool) (F : (Fin n → Bool) → ℝ)
    (hf : ∀ x, f (flipBits x) = !(f x))
    (hF : ∀ x, (0 < F x ↔ f x = true)) (x : Fin n → Bool) :
    if f x then 0 < (F x - F (flipBits x)) / 2
    else (F x - F (flipBits x)) / 2 < 0 := by
  cases hx : f x with
  | false =>
      have h0 : F x ≤ 0 := le_of_not_gt (by simpa [hx] using (hF x).not)
      have h1 : 0 < F (flipBits x) := (hF _).mpr (by simp [hf, hx])
      simp only [Bool.false_eq_true, ite_false]
      linarith
  | true =>
      have h0 : 0 < F x := (hF x).mpr hx
      have h1 : F (flipBits x) ≤ 0 := le_of_not_gt (by
        simpa [hf, hx] using (hF (flipBits x)).not)
      simp only [ite_true]
      linarith

/-- Every original representation of an odd target has a positive-kernel
normal form with the same number of summands. -/
theorem of_fracComputable {f : (Fin n → Bool) → Bool}
    (hf : ∀ x, f (flipBits x) = !(f x)) (hrep : fracComputable n H f) :
    ∃ (u w : Fin H → Fin n → ℝ),
      (∀ h i, 0 ≤ w h i) ∧ (∀ h, (∑ i, w h i) < 1) ∧
      ∀ x, if f x then 0 < ∑ h, value (u h) (w h) x
        else (∑ h, value (u h) (w h) x) < 0 := by
  obtain ⟨phi, c, hphi⟩ := hrep
  refine ⟨fun h ↦ oddVector (phi h), fun h ↦ positiveVector (phi h),
    fun h i ↦ positiveVector_nonneg _ _, fun h ↦ positiveVector_sum_lt _, ?_⟩
  intro x
  have he : (∑ h, value (oddVector (phi h)) (positiveVector (phi h)) x) =
      ((c + ∑ h, (phi h).eval x) - (c + ∑ h, (phi h).eval (flipBits x))) / 2 := by
    simp_rw [← atom_odd_identity]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [he]
  exact strict_odd_part f (fun y ↦ c + ∑ h, (phi h).eval y) hf hphi x

end OddKernel
end HeadComplexity
