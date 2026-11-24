import HeadComplexity.Research.OriginalMarginCapacity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

/-! A parity dual certificate which applies to every original head. -/

noncomputable section
namespace HeadComplexity.GlobalParityMargin
open Finset MeasureTheory Set
open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

def parity {n : ℕ} (x : Cube n) : ℝ := ∏ i, bitSign (x i)

def affine {n : ℕ} (a : ℝ) (u : Fin n → ℝ) (x : Cube n) : ℝ :=
  a + ∑ i, u i * boolToReal (x i)

theorem sum_product {n : ℕ} (g : Fin n → Bool → ℝ) :
    (∑ x : Cube n, ∏ i, g i (x i)) = ∏ i, (g i false + g i true) := by
  rw [← Fintype.prod_sum]
  simp [add_comm]

theorem parity_sum_eq_zero {n : ℕ} (hn : 0 < n) :
    (∑ x : Cube n, parity x) = 0 := by
  change (∑ x : Cube n, ∏ i, bitSign (x i)) = 0
  rw [sum_product (fun _ b => bitSign b)]
  simp [bitSign, hn.ne']

theorem exp_affine_factor {n : ℕ} (b : ℝ) (w : Fin n → ℝ) (t : ℝ)
    (x : Cube n) :
    Real.exp (-(affine b w x) * t) =
      Real.exp (-b * t) * ∏ i, (if x i then Real.exp (-w i * t) else 1) := by
  have heq : -(affine b w x) * t = -b * t +
      ∑ i, (if x i then -w i * t else 0) := by
    simp only [affine, neg_add, add_mul, neg_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [boolToReal]
  rw [heq, Real.exp_add, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp

theorem parity_exp_sum {n : ℕ} (b : ℝ) (w : Fin n → ℝ) (t : ℝ) :
    (∑ x : Cube n, parity x * Real.exp (-(affine b w x) * t)) =
      Real.exp (-b * t) * ∏ i, (1 - Real.exp (-w i * t)) := by
  simp_rw [exp_affine_factor]
  have hterm (x : Cube n) : parity x *
      (Real.exp (-b * t) * ∏ i, if x i then Real.exp (-w i * t) else 1) =
      Real.exp (-b * t) * ∏ i,
        (bitSign (x i) * (if x i then Real.exp (-w i * t) else 1)) := by
    rw [Finset.prod_mul_distrib]
    simp only [parity]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum,
    sum_product (fun i z => bitSign z * (if z then Real.exp (-w i * t) else 1))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [bitSign, sub_eq_add_neg]

theorem affine_pos {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) (x : Cube n) : 0 < affine b w x := by
  apply add_pos_of_pos_of_nonneg hb
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw i) (by cases x i <;> simp [boolToReal])

theorem integral_reciprocal {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ in Ioi 0, Real.exp (-B * t)) = 1 / B := by
  simpa using integral_exp_mul_Ioi (a := -B) (by linarith) 0

theorem parity_reciprocal_integral {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) :
    (∑ x : Cube n, parity x / affine b w x) =
      ∫ t : ℝ in Ioi 0, Real.exp (-b * t) * ∏ i, (1 - Real.exp (-w i * t)) := by
  simp_rw [← parity_exp_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul, integral_reciprocal (affine_pos hb hw x)]
    ring
  · intro x _
    exact (integrableOn_exp_mul_Ioi (a := -(affine b w x))
      (by linarith [affine_pos hb hw x]) 0).const_mul _

theorem weighted_reciprocal_integral {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) (a : Cube n → ℝ) :
    (∑ x, a x / affine b w x) =
      ∫ t : ℝ in Ioi 0, ∑ x, a x * Real.exp (-(affine b w x) * t) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul, integral_reciprocal (affine_pos hb hw x)]
    ring
  · intro x _
    exact (integrableOn_exp_mul_Ioi (a := -(affine b w x))
      (by linarith [affine_pos hb hw x]) 0).const_mul _

theorem parity_exp_coordinate {n : ℕ} (b : ℝ) (w : Fin n → ℝ) (t : ℝ)
    (i : Fin n) (r : Bool → ℝ) :
    (∑ x : Cube n, parity x * r (x i) * Real.exp (-(affine b w x) * t)) =
      Real.exp (-b * t) *
        ∏ j, (if j = i then r false - r true * Real.exp (-w j * t)
          else 1 - Real.exp (-w j * t)) := by
  let g (j : Fin n) (z : Bool) : ℝ :=
    (if j = i then r z else 1) * bitSign z *
      (if z then Real.exp (-w j * t) else 1)
  have hterm (x : Cube n) : parity x * r (x i) *
      Real.exp (-(affine b w x) * t) = Real.exp (-b * t) * ∏ j, g j (x j) := by
    rw [exp_affine_factor]
    simp only [g, Finset.prod_mul_distrib]
    have hsel : (∏ j : Fin n, if j = i then r (x j) else 1) = r (x i) := by simp
    rw [hsel]
    unfold parity
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_product g]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i <;> simp [g, bitSign, h, sub_eq_add_neg]

theorem exp_factor_bounds {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin n) :
    0 ≤ 1 - Real.exp (-w i * t) ∧ 1 - Real.exp (-w i * t) ≤ 1 := by
  constructor
  · apply sub_nonneg.mpr
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hw i)) ht
  · linarith [Real.exp_pos (-w i * t)]

theorem reciprocal_parity_nonneg {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ x : Cube n, parity x / affine b w x := by
  rw [parity_reciprocal_integral hb hw]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun i _ => (exp_factor_bounds hw (le_of_lt ht) i).1)

theorem reciprocal_coordinate_nonpos {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    (∑ x : Cube n, parity x * boolToReal (x i) / affine b w x) ≤ 0 := by
  rw [weighted_reciprocal_integral hb hw]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [parity_exp_coordinate]
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have heq : (∏ j : Fin n,
      if j = i then boolToReal false - boolToReal true * Real.exp (-w j * t)
      else 1 - Real.exp (-w j * t)) =
      -Real.exp (-w i * t) * ∏ j ∈ Finset.univ.erase i,
        (1 - Real.exp (-w j * t)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j =>
      if j = i then boolToReal false - boolToReal true * Real.exp (-w j * t)
      else 1 - Real.exp (-w j * t)) (Finset.mem_univ i)]
    norm_num only [↓reduceIte, boolToReal, Bool.false_eq_true, zero_sub, one_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [heq]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
    (Finset.prod_nonneg fun j _ => (exp_factor_bounds hw (le_of_lt ht) j).1)

theorem reciprocal_upper_of_exp_upper {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) (a : Cube n → ℝ)
    (hupper : ∀ t, 0 < t →
      (∑ x, a x * Real.exp (-(affine b w x) * t)) ≤ Real.exp (-b * t)) :
    (∑ x, a x / affine b w x) ≤ 1 / b := by
  rw [weighted_reciprocal_integral hb hw]
  rw [← integral_reciprocal hb]
  apply integral_mono_ae
  · apply integrable_finsetSum
    intro x _
    exact (integrableOn_exp_mul_Ioi (a := -(affine b w x))
      (by linarith [affine_pos hb hw x]) 0).const_mul _
  · exact integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hupper t ht

theorem reciprocal_parity_le {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) :
    (∑ x : Cube n, parity x / affine b w x) ≤ 1 / b := by
  apply reciprocal_upper_of_exp_upper hb hw
  intro t ht
  rw [parity_exp_sum]
  apply mul_le_of_le_one_right (Real.exp_pos _).le
  exact Finset.prod_le_one₀ (fun i _ => (exp_factor_bounds hw ht.le i).1)
    (fun i _ => (exp_factor_bounds hw ht.le i).2)

theorem reciprocal_false_literal_le {n : ℕ} {b : ℝ} {w : Fin n → ℝ}
    (hb : 0 < b) (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    (∑ x : Cube n, parity x * (1 - boolToReal (x i)) / affine b w x) ≤ 1 / b := by
  apply reciprocal_upper_of_exp_upper hb hw
  intro t ht
  rw [parity_exp_coordinate b w t i (fun z => 1 - boolToReal z)]
  apply mul_le_of_le_one_right (Real.exp_pos _).le
  apply Finset.prod_le_one₀
  · intro j _
    by_cases hj : j = i
    · norm_num [hj, boolToReal]
    · simpa [hj] using (exp_factor_bounds hw ht.le j).1
  · intro j _
    by_cases hj : j = i
    · norm_num [hj, boolToReal]
    · simpa [hj] using (exp_factor_bounds hw ht.le j).2

def reciprocalFunctional {n : ℕ} (b : ℝ) (w : Fin n → ℝ) (U : Cube n → ℝ) : ℝ :=
  ∑ x, parity x * U x / affine b w x

theorem reciprocalFunctional_affine {n : ℕ} (b : ℝ) (w : Fin n → ℝ)
    (a : ℝ) (u : Fin n → ℝ) :
    reciprocalFunctional b w (affine a u) =
      a * (∑ x, parity x / affine b w x) +
      ∑ i, u i * (∑ x, parity x * boolToReal (x i) / affine b w x) := by
  unfold reciprocalFunctional affine
  simp_rw [mul_add, add_div, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

theorem negative_slope_mass_le {n : ℕ} (a : ℝ) (u : Fin n → ℝ)
    (hU : ∀ x, 0 ≤ affine a u x) :
    ∑ i, max (-u i) 0 ≤ a := by
  let x : Cube n := fun i => decide (u i < 0)
  have h := hU x
  have heq : affine a u x = a - ∑ i, max (-u i) 0 := by
    unfold affine
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i < 0
    · simp [x, hi, boolToReal, max_eq_left (by linarith : 0 ≤ -u i)]
    · simp [x, hi, boolToReal, max_eq_right (by linarith : -u i ≤ 0)]
  rw [heq] at h
  linarith

theorem reciprocalFunctional_nonnegative_affine_le {n : ℕ}
    {b : ℝ} {w : Fin n → ℝ} (hb : 0 < b) (hw : ∀ i, 0 ≤ w i)
    (a : ℝ) (u : Fin n → ℝ) (hU : ∀ x, 0 ≤ affine a u x) :
    reciprocalFunctional b w (affine a u) ≤ a / b := by
  let C : ℝ := ∑ x : Cube n, parity x / affine b w x
  let E : Fin n → ℝ := fun i => ∑ x : Cube n,
    parity x * boolToReal (x i) / affine b w x
  have hC : C ≤ 1 / b := reciprocal_parity_le hb hw
  have hE : ∀ i, E i ≤ 0 := reciprocal_coordinate_nonpos hb hw
  have hCE (i : Fin n) : C - E i ≤ 1 / b := by
    have h := reciprocal_false_literal_le hb hw i
    have heq : C - E i = ∑ x : Cube n,
        parity x * (1 - boolToReal (x i)) / affine b w x := by
      unfold C E
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rwa [heq]
  have hR : 0 ≤ 1 / b - C := sub_nonneg.mpr hC
  have hterm (i : Fin n) : u i * E i ≤ max (-u i) 0 * (1 / b - C) := by
    by_cases hi : 0 ≤ u i
    · rw [max_eq_right (neg_nonpos.mpr hi), zero_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hi (hE i)
    · have hn : 0 ≤ -u i := by linarith
      rw [max_eq_left hn]
      have hc : -E i ≤ 1 / b - C := by linarith [hCE i]
      have hm := mul_le_mul_of_nonneg_left hc hn
      nlinarith
  have hsum : (∑ i, u i * E i) ≤ a * (1 / b - C) := by
    calc
      _ ≤ ∑ i, max (-u i) 0 * (1 / b - C) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i, max (-u i) 0) * (1 / b - C) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (negative_slope_mass_le a u hU) hR
  rw [reciprocalFunctional_affine]
  change a * C + ∑ i, u i * E i ≤ a / b
  have hid : a * (1 / b - C) = a / b - a * C := by ring
  rw [hid] at hsum
  linarith

theorem affine_linear_combination {n : ℕ} (a b c : ℝ)
    (u w : Fin n → ℝ) (x : Cube n) :
    affine (c * b + a) (fun i => c * w i + u i) x =
      c * affine b w x + affine a u x := by
  simp only [affine, add_mul, Finset.sum_add_distrib, mul_add,
    Finset.mul_sum, mul_assoc]
  ring

theorem reciprocalFunctional_affine_upper {n : ℕ} (hn : 0 < n)
    {b : ℝ} {w : Fin n → ℝ} (hb : 0 < b) (hw : ∀ i, 0 ≤ w i)
    (a M : ℝ) (u : Fin n → ℝ)
    (hbound : ∀ x, |affine a u x / affine b w x| ≤ M) :
    reciprocalFunctional b w (affine a u) ≤ 2 * M := by
  have hnum (x : Cube n) : |affine a u x| ≤ M * affine b w x := by
    have h := hbound x
    rw [abs_div, abs_of_pos (affine_pos hb hw x)] at h
    exact (div_le_iff₀ (affine_pos hb hw x)).mp h
  have hU (x : Cube n) : 0 ≤ affine (M * b + a) (fun i => M * w i + u i) x := by
    rw [affine_linear_combination]
    have h := (abs_le.mp (hnum x)).1
    linarith
  have hu := reciprocalFunctional_nonnegative_affine_le hb hw
    (M * b + a) (fun i => M * w i + u i) hU
  have heq : reciprocalFunctional b w (affine (M * b + a)
      (fun i => M * w i + u i)) = reciprocalFunctional b w (affine a u) := by
    unfold reciprocalFunctional
    simp_rw [affine_linear_combination]
    have hterm (x : Cube n) :
        parity x * (M * affine b w x + affine a u x) / affine b w x =
        M * parity x + parity x * affine a u x / affine b w x := by
      field_simp [(affine_pos hb hw x).ne']
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, parity_sum_eq_zero hn]
    ring
  rw [heq] at hu
  have hzero := hnum (fun _ => false)
  simp only [affine, boolToReal, Bool.false_eq_true, ↓reduceIte, mul_zero,
    Finset.sum_const_zero, add_zero] at hzero
  have ha : a ≤ M * b := (abs_le.mp hzero).2
  have hdiv : (M * b + a) / b ≤ 2 * M := by
    apply (div_le_iff₀ hb).mpr
    nlinarith
  exact hu.trans hdiv

theorem reciprocalFunctional_affine_abs_le {n : ℕ} (hn : 0 < n)
    {b : ℝ} {w : Fin n → ℝ} (hb : 0 < b) (hw : ∀ i, 0 ≤ w i)
    (a M : ℝ) (u : Fin n → ℝ)
    (hbound : ∀ x, |affine a u x / affine b w x| ≤ M) :
    |reciprocalFunctional b w (affine a u)| ≤ 2 * M := by
  apply abs_le.mpr
  constructor
  · have hneg (x : Cube n) : affine (-a) (fun i => -u i) x = -affine a u x := by
      simp [affine, Finset.sum_neg_distrib, neg_mul, add_comm]
    have h := reciprocalFunctional_affine_upper hn hb hw (-a) M (fun i => -u i)
      (by intro x; simpa [hneg, neg_div, abs_neg] using hbound x)
    have heq : reciprocalFunctional b w (affine (-a) (fun i => -u i)) =
        -reciprocalFunctional b w (affine a u) := by
      simp only [reciprocalFunctional, hneg, mul_neg, neg_div, Finset.sum_neg_distrib]
    rw [heq] at h
    linarith
  · exact reciprocalFunctional_affine_upper hn hb hw a M u hbound

theorem parity_flip {n : ℕ} (x : Cube n) :
    parity (flipBits x) = (-1 : ℝ) ^ n * parity x := by
  have hbit (z : Bool) : bitSign (!z) = (-1) * bitSign z := by
    cases z <;> norm_num [bitSign]
  simp only [parity, flipBits, hbit, Finset.prod_mul_distrib]
  simp

theorem abs_parity_sum_flip {n : ℕ} (g : Cube n → ℝ) :
    |∑ x, parity x * g (flipBits x)| = |∑ x, parity x * g x| := by
  let e : Cube n ≃ Cube n :=
    { toFun := flipBits, invFun := flipBits,
      left_inv := flipBits_involutive, right_inv := flipBits_involutive }
  have heq := e.sum_comp (fun x => parity x * g (flipBits x))
  change (∑ x, parity (flipBits x) * g (flipBits (flipBits x))) =
    ∑ x, parity x * g (flipBits x) at heq
  simp only [flipBits_involutive, parity_flip, mul_assoc, ← Finset.mul_sum] at heq
  rw [← heq, abs_mul, abs_pow]
  norm_num

theorem original_head_bound_of_nonnegative_slopes {n : ℕ} (hn : 0 < n)
    (phi : FracAtom n) (ha : 1 ≤ phi.α) (M : ℝ)
    (hM : ∀ x, |phi.eval x| ≤ M) :
    |∑ x : Cube n, parity x * phi.eval x| ≤ 2 * M := by
  let aa := OriginalMarginCapacity.numeratorCoefficients phi
  let bb := OriginalMarginCapacity.denominatorCoefficients phi
  have heq (x : Cube n) :
      affine (aa none) (fun i => aa (some i)) x /
        affine (bb none) (fun i => bb (some i)) x = phi.eval x := by
    simpa [affine, aa, bb, CoefficientOrderChart.affineValue, mul_comm] using
      OriginalMarginCapacity.affineRatio_eq_eval phi x
  have hb : 0 < bb none := OriginalMarginCapacity.denominatorCoefficients_constant_pos phi
  have hw (i : Fin n) : 0 ≤ bb (some i) :=
    OriginalMarginCapacity.denominatorCoefficients_nonneg phi ha (some i)
  have h := reciprocalFunctional_affine_abs_le hn hb hw (aa none) M
    (fun i => aa (some i)) (by intro x; simpa [heq] using hM x)
  simpa only [reciprocalFunctional, mul_div_assoc, heq] using h

/-- The bound quantifies over every genuine head, with either orientation. -/
theorem original_head_parity_abs_le {n : ℕ} (hn : 0 < n)
    (phi : FracAtom n) :
    |∑ x : Cube n, parity x * phi.eval x| ≤
      2 * RelativeMarginQuantifiers.atomSup phi := by
  by_cases ha : 1 ≤ phi.α
  · exact original_head_bound_of_nonnegative_slopes hn phi ha _
      (RelativeMarginQuantifiers.abs_eval_le_atomSup phi)
  · have hf : 1 ≤ phi.flip.α := by
      change 1 ≤ phi.α⁻¹
      exact (one_le_inv₀ phi.hα).mpr (le_of_not_ge ha)
    have h := original_head_bound_of_nonnegative_slopes hn phi.flip hf
      (RelativeMarginQuantifiers.atomSup phi)
      (by intro x; rw [FracAtom.flip_eval];
          exact RelativeMarginQuantifiers.abs_eval_le_atomSup phi _)
    simpa only [FracAtom.flip_eval, abs_parity_sum_flip] using h

theorem parity_sq {n : ℕ} (x : Cube n) : parity x ^ 2 = 1 := by
  rw [parity, ← Finset.prod_pow]
  have hbit (z : Bool) : bitSign z ^ 2 = 1 := by cases z <;> norm_num [bitSign]
  simp [hbit]

def parityFunction {n : ℕ} (x : Cube n) : Bool := decide (parity x = 1)

theorem signedLabel_parityFunction {n : ℕ} (x : Cube n) :
    signedLabel parityFunction x = parity x := by
  have hx : parity x = 1 ∨ parity x = -1 := (sq_eq_one_iff.mp (parity_sq x))
  rcases hx with hx | hx <;> norm_num [parityFunction, signedLabel, hx]

theorem score_parity_abs_le {n H : ℕ} (hn : 0 < n)
    (phi : Fin H → FracAtom n) (c : ℝ) :
    |∑ x : Cube n, parity x * RelativeMarginQuantifiers.score phi c x| ≤
      2 * RelativeMarginQuantifiers.amplitude phi c := by
  have heq : (∑ x : Cube n, parity x * RelativeMarginQuantifiers.score phi c x) =
      ∑ h, ∑ x : Cube n, parity x * (phi h).eval x := by
    simp only [RelativeMarginQuantifiers.score, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, parity_sum_eq_zero hn, zero_mul, zero_add, Finset.sum_comm]
  rw [heq]
  calc
    _ ≤ ∑ h, |∑ x : Cube n, parity x * (phi h).eval x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, 2 * RelativeMarginQuantifiers.atomSup (phi h) :=
      Finset.sum_le_sum (fun h _ => original_head_parity_abs_le hn (phi h))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      unfold RelativeMarginQuantifiers.amplitude
      linarith [abs_nonneg c]

/-- Every representation of parity, at every width, has relative margin at
most twice the reciprocal of the number of Boolean inputs. -/
theorem relativeMargin_parity_le {n H : ℕ} (hn : 0 < n)
    (phi : Fin H → FracAtom n) (c : ℝ)
    (hs : RelativeMarginQuantifiers.StrictlyRepresents parityFunction phi c) :
    RelativeMarginQuantifiers.relativeMargin parityFunction phi c ≤ 2 / (2 : ℝ) ^ n := by
  let γ := RelativeMarginQuantifiers.relativeMargin parityFunction phi c
  let A := RelativeMarginQuantifiers.amplitude phi c
  have hA : 0 < A := RelativeMarginQuantifiers.amplitude_pos_of_strict hs
  have hgap := (RelativeMarginQuantifiers.le_relativeMargin_iff hs).mp
    (show γ ≤ RelativeMarginQuantifiers.relativeMargin parityFunction phi c from le_rfl)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Cube n)))
    (fun x _ => hgap x)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, signedLabel_parityFunction] at hsum
  have hupper := score_parity_abs_le hn phi c
  have hraw := (le_abs_self (∑ x : Cube n,
    parity x * RelativeMarginQuantifiers.score phi c x)).trans hupper
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hmul : γ * (2 : ℝ) ^ n ≤ 2 := by
    change ((2 ^ n : ℕ) : ℝ) * (γ * A) ≤ _ at hsum
    push_cast at hsum
    change _ ≤ 2 * A at hraw
    nlinarith
  exact (le_div_iff₀ hN).mpr hmul

end HeadComplexity.GlobalParityMargin
