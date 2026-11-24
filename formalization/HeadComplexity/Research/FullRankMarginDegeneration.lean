import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.AtomicMargin
import Mathlib.Tactic

set_option linter.style.header false

/-!
An exact three-bit margin obstruction for a fixed admissible denominator.
It is a restricted-family result, not a lower bound for unrestricted heads.
-/

noncomputable section

namespace HeadComplexity.FullRankMarginDegeneration

open Finset
open scoped BigOperators

def score (epsilon bias a : ℝ) (c : Fin 3 → ℝ) (x : Fin 3 → Bool) : ℝ :=
  bias + affineValue a c x / affineValue epsilon (fun _ ↦ 1) x

def majority (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

/-- This displayed ratio is a genuine original fractional atom, with strictly
positive denominator slopes. The bias is the original free score bias. -/
theorem score_has_genuine_atom (epsilon bias a : ℝ) (c : Fin 3 → ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ atom : FracAtom 3, ∀ x, score epsilon bias a c x = bias + atom.eval x := by
  refine ⟨FracAtom.ofPositiveAffineRatio a c epsilon (fun _ ↦ 1)
    hepsilon (fun _ ↦ zero_lt_one), ?_⟩
  intro x
  rw [FracAtom.ofPositiveAffineRatio_eval]
  rfl

/-- The exact upper bound uses only two negative singleton rows, their positive
pair row, and the norm at the zero row. No coefficient symmetry is assumed. -/
theorem margin_upper (epsilon bias a gamma M : ℝ) (c : Fin 3 → ℝ)
    (hepsilon : 0 < epsilon) (hM : 0 < M)
    (hbound : |score epsilon bias a c ![false, false, false]| ≤ M)
    (hmargin : ∀ x, gamma * M ≤ signedLabel majority x * score epsilon bias a c x) :
    gamma ≤ epsilon / (4 + 3 * epsilon) := by
  have h0 := hbound
  have h1 := hmargin ![true, false, false]
  have h2 := hmargin ![false, true, false]
  have h12 := hmargin ![true, true, false]
  simp only [score, affineValue, Fin.sum_univ_three] at h0 h1 h2 h12
  simp [signedLabel, majority, boolToReal] at h0 h1 h2 h12
  have hden1 : 0 < epsilon + 1 := by linarith
  have hden2 : 0 < epsilon + 1 + 1 := by linarith
  have hz : -(epsilon * bias + a) ≤ epsilon * M := by
    have h := (abs_le.mp h0).1
    have hmul := mul_le_mul_of_nonneg_right h hepsilon.le
    field_simp [hepsilon.ne'] at hmul
    nlinarith
  have hs1 : epsilon * bias + a + (bias + c 0) ≤
      -(gamma * M) * (epsilon + 1) := by
    have h := mul_le_mul_of_nonneg_right h1 hden1.le
    field_simp [hden1.ne'] at h
    nlinarith
  have hs2 : epsilon * bias + a + (bias + c 1) ≤
      -(gamma * M) * (epsilon + 1) := by
    have h := mul_le_mul_of_nonneg_right h2 hden1.le
    field_simp [hden1.ne'] at h
    nlinarith
  have hs12 : gamma * M * (epsilon + 2) ≤
      epsilon * bias + a + (bias + c 0) + (bias + c 1) := by
    have h := mul_le_mul_of_nonneg_right h12 hden2.le
    field_simp [hden2.ne'] at h
    nlinarith
  apply (le_div_iff₀ (by linarith : 0 < 4 + 3 * epsilon)).mpr
  have hkey : gamma * M * (4 + 3 * epsilon) ≤ epsilon * M := by
    nlinarith
  nlinarith [hkey]

/-- A symmetric genuine numerator attains the margin upper bound. -/
def optimalNumeratorConstant (epsilon : ℝ) : ℝ := -epsilon

def optimalNumeratorSlope (epsilon : ℝ) : ℝ :=
  epsilon * ((3 + 2 * epsilon) / (4 + 3 * epsilon))

theorem optimal_at_zero (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    score epsilon 0 (optimalNumeratorConstant epsilon)
      (fun _ ↦ optimalNumeratorSlope epsilon) ![false, false, false] = -1 := by
  simp only [score, affineValue, Fin.sum_univ_three]
  simp [boolToReal, optimalNumeratorConstant, hepsilon.ne']

theorem optimal_at_singleton (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    score epsilon 0 (optimalNumeratorConstant epsilon)
      (fun _ ↦ optimalNumeratorSlope epsilon) ![true, false, false] =
        -(epsilon / (4 + 3 * epsilon)) := by
  have hd : 4 + 3 * epsilon ≠ 0 := by positivity
  have he : epsilon + 1 ≠ 0 := by positivity
  simp only [score, affineValue, Fin.sum_univ_three, boolToReal,
    optimalNumeratorConstant, optimalNumeratorSlope]
  norm_num
  field_simp
  ring

theorem optimal_at_pair (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    score epsilon 0 (optimalNumeratorConstant epsilon)
      (fun _ ↦ optimalNumeratorSlope epsilon) ![true, true, false] =
        epsilon / (4 + 3 * epsilon) := by
  have hd : 4 + 3 * epsilon ≠ 0 := by positivity
  have he : epsilon + 1 + 1 ≠ 0 := by positivity
  simp only [score, affineValue, Fin.sum_univ_three, boolToReal,
    optimalNumeratorConstant, optimalNumeratorSlope]
  norm_num
  field_simp
  ring

theorem optimal_at_triple (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    score epsilon 0 (optimalNumeratorConstant epsilon)
      (fun _ ↦ optimalNumeratorSlope epsilon) ![true, true, true] =
        epsilon * (5 + 3 * epsilon) / ((4 + 3 * epsilon) * (3 + epsilon)) := by
  have hd : 4 + 3 * epsilon ≠ 0 := by positivity
  have he : epsilon + 1 + 1 + 1 ≠ 0 := by positivity
  have he' : 3 + epsilon ≠ 0 := by positivity
  simp only [score, affineValue, Fin.sum_univ_three, boolToReal,
    optimalNumeratorConstant, optimalNumeratorSlope]
  norm_num
  field_simp
  ring

private theorem optimal_triple_bounds (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    epsilon / (4 + 3 * epsilon) ≤
      epsilon * (5 + 3 * epsilon) / ((4 + 3 * epsilon) * (3 + epsilon)) ∧
    epsilon * (5 + 3 * epsilon) / ((4 + 3 * epsilon) * (3 + epsilon)) ≤ 1 := by
  have hd : 0 < 4 + 3 * epsilon := by positivity
  have he : 0 < 3 + epsilon := by positivity
  constructor
  · apply (div_le_div_iff₀ hd (mul_pos hd he)).mpr
    calc
      epsilon * ((4 + 3 * epsilon) * (3 + epsilon)) =
          (epsilon * (4 + 3 * epsilon)) * (3 + epsilon) := by ring
      _ ≤ (epsilon * (4 + 3 * epsilon)) * (5 + 3 * epsilon) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_pos hepsilon hd).le
      _ = epsilon * (5 + 3 * epsilon) * (4 + 3 * epsilon) := by ring
  · apply (div_le_one (mul_pos hd he)).mpr
    nlinarith

/-- A full-cube certificate of the exact optimum. The norm is one because
`optimal_at_zero` attains absolute value one, and a singleton attains the margin. -/
theorem optimal_full_cube_bounds (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (x : Fin 3 → Bool) :
    |score epsilon 0 (optimalNumeratorConstant epsilon)
      (fun _ ↦ optimalNumeratorSlope epsilon) x| ≤ 1 ∧
    epsilon / (4 + 3 * epsilon) ≤ signedLabel majority x *
      score epsilon 0 (optimalNumeratorConstant epsilon)
        (fun _ ↦ optimalNumeratorSlope epsilon) x := by
  have hgpos : 0 < epsilon / (4 + 3 * epsilon) := by positivity
  have hgle : epsilon / (4 + 3 * epsilon) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4 + 3 * epsilon)).mpr
    linarith
  have ht := optimal_triple_bounds epsilon hepsilon
  have hvec : x = ![x 0, x 1, x 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  generalize x 0 = b0, x 1 = b1, x 2 = b2
  cases b0 <;> cases b1 <;> cases b2
  all_goals
    have hs0 := optimal_at_zero epsilon hepsilon
    have hs1 := optimal_at_singleton epsilon hepsilon
    have hs2 := optimal_at_pair epsilon hepsilon
    have hs3 := optimal_at_triple epsilon hepsilon
    simp only [score, affineValue, Fin.sum_univ_three] at hs0 hs1 hs2 hs3 ⊢
    simp only [show boolToReal false = 0 from rfl, show boolToReal true = 1 from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      mul_zero, mul_one, add_zero, zero_add] at hs0 hs1 hs2 hs3 ⊢
    simp only [signedLabel, majority, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Bool.false_and, Bool.true_and,
      Bool.false_or, Bool.true_or, Bool.false_eq_true, ite_false, ite_true,
      neg_mul, one_mul]
    first
    | rw [hs0]; norm_num; exact hgle
    | rw [hs1]; simp only [abs_neg, abs_of_pos hgpos, neg_neg]; exact ⟨hgle, le_rfl⟩
    | rw [hs2]; simp only [abs_of_pos hgpos]; exact ⟨hgle, le_rfl⟩
    | rw [hs3]; rw [abs_of_nonneg (hgpos.le.trans ht.1)]; exact ⟨ht.2, ht.1⟩

#print axioms score_has_genuine_atom
#print axioms margin_upper
#print axioms optimal_at_zero
#print axioms optimal_at_singleton
#print axioms optimal_at_pair
#print axioms optimal_full_cube_bounds

end HeadComplexity.FullRankMarginDegeneration
