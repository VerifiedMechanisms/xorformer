import Mathlib.Tactic

set_option linter.style.header false

/-! A reciprocal inversion converts signed residues to positive residues at
the cost of duplicating parameters and adding an arbitrarily small error. -/

namespace HeadComplexity.PositiveReciprocalCompletion

noncomputable def pole (r p : ℝ) (b : Bool) : ℝ :=
  if b then (if 0 < r then p else 1) else (if r < 0 then p⁻¹ else 1)

noncomputable def residue (δ r p : ℝ) (b : Bool) : ℝ :=
  if b then (if 0 < r then r else δ) else (if r < 0 then -r / p ^ 2 else δ)

noncomputable def parameter (t : ℝ) (b : Bool) : ℝ := if b then t else t⁻¹

noncomputable def constant (r p : ℝ) : ℝ := if r < 0 then -r / p else 0

noncomputable def pairValue (δ r p t : ℝ) : ℝ :=
  ∑ b : Bool, residue δ r p b / (parameter t b + pole r p b)

theorem pole_positive {r p : ℝ} (hp : 0 < p) (b : Bool) : 0 < pole r p b := by
  cases b <;> simp only [pole, Bool.false_eq_true, ite_true, ite_false] <;> split <;> positivity

theorem residue_positive {δ r p : ℝ} (hδ : 0 < δ) (hp : 0 < p) (b : Bool) :
    0 < residue δ r p b := by
  cases b with
  | false =>
      simp only [residue, Bool.false_eq_true, ite_false]
      split
      · next hr => exact div_pos (neg_pos.mpr hr) (sq_pos_of_pos hp)
      · exact hδ
  | true =>
      simp only [residue, ite_true]
      split
      · assumption
      · exact hδ

theorem parameter_positive {t : ℝ} (ht : 0 < t) (b : Bool) : 0 < parameter t b := by
  cases b <;> simp only [parameter, Bool.false_eq_true, ite_true, ite_false] <;> positivity

theorem reciprocal_complement {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    p / (t + p) + p⁻¹ / (t⁻¹ + p⁻¹) = 1 := by
  have hsum : t + p ≠ 0 := ne_of_gt (add_pos ht hp)
  have hinv : t⁻¹ + p⁻¹ ≠ 0 := by positivity
  have ht0 := ne_of_gt ht
  have hp0 := ne_of_gt hp
  field_simp
  ring

theorem negative_identity {t p : ℝ} (ht : 0 < t) (hp : 0 < p) (r : ℝ) :
    (-r / p ^ 2) / (t⁻¹ + p⁻¹) + r / p = r / (t + p) := by
  have hsum : t + p ≠ 0 := ne_of_gt (add_pos ht hp)
  have hinv : t⁻¹ + p⁻¹ ≠ 0 := by positivity
  have ht0 := ne_of_gt ht
  have hp0 := ne_of_gt hp
  field_simp
  ring

theorem noise_bounds {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    0 ≤ δ / (t + 1) ∧ δ / (t + 1) ≤ δ := by
  have hd : 0 < t + 1 := by positivity
  constructor
  · positivity
  · apply (div_le_iff₀ hd).mpr
    nlinarith

theorem pair_error {δ r p t : ℝ} (hδ : 0 < δ) (hp : 0 < p) (ht : 0 < t) :
    0 ≤ pairValue δ r p t - constant r p - r / (t + p) ∧
      pairValue δ r p t - constant r p - r / (t + p) ≤ 2 * δ := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hn : ¬0 < r := not_lt_of_ge (le_of_lt hr)
    have he : pairValue δ r p t - constant r p - r / (t + p) = δ / (t + 1) := by
      simp only [pairValue, Fintype.sum_bool, residue, pole, parameter, constant,
        Bool.false_eq_true, ite_true, ite_false, hr, hn]
      have hi := negative_identity ht hp r
      simp only [neg_div] at hi ⊢
      linarith
    rw [he]
    have hh := noise_bounds hδ ht
    constructor <;> linarith
  · subst r
    simp only [pairValue, Fintype.sum_bool, residue, pole, parameter, constant,
      Bool.false_eq_true, ite_true, ite_false, lt_self_iff_false, zero_div, sub_zero]
    have h1 := noise_bounds hδ ht
    have h2 := noise_bounds hδ (inv_pos.mpr ht)
    constructor <;> linarith
  · have hn : ¬r < 0 := not_lt_of_ge (le_of_lt hr)
    have he : pairValue δ r p t - constant r p - r / (t + p) = δ / (t⁻¹ + 1) := by
      simp only [pairValue, Fintype.sum_bool, residue, pole, parameter, constant,
        Bool.false_eq_true, ite_true, ite_false, hr, hn]
      ring
    rw [he]
    have hh := noise_bounds hδ (inv_pos.mpr ht)
    constructor <;> linarith

#print axioms pair_error

end HeadComplexity.PositiveReciprocalCompletion
