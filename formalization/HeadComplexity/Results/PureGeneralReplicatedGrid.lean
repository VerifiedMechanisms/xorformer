import HeadComplexity.Model.RectangularPureRoPE

set_option linter.style.header false

/-!
# A pure rotary source family with an arbitrary number of heads

The H blocks each contain 2H coordinate groups. Replication gives H literal
pure rotary heads on H(2H)m bits. This module establishes the scalar formula
and its architectural realization only. The general-H vanilla lower bound
is not a theorem of this module.
-/

namespace HeadComplexity.PureGeneralReplicatedGrid

open scoped BigOperators

abbrev groupCount (H : ℕ) := H * (2 * H)

def leftIndex {H : ℕ} (h : Fin H) : Fin (2 * H) := ⟨h.val, by omega⟩
def rightIndex {H : ℕ} (h : Fin H) : Fin (2 * H) := ⟨h.val + H, by omega⟩

def localIndex {H : ℕ} (g : Fin (groupCount H)) : Fin (2 * H) :=
  ((finProdFinEquiv (m := H) (n := 2 * H)).symm g).2

noncomputable def d {H : ℕ} (h : Fin H) (g : Fin (groupCount H)) : ℝ :=
  (if localIndex g = leftIndex h then 1 else 0) -
    (if localIndex g = rightIndex h then 1 else 0)

noncomputable def u {H : ℕ} (h : Fin H) (g : Fin (groupCount H)) : ℝ :=
  2 + 2 * (if localIndex g = leftIndex h then 1 else 0)

noncomputable def mass (H : ℕ) : ℝ := 4 * (H : ℝ) ^ 2 + 2 * H
noncomputable def base (H : ℕ) : ℝ := 20 * (H : ℝ) ^ 2 + 20

theorem sum_d {H : ℕ} (h : Fin H) : ∑ g, d h g = 0 := by
  rw [← (finProdFinEquiv (m := H) (n := 2 * H)).sum_comp]
  simp only [d, localIndex, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp [Finset.sum_sub_distrib]

theorem sum_u {H : ℕ} (h : Fin H) : ∑ g, u h g = mass H := by
  rw [← (finProdFinEquiv (m := H) (n := 2 * H)).sum_comp]
  simp [u, localIndex, Fintype.sum_prod_type, Finset.sum_add_distrib,
    mass]
  ring

theorem sum_abs_d {H : ℕ} (h : Fin H) : ∑ g, |d h g| = 2 * H := by
  have hne : leftIndex h ≠ rightIndex h := by
    intro heq
    have heq' := congrArg Fin.val heq
    dsimp [leftIndex, rightIndex] at heq'
    omega
  have habs (g : Fin (groupCount H)) : |d h g| =
      (if localIndex g = leftIndex h then 1 else 0) +
      (if localIndex g = rightIndex h then 1 else 0) := by
    by_cases hl : localIndex g = leftIndex h
    · simp [d, hl, hne]
    · by_cases hr : localIndex g = rightIndex h <;> simp [d, hl, hr, Ne.symm hne]
  simp_rw [habs]
  rw [← (finProdFinEquiv (m := H) (n := 2 * H)).sum_comp]
  simp only [localIndex, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp [Finset.sum_add_distrib]
  ring

theorem u_pos {H : ℕ} (h : Fin H) (g : Fin (groupCount H)) : 0 < u h g := by
  simp only [u]
  split <;> norm_num

theorem u_sub_d_pos {H : ℕ} (h : Fin H) (g : Fin (groupCount H)) :
    0 < u h g - d h g := by
  simp only [u, d]
  split <;> split <;> norm_num

theorem query_mass_pos (H : ℕ) : 0 < base H - 2 * mass H := by
  dsimp [base, mass]
  nlinarith [sq_nonneg ((H : ℝ) - 1 / 2)]

def group {H m : ℕ} (p : Fin (groupCount H * m)) : Fin (groupCount H) :=
  ((finProdFinEquiv (m := groupCount H) (n := m)).symm p).1

noncomputable def coordinate {H m : ℕ} (x : Fin (groupCount H * m) → Bool)
    (g : Fin (groupCount H)) : ℝ :=
  (∑ r : Fin m, (2 * boolToReal (x (finProdFinEquiv (g, r))) - 1)) / m

noncomputable def denominator {H : ℕ} (h : Fin H)
    (q : Fin (groupCount H) → ℝ) : ℝ := base H + ∑ g, d h g * q g

noncomputable def numerator {H : ℕ} (h : Fin H)
    (q : Fin (groupCount H) → ℝ) : ℝ := ∑ g, u h g * q g

noncomputable def score {H : ℕ} (q : Fin (groupCount H) → ℝ) : ℝ :=
  ∑ h, numerator h q / denominator h q

theorem denominator_bounds {H : ℕ} (h : Fin H) (q : Fin (groupCount H) → ℝ)
    (hq : ∀ g, |q g| ≤ 1) :
    base H - 2 * H ≤ denominator h q ∧ denominator h q ≤ base H + 2 * H := by
  have hb : |∑ g, d h g * q g| ≤ 2 * H := by
    calc
      |∑ g, d h g * q g| ≤ ∑ g, |d h g * q g| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ g, |d h g| * |q g| := by simp only [abs_mul]
      _ ≤ ∑ g, |d h g| := by
        apply Finset.sum_le_sum
        intro g _
        simpa using mul_le_mul_of_nonneg_left (hq g) (abs_nonneg (d h g))
      _ = 2 * H := sum_abs_d h
  have hl := (abs_le.mp hb).1
  have hu := (abs_le.mp hb).2
  dsimp [denominator]
  constructor <;> linarith

theorem denominator_pos {H : ℕ} (h : Fin H) (q : Fin (groupCount H) → ℝ)
    (hq : ∀ g, |q g| ≤ 1) : 0 < denominator h q := by
  have hb := (denominator_bounds h q hq).1
  dsimp [base] at hb
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  nlinarith [sq_nonneg ((H : ℝ) - 1 / 2)]

theorem score_all_one (H : ℕ) :
    score (H := H) (fun _ ↦ 1) = H * mass H / base H := by
  simp [score, numerator, denominator, sum_u, sum_d, mul_div_assoc]

theorem score_all_neg_one (H : ℕ) :
    score (H := H) (fun _ ↦ -1) = -(H * mass H / base H) := by
  simp [score, numerator, denominator, Finset.sum_neg_distrib, sum_u, sum_d,
    mul_div_assoc]
  ring

theorem corner_score_pos (H : ℕ) (hH : 0 < H) : 0 < H * mass H / base H := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  dsimp [mass, base]
  positivity

theorem replicated_sum {H m : ℕ} (hm : 0 < m) (w : Fin (groupCount H) → ℝ) :
    (∑ p : Fin (groupCount H * m), 2 * w (group p) / m) = 2 * ∑ g, w g := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [← (finProdFinEquiv (m := groupCount H) (n := m)).sum_comp]
  simp only [group, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  field_simp

theorem replicated_weighted_sum {H m : ℕ} (hm : 0 < m)
    (w : Fin (groupCount H) → ℝ) (x : Fin (groupCount H * m) → Bool) :
    (∑ p : Fin (groupCount H * m), (2 * w (group p) / m) * boolToReal (x p)) =
      (∑ g, w g * coordinate x g) + ∑ g, w g := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [← (finProdFinEquiv (m := groupCount H) (n := m)).sum_comp]
  simp only [group, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  simp only [coordinate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

noncomputable def atom {H : ℕ} (m : ℕ) (hm : 0 < m) (h : Fin H) :
    PureRoPEAtom (groupCount H * m) where
  a p := 2 * (u h (group p) - d h (group p)) / m
  b p := 2 * u h (group p) / m
  γ := base H - 2 * mass H
  η := -mass H
  v₀ := 0
  v₁ := 1
  ha p := div_pos (mul_pos (by norm_num) (u_sub_d_pos h (group p))) (by exact_mod_cast hm)
  hb p := div_pos (mul_pos (by norm_num) (u_pos h (group p))) (by exact_mod_cast hm)
  hγ := query_mass_pos H

theorem atom_denominator {H m : ℕ} (hm : 0 < m) (h : Fin H)
    (x : Fin (groupCount H * m) → Bool) :
    (atom m hm h).toAffineFraction.denominator x = denominator h (coordinate x) := by
  have hmass := replicated_sum hm (fun g ↦ u h g - d h g)
  rw [Finset.sum_sub_distrib, sum_u, sum_d, sub_zero] at hmass
  have hs := replicated_weighted_sum hm (d h) x
  rw [sum_d, add_zero] at hs
  simp only [PureRoPEAtom.toAffineFraction, AffineFraction.denominator, atom]
  rw [hmass]
  have hc (p : Fin (groupCount H * m)) :
      2 * u h (group p) / (m : ℝ) - 2 * (u h (group p) - d h (group p)) / m =
        2 * d h (group p) / m := by ring
  simp_rw [hc]
  rw [hs]
  dsimp [denominator]
  ring

theorem atom_numerator {H m : ℕ} (hm : 0 < m) (h : Fin H)
    (x : Fin (groupCount H * m) → Bool) :
    (atom m hm h).toAffineFraction.numerator x = numerator h (coordinate x) := by
  have hs := replicated_weighted_sum hm (u h) x
  rw [sum_u] at hs
  simp only [PureRoPEAtom.toAffineFraction, AffineFraction.numerator, atom,
    mul_zero, Finset.sum_const_zero, add_zero, mul_one, sub_zero]
  rw [hs]
  dsimp [numerator]
  ring

theorem atom_eval {H m : ℕ} (hm : 0 < m) (h : Fin H)
    (x : Fin (groupCount H * m) → Bool) :
    (atom m hm h).eval x = numerator h (coordinate x) / denominator h (coordinate x) := by
  rw [PureRoPEAtom.eval_eq, AffineFraction.eval, atom_numerator, atom_denominator]

noncomputable def classifier (H m : ℕ) (x : Fin (groupCount H * m) → Bool) : Bool :=
  decide (0 < score (coordinate x))

theorem coordinate_all_true {H m : ℕ} (hm : 0 < m) :
    coordinate (H := H) (fun _ : Fin (groupCount H * m) ↦ true) = fun _ ↦ 1 := by
  funext g
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [coordinate, boolToReal, ite_true, mul_one,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem coordinate_all_false {H m : ℕ} (hm : 0 < m) :
    coordinate (H := H) (fun _ : Fin (groupCount H * m) ↦ false) = fun _ ↦ -1 := by
  funext g
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [coordinate, boolToReal, hm']

theorem classifier_all_true (H m : ℕ) (hH : 0 < H) (hm : 0 < m) :
    classifier H m (fun _ ↦ true) = true := by
  simpa only [classifier, coordinate_all_true hm, score_all_one, decide_eq_true_eq]
    using corner_score_pos H hH

theorem classifier_all_false (H m : ℕ) (hH : 0 < H) (hm : 0 < m) :
    classifier H m (fun _ ↦ false) = false := by
  simp only [classifier, coordinate_all_false hm, score_all_neg_one, decide_eq_false_iff_not,
    not_lt, neg_nonpos]
  exact le_of_lt (corner_score_pos H hH)

theorem pure_computable (H m : ℕ) (hm : 0 < m) :
    pureRoPEComputable (groupCount H * m) H (classifier H m) := by
  refine ⟨atom m hm, 0, fun x ↦ ?_⟩
  simp only [zero_add, atom_eval, classifier, decide_eq_true_eq, score]

theorem standard_computable (H m : ℕ) (hm : 0 < m) :
    rectangularStandardPureRotaryComputable (groupCount H * m) H (classifier H m) :=
  (rectangularStandardPureRotaryComputable_iff_scalar _ _ _).mpr (pure_computable H m hm)

theorem free_computable (H m : ℕ) (hm : 0 < m) :
    rectangularFreePureRotaryComputable (groupCount H * m) H (classifier H m) :=
  (rectangularFreePureRotaryComputable_iff_scalar _ _ _).mpr (pure_computable H m hm)

end HeadComplexity.PureGeneralReplicatedGrid
