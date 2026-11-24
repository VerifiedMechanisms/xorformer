import HeadComplexity.Model.RectangularPureRoPE

set_option linter.style.header false

/-!
# An explicit three-head pure rotary family on replicated grids

There are eighteen coordinate groups, arranged in three blocks of six.
Replicating each group m times realizes the rational score used in the
continuous-grid argument by three literal pure rotary heads. This module
proves the upper realization only; no vanilla lower bound is asserted here.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

def d (h : Fin 3) (g : Fin 18) : ℝ :=
  if g.val % 6 = h.val then 1 else if g.val % 6 = h.val + 3 then -1 else 0

def u (h : Fin 3) (g : Fin 18) : ℝ :=
  if g.val % 6 = h.val then 4 else 2

theorem sum_d (h : Fin 3) : ∑ g, d h g = 0 := by
  fin_cases h <;> norm_num [d, Fin.sum_univ_succ]

theorem sum_u (h : Fin 3) : ∑ g, u h g = 42 := by
  fin_cases h <;> norm_num [u, Fin.sum_univ_succ]

theorem sum_abs_d (h : Fin 3) : ∑ g, |d h g| = 6 := by
  fin_cases h <;> norm_num [d, Fin.sum_univ_succ]

theorem u_pos (h : Fin 3) (g : Fin 18) : 0 < u h g := by
  simp only [u]
  split <;> norm_num

theorem u_sub_d_pos (h : Fin 3) (g : Fin 18) : 0 < u h g - d h g := by
  simp only [u, d]
  split <;> (try split) <;> norm_num

def group {m : ℕ} (p : Fin (18 * m)) : Fin 18 :=
  ((finProdFinEquiv (m := 18) (n := m)).symm p).1

noncomputable def coordinate {m : ℕ} (x : Fin (18 * m) → Bool) (g : Fin 18) : ℝ :=
  (∑ r : Fin m, (2 * boolToReal (x (finProdFinEquiv (g, r))) - 1)) / m

noncomputable def denominator (h : Fin 3) (q : Fin 18 → ℝ) : ℝ :=
  200 + ∑ g, d h g * q g

noncomputable def numerator (h : Fin 3) (q : Fin 18 → ℝ) : ℝ :=
  ∑ g, u h g * q g

noncomputable def score (q : Fin 18 → ℝ) : ℝ :=
  ∑ h, numerator h q / denominator h q

noncomputable def clearedScore (q : Fin 18 → ℝ) : ℝ :=
  numerator 0 q * denominator 1 q * denominator 2 q +
    numerator 1 q * denominator 0 q * denominator 2 q +
    numerator 2 q * denominator 0 q * denominator 1 q

theorem denominator_bounds (h : Fin 3) (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) : 194 ≤ denominator h q ∧ denominator h q ≤ 206 := by
  have hb : |∑ g, d h g * q g| ≤ 6 := by
    calc
      |∑ g, d h g * q g| ≤ ∑ g, |d h g * q g| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ g, |d h g| * |q g| := by simp only [abs_mul]
      _ ≤ ∑ g, |d h g| := by
        apply Finset.sum_le_sum
        intro g _
        simpa using mul_le_mul_of_nonneg_left (hq g) (abs_nonneg (d h g))
      _ = 6 := sum_abs_d h
  have hl := (abs_le.mp hb).1
  have hu := (abs_le.mp hb).2
  dsimp [denominator]
  constructor <;> linarith

theorem denominator_pos (h : Fin 3) (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) : 0 < denominator h q := by
  have := (denominator_bounds h q hq).1
  linarith

theorem clearedScore_eq (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    clearedScore q = denominator 0 q * denominator 1 q * denominator 2 q * score q := by
  simp only [clearedScore, score, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  dsimp
  field_simp [(denominator_pos 0 q hq).ne', (denominator_pos 1 q hq).ne',
    (denominator_pos 2 q hq).ne']
  ring

theorem clearedScore_pos_iff (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    0 < clearedScore q ↔ 0 < score q := by
  rw [clearedScore_eq q hq]
  exact mul_pos_iff_of_pos_left (mul_pos
    (mul_pos (denominator_pos 0 q hq) (denominator_pos 1 q hq)) (denominator_pos 2 q hq))

theorem score_all_one : score (fun _ ↦ 1) = 63 / 100 := by
  simp only [score, numerator, denominator, mul_one, sum_u, sum_d]
  norm_num [Fin.sum_univ_succ]

theorem score_all_neg_one : score (fun _ ↦ -1) = -(63 / 100) := by
  simp only [score, numerator, denominator, mul_neg_one, Finset.sum_neg_distrib,
    sum_u, sum_d]
  norm_num [Fin.sum_univ_succ]

theorem replicated_sum {m : ℕ} (hm : 0 < m) (w : Fin 18 → ℝ) :
    (∑ p : Fin (18 * m), 2 * w (group p) / m) = 2 * ∑ g, w g := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [← (finProdFinEquiv (m := 18) (n := m)).sum_comp]
  simp only [group, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  field_simp

theorem replicated_weighted_sum {m : ℕ} (hm : 0 < m) (w : Fin 18 → ℝ)
    (x : Fin (18 * m) → Bool) :
    (∑ p : Fin (18 * m), (2 * w (group p) / m) * boolToReal (x p)) =
      (∑ g, w g * coordinate x g) + ∑ g, w g := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [← (finProdFinEquiv (m := 18) (n := m)).sum_comp]
  simp only [group, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  simp only [coordinate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

noncomputable def atom (m : ℕ) (hm : 0 < m) (h : Fin 3) : PureRoPEAtom (18 * m) where
  a p := 2 * (u h (group p) - d h (group p)) / m
  b p := 2 * u h (group p) / m
  γ := 116
  η := -42
  v₀ := 0
  v₁ := 1
  ha p := div_pos (mul_pos (by norm_num) (u_sub_d_pos h (group p))) (by exact_mod_cast hm)
  hb p := div_pos (mul_pos (by norm_num) (u_pos h (group p))) (by exact_mod_cast hm)
  hγ := by norm_num

theorem atom_denominator {m : ℕ} (hm : 0 < m) (h : Fin 3)
    (x : Fin (18 * m) → Bool) :
    (atom m hm h).toAffineFraction.denominator x = denominator h (coordinate x) := by
  have hmass := replicated_sum hm (fun g ↦ u h g - d h g)
  rw [Finset.sum_sub_distrib, sum_u, sum_d] at hmass
  have hs := replicated_weighted_sum hm (d h) x
  rw [sum_d, add_zero] at hs
  simp only [PureRoPEAtom.toAffineFraction, AffineFraction.denominator, atom]
  rw [hmass]
  have hc (p : Fin (18 * m)) :
      2 * u h (group p) / (m : ℝ) - 2 * (u h (group p) - d h (group p)) / m =
        2 * d h (group p) / m := by ring
  simp_rw [hc]
  rw [hs]
  norm_num [denominator]

theorem atom_numerator {m : ℕ} (hm : 0 < m) (h : Fin 3)
    (x : Fin (18 * m) → Bool) :
    (atom m hm h).toAffineFraction.numerator x = numerator h (coordinate x) := by
  have hs := replicated_weighted_sum hm (u h) x
  rw [sum_u] at hs
  simp only [PureRoPEAtom.toAffineFraction, AffineFraction.numerator, atom,
    mul_zero, Finset.sum_const_zero, add_zero, mul_one, sub_zero]
  rw [hs]
  dsimp [numerator]
  ring

theorem atom_eval {m : ℕ} (hm : 0 < m) (h : Fin 3)
    (x : Fin (18 * m) → Bool) :
    (atom m hm h).eval x = numerator h (coordinate x) / denominator h (coordinate x) := by
  rw [PureRoPEAtom.eval_eq, AffineFraction.eval, atom_numerator, atom_denominator]

noncomputable def classifier (m : ℕ) (x : Fin (18 * m) → Bool) : Bool :=
  decide (0 < score (coordinate x))

theorem coordinate_all_true {m : ℕ} (hm : 0 < m) :
    coordinate (fun _ : Fin (18 * m) ↦ true) = fun _ ↦ 1 := by
  funext g
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [coordinate, boolToReal, ite_true, mul_one,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem coordinate_all_false {m : ℕ} (hm : 0 < m) :
    coordinate (fun _ : Fin (18 * m) ↦ false) = fun _ ↦ -1 := by
  funext g
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [coordinate, boolToReal, hm']

theorem classifier_all_true (m : ℕ) (hm : 0 < m) :
    classifier m (fun _ ↦ true) = true := by
  simp only [classifier, coordinate_all_true hm, score_all_one]
  norm_num

theorem classifier_all_false (m : ℕ) (hm : 0 < m) :
    classifier m (fun _ ↦ false) = false := by
  simp only [classifier, coordinate_all_false hm, score_all_neg_one]
  norm_num

theorem pure_computable (m : ℕ) (hm : 0 < m) :
    pureRoPEComputable (18 * m) 3 (classifier m) := by
  refine ⟨atom m hm, 0, fun x ↦ ?_⟩
  simp only [zero_add, atom_eval, classifier, decide_eq_true_eq, score]

theorem standard_computable (m : ℕ) (hm : 0 < m) :
    rectangularStandardPureRotaryComputable (18 * m) 3 (classifier m) :=
  (rectangularStandardPureRotaryComputable_iff_scalar _ _ _).mpr (pure_computable m hm)

theorem free_computable (m : ℕ) (hm : 0 < m) :
    rectangularFreePureRotaryComputable (18 * m) 3 (classifier m) :=
  (rectangularFreePureRotaryComputable_iff_scalar _ _ _).mpr (pure_computable m hm)

end HeadComplexity.PureThreeReplicatedGrid
