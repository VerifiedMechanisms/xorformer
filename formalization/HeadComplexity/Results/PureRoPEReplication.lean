import HeadComplexity.Atoms.PureRoPECenteredConstruction
import HeadComplexity.Results.RoPEComparison
import HeadComplexity.Polynomial.ThreeHeadCubicFace
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-! # Exact pure-atom upper bounds under arbitrary finite coordinate replication -/

namespace HeadComplexity.PureRoPEReplication

noncomputable section

open PureRoPECenteredConstruction
open scoped BigOperators

def replicate {n : ℕ} (m : ℕ) (v : Fin n → ℝ) (j : Fin (n * m)) : ℝ :=
  v ((finProdFinEquiv (m := n) (n := m)).symm j).1 / m

def means {n m : ℕ} (x : Fin (n * m) → Bool) (i : Fin n) : ℝ :=
  (∑ r : Fin m, spin (x (finProdFinEquiv (i, r)))) / m

theorem sum_replicate {n m : ℕ} (hm : 0 < m) (v : Fin n → ℝ) :
    (∑ j, replicate m v j) = ∑ i, v i := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← (finProdFinEquiv (m := n) (n := m)).sum_comp]
  simp only [replicate, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem linear_replicate {n m : ℕ} (v : Fin n → ℝ) (x : Fin (n * m) → Bool) :
    linear (replicate m v) x = ∑ i, v i * means x i := by
  unfold linear
  rw [← (finProdFinEquiv (m := n) (n := m)).sum_comp]
  simp only [Fintype.sum_prod_type, replicate, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [means, ← Finset.mul_sum]
  ring

theorem replicate_mass {n m : ℕ} (hm : 0 < m) (s b : Fin n → ℝ)
    (hs : ∀ i, |b i| < s i) (j : Fin (n * m)) :
    |replicate m b j| < replicate m s j := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  simp only [replicate, abs_div, abs_of_pos hm']
  exact div_lt_div_of_pos_right (hs _) hm'

def replicatedAtom {n m : ℕ} (hm : 0 < m) (s b : Fin n → ℝ)
    (hs : ∀ i, |b i| < s i) (hd : ∑ i, s i < 1) : PureRoPEAtom (n * m) :=
  atom (replicate m s) (replicate m b) 1 0 1 0 (replicate_mass hm s b hs)
    (by rw [sum_replicate hm]; exact hd)

theorem replicatedAtom_eval {n m : ℕ} (hm : 0 < m) (s b : Fin n → ℝ)
    (hs : ∀ i, |b i| < s i) (hd : ∑ i, s i < 1) (x : Fin (n * m) → Bool) :
    (replicatedAtom hm s b hs hd).eval x =
      (∑ i, s i * means x i) / (1 + ∑ i, b i * means x i) := by
  unfold replicatedAtom
  rw [atom_eval]
  simp only [one_mul, zero_mul, add_zero, zero_add, linear_replicate]

def baseS (h : Fin 3) (i : Fin 14) : ℝ := ((i.val + 1 : ℕ) : ℝ) ^ h.val / 10000

def baseB (h : Fin 3) (i : Fin 14) : ℝ :=
  (((i.val + 1 : ℕ) : ℝ) ^ (h.val + 3) - (15 / 2 : ℝ) ^ (h.val + 3)) / 1000000000

theorem base_mass : ∀ h i, |baseB h i| < baseS h i := by
  intro h i
  fin_cases h <;> fin_cases i <;> norm_num [baseB, baseS, abs_lt]

theorem base_sum : ∀ h, ∑ i, baseS h i < 1 := by
  intro h
  fin_cases h <;> norm_num [baseS, Fin.sum_univ_succ]

def pureAtoms {m : ℕ} (hm : 0 < m) (h : Fin 3) : PureRoPEAtom (14 * m) :=
  replicatedAtom hm (baseS h) (baseB h) (base_mass h) (base_sum h)

def score {m : ℕ} (c : ℝ) (x : Fin (14 * m) → Bool) : ℝ :=
  c + ∑ h : Fin 3,
    (∑ i, baseS h i * means x i) / (1 + ∑ i, baseB h i * means x i)

def function {m : ℕ} (c : ℝ) (x : Fin (14 * m) → Bool) : Bool := by
  classical
  exact decide (0 < score c x)

theorem pureAtoms_score {m : ℕ} (hm : 0 < m) (c : ℝ) (x : Fin (14 * m) → Bool) :
    c + ∑ h, (pureAtoms hm h).eval x = score c x := by
  simp only [pureAtoms, replicatedAtom_eval, score]

theorem pureRoPEComputable_three {m : ℕ} (hm : 0 < m) (c : ℝ) :
    pureRoPEComputable (14 * m) 3 (function c) := by
  refine ⟨pureAtoms hm, c, ?_⟩
  intro x
  rw [pureAtoms_score]
  simp [function]

def numerator {m : ℕ} (x : Fin (14 * m) → Bool) (h : Fin 3) : ℝ :=
  ∑ i, baseS h i * means x i

def denominator {m : ℕ} (x : Fin (14 * m) → Bool) (h : Fin 3) : ℝ :=
  1 + ∑ i, baseB h i * means x i

theorem denominator_positive {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool)
    (h : Fin 3) : 0 < denominator x h := by
  have hp := (pureAtoms hm h).denominator_pos x
  have he : (pureAtoms hm h).toAffineFraction.denominator x = denominator x h := by
    rw [PureRoPEAtom.denominator_eq]
    unfold pureAtoms replicatedAtom
    rw [atom_denominator, linear_replicate]
    rfl
  rwa [he] at hp

def clearedScore {m : ℕ} (c : ℝ) (x : Fin (14 * m) → Bool) : ℝ :=
  ThreeHeadCubicFace.cleared c (numerator x) (denominator x)

theorem clearedScore_eq {m : ℕ} (hm : 0 < m) (c : ℝ) (x : Fin (14 * m) → Bool) :
    clearedScore c x = denominator x 0 * denominator x 1 * denominator x 2 * score c x := by
  unfold clearedScore
  rw [ThreeHeadCubicFace.cleared_eq _ _ _ (fun h ↦ (denominator_positive hm x h).ne')]
  rfl

theorem full_cube_sign {m : ℕ} (hm : 0 < m) (c : ℝ) (x : Fin (14 * m) → Bool) :
    0 < clearedScore c x ↔ function c x = true := by
  rw [clearedScore_eq hm]
  rw [mul_pos_iff_of_pos_left (mul_pos
    (mul_pos (denominator_positive hm x 0) (denominator_positive hm x 1))
    (denominator_positive hm x 2))]
  simp [function]

def replicationCount : ℕ := 2 ^ 400000

theorem replicationCount_positive : 0 < replicationCount := by
  exact pow_pos (by decide : 0 < (2 : ℕ)) _

def bias (m : ℕ) : ℝ :=
  -1 / (16 * 10000 * (32 * 1000000000 : ℝ) ^ 2 * (m : ℝ) ^ 3)

def explicitFunction : (Fin (14 * replicationCount) → Bool) → Bool :=
  function (bias replicationCount)

theorem explicitFunction_pure_three :
    pureRoPEComputable (14 * replicationCount) 3 explicitFunction :=
  pureRoPEComputable_three replicationCount_positive _

theorem explicitFunction_full_cube_sign (x : Fin (14 * replicationCount) → Bool) :
    0 < clearedScore (bias replicationCount) x ↔ explicitFunction x = true :=
  full_cube_sign replicationCount_positive _ x

end

end HeadComplexity.PureRoPEReplication
