import HeadComplexity.Results.PureRoPEReplicationStrict
import HeadComplexity.Results.PureRoPETwoHeads

set_option linter.style.header false

/-! # A strictly oriented denominator in the explicit cubic pencil -/

namespace HeadComplexity.PureCubicOrientedBase

noncomputable section

open scoped BigOperators
open RoPETwoHead PureRoPEReplication PureRoPEReplicationStrict

def centeredForm {n : ℕ} (c : ℝ) (v : Fin n → ℝ) : Form n :=
  ⟨c - ∑ i, v i, fun i ↦ 2 * v i⟩

theorem centeredForm_eval {n : ℕ} (c : ℝ) (v : Fin n → ℝ)
    (x : Fin n → Bool) :
    (centeredForm c v).eval x = c + PureRoPECenteredConstruction.linear v x := by
  have hi (i : Fin n) : v i * PureRoPECenteredConstruction.spin (x i) =
      2 * v i * boolToReal (x i) - v i := by
    cases x i <;> simp [PureRoPECenteredConstruction.spin, boolToReal]
    ring
  simp only [Form.eval, centeredForm, PureRoPECenteredConstruction.linear,
    hi, Finset.sum_sub_distrib]
  ring

def numeratorForm {m : ℕ} (h : Fin 3) : Form (14 * m) :=
  centeredForm 0 (replicate m (baseS h))

def denominatorForm {m : ℕ} (h : Fin 3) : Form (14 * m) :=
  centeredForm 1 (replicate m (baseB h))

@[simp] theorem numeratorForm_eval {m : ℕ} (h : Fin 3) (x : Fin (14 * m) → Bool) :
    (numeratorForm h).eval x = PureRoPEReplication.numerator x h := by
  rw [numeratorForm, centeredForm_eval, linear_replicate]
  simp [PureRoPEReplication.numerator]

@[simp] theorem denominatorForm_eval {m : ℕ} (h : Fin 3) (x : Fin (14 * m) → Bool) :
    (denominatorForm h).eval x = PureRoPEReplication.denominator x h := by
  rw [denominatorForm, centeredForm_eval, linear_replicate]
  rfl

def baseSlope (i : Fin 14) : ℝ := 10 * baseB 0 i - baseB 1 i

theorem baseSlope_negative (i : Fin 14) : baseSlope i < 0 := by
  fin_cases i <;> norm_num [baseSlope, baseB]

theorem baseSlope_margin (i : Fin 14) :
    (411 : ℝ) / 16000000000 ≤ -baseSlope i := by
  fin_cases i <;> norm_num [baseSlope, baseB]

theorem baseSlope_mass : (∑ i, |baseSlope i|) = 257621 / (8000000000 : ℝ) := by
  norm_num [baseSlope, baseB, Fin.sum_univ_succ]

def baseForm {m : ℕ} : Form (14 * m) :=
  (denominatorForm 0).lin (denominatorForm 1) 10 (-1)

theorem baseForm_relation {m : ℕ} (x : Fin (14 * m) → Bool) :
    baseForm.eval x = 10 * (denominatorForm 0).eval x - (denominatorForm 1).eval x := by
  rw [baseForm, Form.lin_eval]
  ring

theorem baseForm_eval {m : ℕ} (x : Fin (14 * m) → Bool) :
    baseForm.eval x = 9 + ∑ i, baseSlope i * means x i := by
  rw [baseForm_relation, denominatorForm_eval, denominatorForm_eval]
  simp only [PureRoPEReplication.denominator, baseSlope, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem baseForm_slopes {m : ℕ} (hm : 0 < m) (j : Fin (14 * m)) :
    baseForm.v j < 0 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hj := baseSlope_negative ((finProdFinEquiv (m := 14) (n := m)).symm j).1
  have he : baseForm.v j = 2 * baseSlope
      ((finProdFinEquiv (m := 14) (n := m)).symm j).1 / m := by
    simp only [baseForm, Form.lin, denominatorForm, centeredForm, replicate, baseSlope]
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hj) hm'

theorem baseForm_gt_eight {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) :
    8 < baseForm.eval x := by
  have hb : |∑ i, baseSlope i * means x i| ≤ ∑ i, |baseSlope i| := by
    calc
      _ ≤ ∑ i, |baseSlope i * means x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |baseSlope i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left (means_abs_le_one hm x i)
          (abs_nonneg (baseSlope i))
  rw [baseSlope_mass] at hb
  rw [baseForm_eval]
  have hh := neg_le_abs (∑ i, baseSlope i * means x i)
  linarith

end
end HeadComplexity.PureCubicOrientedBase
