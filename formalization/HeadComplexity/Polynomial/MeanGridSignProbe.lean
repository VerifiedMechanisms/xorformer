import HeadComplexity.Polynomial.PolynomialCubeLipschitz
import Mathlib.Algebra.Order.Round

set_option linter.style.header false

/-! # Finite mean-grid rounding and quantitative sign probes -/

namespace HeadComplexity.MeanGridSignProbe
noncomputable section
open scoped BigOperators
open MvPolynomial PolynomialCubeLipschitz

def gridValue (m : ℕ) (k : Fin (m + 1)) : ℝ := -1 + 2 * (k.val : ℝ) / m

theorem gridValue_abs_le_one (m : ℕ) (hm : 0 < m) (k : Fin (m + 1)) :
    |gridValue m k| ≤ 1 := by
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : (k.val : ℝ) ≤ m := by exact_mod_cast (by omega : k.val ≤ m)
  have hn : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  apply abs_le.mpr
  unfold gridValue
  have hlow : (0 : ℝ) ≤ 2 * k.val / m := by positivity
  have hhigh : 2 * (k.val : ℝ) / m ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  constructor <;> linarith

theorem exists_grid_near (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : |x| ≤ 1) :
    ∃ k : Fin (m + 1), |x - gridValue m k| ≤ 1 / m := by
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  let u : ℝ := (m : ℝ) * (x + 1) / 2
  let r : ℤ := round u
  have hu0 : 0 ≤ u := by dsimp [u]; nlinarith [(abs_le.mp hx).1]
  have hum : u ≤ m := by dsimp [u]; nlinarith [(abs_le.mp hx).2]
  have hr : |u - (r : ℝ)| ≤ 1 / 2 := abs_sub_round u
  have hr0 : 0 ≤ r := by
    by_contra hn
    have hi : r ≤ -1 := by omega
    have hir : (r : ℝ) ≤ -1 := by exact_mod_cast hi
    linarith [(abs_le.mp hr).2]
  have hrm : r ≤ m := by
    by_contra hn
    have hi : (m : ℤ) + 1 ≤ r := by omega
    have hir : (m : ℝ) + 1 ≤ r := by exact_mod_cast hi
    linarith [(abs_le.mp hr).1]
  let k : Fin (m + 1) := ⟨r.toNat, by omega⟩
  have hk : (k.val : ℝ) = r := by
    dsimp [k]
    exact_mod_cast Int.toNat_of_nonneg hr0
  refine ⟨k, ?_⟩
  have heq : x - gridValue m k = (2 / m) * (u - r) := by
    unfold gridValue
    rw [hk]
    dsimp [u]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos (div_pos (by norm_num) hp)]
  calc
    _ ≤ ((2 : ℝ) / m) * (1 / 2) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (1 : ℝ) / m := by ring

theorem exists_grid_vector_near {n : ℕ} (m : ℕ) (hm : 0 < m)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∃ k : Fin n → Fin (m + 1), ∀ i, |x i - gridValue m (k i)| ≤ 1 / m := by
  classical
  exact Classical.axiomOfChoice (fun i ↦ exists_grid_near m hm (x i) (hx i))

/-- Opposite signs at two nearby samples bound the value at the bracketed point.
The negative label may be weak, as in the model's strict-positive classifier. -/
theorem bracket_value_bound (q qplus qminus L : ℝ)
    (hp : 0 < qplus) (hm : qminus ≤ 0)
    (hplus : |q - qplus| ≤ L) (hminus : |q - qminus| ≤ L) : |q| ≤ L := by
  apply abs_le.mpr
  constructor
  · linarith [(abs_le.mp hplus).1]
  · linarith [(abs_le.mp hminus).2]

/-- Once the two target signs are robust to rounding, cubic coefficient bounds
force a small value of the competing polynomial at the zero-surface sample. -/
theorem rounded_probe_bound (F Q : MvPolynomial (Fin 14) ℝ)
    (hFdeg : F.totalDegree ≤ 3) (hQdeg : Q.totalDegree ≤ 3)
    (hFc : ∀ d, |F.coeff d| ≤ 1) (hQc : ∀ d, |Q.coeff d| ≤ 1)
    (m : ℕ) (hm : 0 < m) (a xp xm : Fin 14 → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hxp : ∀ i, |xp i| ≤ 1) (hxm : ∀ i, |xm i| ≤ 1)
    (hdp : ∀ i, |xp i - a i| ≤ (2 : ℝ) ^ 54 / m)
    (hdm : ∀ i, |xm i - a i| ≤ (2 : ℝ) ^ 54 / m)
    (hFp : (2 : ℝ) ^ 18 / m ≤ eval xp F)
    (hFm : eval xm F ≤ -((2 : ℝ) ^ 18 / m))
    (hsign : ∀ k : Fin 14 → Fin (m + 1),
      (0 < eval (fun i ↦ gridValue m (k i)) F ↔
        0 < eval (fun i ↦ gridValue m (k i)) Q)) :
    |eval a Q| < (2 : ℝ) ^ 67 / m := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hinv : (0 : ℝ) ≤ 1 / m := by positivity
  obtain ⟨kp, hkp⟩ := exists_grid_vector_near m hm xp hxp
  obtain ⟨km, hkm⟩ := exists_grid_vector_near m hm xm hxm
  let yp : Fin 14 → ℝ := fun i ↦ gridValue m (kp i)
  let ym : Fin 14 → ℝ := fun i ↦ gridValue m (km i)
  have hyp (i) : |yp i| ≤ 1 := gridValue_abs_le_one m hm _
  have hym (i) : |ym i| ≤ 1 := gridValue_abs_le_one m hm _
  have hFp' := cubic_fourteen_lipschitz F hFdeg xp yp (1 / m) hinv hxp hyp hkp hFc
  have hFm' := cubic_fourteen_lipschitz F hFdeg xm ym (1 / m) hinv hxm hym hkm hFc
  have hmargin : 2040 * (1 / (m : ℝ)) < (2 : ℝ) ^ 18 / m := by
    rw [mul_one_div]
    exact (div_lt_div_iff_of_pos_right hmr).mpr (by norm_num)
  have hFyp : 0 < eval yp F := by linarith [(abs_le.mp hFp').2]
  have hFym : eval ym F < 0 := by linarith [(abs_le.mp hFm').1]
  have hQyp : 0 < eval yp Q := (hsign kp).mp hFyp
  have hQym : eval ym Q ≤ 0 := by
    by_contra hn
    have hpos : 0 < eval ym Q := by linarith
    have hbad := (hsign km).mpr hpos
    linarith
  let r : ℝ := ((2 : ℝ) ^ 54 + 1) / m
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hap (i) : |a i - yp i| ≤ r := by
    calc
      _ ≤ |a i - xp i| + |xp i - yp i| := abs_sub_le _ _ _
      _ ≤ (2 : ℝ) ^ 54 / m + 1 / m := by
        exact add_le_add (by simpa [abs_sub_comm] using hdp i) (hkp i)
      _ = r := by dsimp [r]; ring
  have ham (i) : |a i - ym i| ≤ r := by
    calc
      _ ≤ |a i - xm i| + |xm i - ym i| := abs_sub_le _ _ _
      _ ≤ (2 : ℝ) ^ 54 / m + 1 / m := by
        exact add_le_add (by simpa [abs_sub_comm] using hdm i) (hkm i)
      _ = r := by dsimp [r]; ring
  have hqp := cubic_fourteen_lipschitz Q hQdeg a yp r hr ha hyp hap hQc
  have hqm := cubic_fourteen_lipschitz Q hQdeg a ym r hr ha hym ham hQc
  have hb := bracket_value_bound _ _ _ _ hQyp hQym hqp hqm
  apply hb.trans_lt
  dsimp [r]
  rw [← mul_div_assoc]
  exact (div_lt_div_iff_of_pos_right hmr).mpr (by norm_num)

end
end HeadComplexity.MeanGridSignProbe
