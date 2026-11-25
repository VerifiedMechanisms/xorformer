import HeadComplexity.Polynomial.RoPEGeneralPhysicalCoordinates
import HeadComplexity.Polynomial.ReplicatedThresholdDegree
import HeadComplexity.Results.RoPEArchitecturalComparison

set_option linter.style.header false

/-!
# Exact threshold degree and pure head minima at every positive head count

For each fixed positive H, the explicit replicated source has threshold
degree and pure head minimum exactly H for all sufficiently large replication
counts. This result is independent of the general-H vanilla tensor obstruction.
-/

namespace HeadComplexity.PureGeneralReplicatedGrid

open scoped BigOperators Topology
open MvPolynomial Filter
open RoPEGeneralPhysicalCoordinates

/-- A centered group mean always lies in the continuous cube. -/
theorem coordinate_abs_le_one {H m : ℕ} (hm : 0 < m)
    (x : Fin (groupCount H * m) → Bool) (g : Fin (groupCount H)) :
    |coordinate x g| ≤ 1 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [coordinate, abs_div, abs_of_pos hm', div_le_one hm']
  calc
    |∑ r : Fin m, (2 * boolToReal (x (finProdFinEquiv (g, r))) - 1)| ≤
        ∑ r : Fin m, |2 * boolToReal (x (finProdFinEquiv (g, r))) - 1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      cases hx : x (finProdFinEquiv (g, r)) <;> norm_num [boolToReal, hx]
    _ = m := by simp

/-- The cleared physical polynomial is the source score times a positive
product of denominators on the continuous cube. -/
theorem eval_physical_eq_score_mul (h : ℕ) (q : Input h → ℝ)
    (hq : ∀ g, |q g| ≤ 1) :
    eval q (physical h) = score q * ∏ i : Fin (h + 1), denominator i q := by
  rw [eval_physical, score, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hdi : denominator i q ≠ 0 := (denominator_pos i q hq).ne'
  have hprod := Finset.prod_erase_mul Finset.univ (fun j ↦ denominator j q)
    (Finset.mem_univ i)
  rw [div_mul_eq_mul_div, eq_div_iff hdi]
  rw [mul_assoc, hprod]

theorem eval_physical_pos_iff (h : ℕ) (q : Input h → ℝ)
    (hq : ∀ g, |q g| ≤ 1) : 0 < eval q (physical h) ↔ 0 < score q := by
  rw [eval_physical_eq_score_mul h q hq]
  exact mul_pos_iff_of_pos_right (Finset.prod_pos (fun i _ ↦ denominator_pos i q hq))

theorem physical_classifier_eq (h m : ℕ) (hm : 0 < m) :
    ReplicatedThresholdDegree.classifier (fun q ↦ eval q (physical h)) m =
      classifier (h + 1) m := by
  funext x
  have hmean : RoPEGroupSymmetrization.mean
      (fun p : Input h × Fin m ↦ x (finProdFinEquiv p)) = coordinate x := rfl
  simp only [ReplicatedThresholdDegree.classifier, hmean, classifier]
  exact decide_eq_decide.mpr (eval_physical_pos_iff h _ (coordinate_abs_le_one hm x))

/-- The explicit source eventually excludes every smaller threshold degree. -/
theorem eventually_not_lower_threshold_degree (h : ℕ) :
    ∀ᶠ m in atTop, ¬ ThresholdDegLE (classifier (h + 1) m) h := by
  have he := ReplicatedThresholdDegree.eventually_not_thresholdDegLE
    (fun q ↦ eval q (physical h)) (physical h).continuous_eval
    (fun Q hQ hdeg hweak ↦ no_lower_degree_weak_sign_cube h Q hQ hdeg hweak)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  rw [physical_classifier_eq h m hmpos] at hm
  exact hm

/-- Every positive head count occurs as the exact threshold degree and pure
minimum of the explicit finite Boolean source family, eventually in m. -/
theorem eventually_exact_degree_and_pure_minima (h : ℕ) :
    ∀ᶠ m in atTop,
      thresholdDeg (classifier (h + 1) m) = h + 1 ∧
      PureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 ∧
      StandardPureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 ∧
      FreePureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 := by
  classical
  filter_upwards [eventually_not_lower_threshold_degree h,
    eventually_gt_atTop (0 : ℕ)] with m hl hm
  have hc := pure_computable (h + 1) m hm
  have hdeg := thresholdDegLE_of_pureRoPEComputable hc
  have hex : ∃ d, ThresholdDegLE (classifier (h + 1) m) d := ⟨h + 1, hdeg⟩
  have he : thresholdDeg (classifier (h + 1) m) = Nat.find hex := by
    unfold thresholdDeg
    rw [dif_pos hex]
  have hdu := Nat.find_min' hex hdeg
  have hdl : ¬ Nat.find hex ≤ h := by
    intro hh
    obtain ⟨P, hP, hs⟩ := Nat.find_spec hex
    exact hl ⟨P, hP.trans hh, hs⟩
  have hd : thresholdDeg (classifier (h + 1) m) = h + 1 := by omega
  have hpu : PureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) ≤ h + 1 :=
    Nat.find_min' (exists_pureRoPEComputable _) hc
  have hpl : ¬ PureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) ≤ h := by
    intro hh
    obtain ⟨P, hP, hs⟩ := thresholdDegLE_of_pureRoPEComputable
      (pureRoPEHStar_computable (classifier (h + 1) m))
    exact hl ⟨P, hP.trans hh, hs⟩
  have hp : PureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 := by omega
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hd, hp, hp, hp⟩

theorem eventually_exact_degree_and_pure_minima_of_pos (H : ℕ) (hH : 0 < H) :
    ∀ᶠ m in atTop,
      thresholdDeg (classifier H m) = H ∧
      PureRoPEHStar (groupCount H * m) (classifier H m) = H ∧
      StandardPureRoPEHStar (groupCount H * m) (classifier H m) = H ∧
      FreePureRoPEHStar (groupCount H * m) (classifier H m) = H := by
  cases H with
  | zero => omega
  | succ h => exact eventually_exact_degree_and_pure_minima h

end HeadComplexity.PureGeneralReplicatedGrid
