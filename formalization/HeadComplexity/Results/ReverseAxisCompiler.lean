import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
# A linear-cost reverse-orientation axis-zero compiler

Every real two-one-hot table has an exact interpolant with `r + 1` actual
atoms in dimension `r + s`. Its denominators have only slopes `-1` and `-2`.
This is a linear-cost baseline, not the requested superconstant head saving.
-/

namespace HeadComplexity

open scoped BigOperators

private theorem reverseAxis_bit_le_one (b : Bool) : boolToReal b ≤ 1 := by
  cases b <;> norm_num [boolToReal]

/-- The Boolean vector with precisely one true coordinate. -/
def reverseAxisOneHot {k : ℕ} (i : Fin k) : Fin k → Bool :=
  fun j ↦ decide (j = i)

/-- A common reverse-orientation denominator. -/
noncomputable def reverseAxisDenom {r s : ℕ}
    (z : Fin r → Bool) (w : Fin s → Bool) : ℝ :=
  (r + s : ℕ) + 2 - (∑ i, boolToReal (z i)) - ∑ j, boolToReal (w j)

/-- The row-dependent affine numerator. -/
noncomputable def reverseAxisNumerator {r s : ℕ} (M : Fin r → Fin s → ℝ)
    (i : Fin r) (w : Fin s → Bool) : ℝ :=
  ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) *
    ∑ j, M i j * boolToReal (w j)

/-- The cancellation score consists of `r` row heads and one common head. -/
noncomputable def reverseAxisScore {r s : ℕ} (M : Fin r → Fin s → ℝ)
    (z : Fin r → Bool) (w : Fin s → Bool) : ℝ :=
  (∑ i, reverseAxisNumerator M i w /
    (reverseAxisDenom z w - boolToReal (z i))) -
    (∑ i, reverseAxisNumerator M i w) / reverseAxisDenom z w

@[simp] theorem reverseAxisScore_zero_left {r s : ℕ}
    (M : Fin r → Fin s → ℝ) (w : Fin s → Bool) :
    reverseAxisScore M (fun _ ↦ false) w = 0 := by
  simp [reverseAxisScore, boolToReal, Finset.sum_div]

@[simp] theorem reverseAxisScore_zero_right {r s : ℕ}
    (M : Fin r → Fin s → ℝ) (z : Fin r → Bool) :
    reverseAxisScore M z (fun _ ↦ false) = 0 := by
  simp [reverseAxisScore, reverseAxisNumerator, boolToReal]

/-- Both the common and all row denominators have a whole-cube positive margin. -/
theorem reverseAxisDenom_ge_two {r s : ℕ}
    (z : Fin r → Bool) (w : Fin s → Bool) :
    2 ≤ reverseAxisDenom z w := by
  have hz : (∑ i, boolToReal (z i)) ≤ (r : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin r, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦ reverseAxis_bit_le_one _
      _ = _ := by simp
  have hw : (∑ j, boolToReal (w j)) ≤ (s : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin s, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦ reverseAxis_bit_le_one _
      _ = _ := by simp
  simp only [reverseAxisDenom, Nat.cast_add]
  linarith

theorem reverseAxisRowDenom_ge_one {r s : ℕ}
    (z : Fin r → Bool) (w : Fin s → Bool) (i : Fin r) :
    1 ≤ reverseAxisDenom z w - boolToReal (z i) := by
  have := reverseAxisDenom_ge_two z w
  have := reverseAxis_bit_le_one (z i)
  linarith

@[simp] theorem reverseAxisDenom_oneHot {r s : ℕ} (i : Fin r) (j : Fin s) :
    reverseAxisDenom (reverseAxisOneHot i) (reverseAxisOneHot j) = (r + s : ℕ) := by
  simp [reverseAxisDenom, reverseAxisOneHot, boolToReal]
  ring

@[simp] theorem reverseAxisNumerator_oneHot {r s : ℕ}
    (M : Fin r → Fin s → ℝ) (i : Fin r) (j : Fin s) :
    reverseAxisNumerator M i (reverseAxisOneHot j) =
      ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) * M i j := by
  simp [reverseAxisNumerator, reverseAxisOneHot, boolToReal]

/-- Exact arbitrary real interpolation, stronger than grid sign interpolation. -/
theorem reverseAxisScore_oneHot {r s : ℕ} (M : Fin r → Fin s → ℝ)
    (i : Fin r) (j : Fin s) :
    reverseAxisScore M (reverseAxisOneHot i) (reverseAxisOneHot j) = M i j := by
  have hm : (2 : ℝ) ≤ (r + s : ℕ) := by
    have hi := i.isLt
    have hj := j.isLt
    exact_mod_cast (show 2 ≤ r + s by omega)
  have hm0 : ((r + s : ℕ) : ℝ) ≠ 0 := by linarith
  have hm1 : ((r + s : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  unfold reverseAxisScore
  rw [reverseAxisDenom_oneHot, Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ k : Fin r, if k = i then M i j else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp only [reverseAxisNumerator_oneHot, reverseAxisOneHot, decide_true,
          boolToReal, ↓reduceIte]
        field_simp
        ring
      · simp [reverseAxisOneHot, hki, boolToReal]
    _ = M i j := by simp

/-- A strictly labelled table has the corresponding strict grid signs. -/
theorem reverseAxisScore_strict_sign {r s : ℕ} (M : Fin r → Fin s → ℝ)
    (hM : ∀ i j, M i j ≠ 0) (i : Fin r) (j : Fin s) :
    0 < M i j * reverseAxisScore M (reverseAxisOneHot i) (reverseAxisOneHot j) := by
  rw [reverseAxisScore_oneHot]
  exact mul_self_pos.mpr (hM i j)

private theorem reverseAxis_num_affine {r s : ℕ}
    (M : Fin r → Fin s → ℝ) (i : Fin r)
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue 0 (Fin.addCases (fun _ ↦ 0)
      (fun j ↦ ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) * M i j))
      (Fin.addCases z w) = reverseAxisNumerator M i w := by
  simp [affineValue, Fin.sum_univ_add, reverseAxisNumerator, Finset.mul_sum, mul_assoc]

private theorem reverseAxis_base_affine {r s : ℕ}
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue (((r + s : ℕ) : ℝ) + 2) (fun _ ↦ -1)
      (Fin.addCases z w) = reverseAxisDenom z w := by
  simp [affineValue, Fin.sum_univ_add, reverseAxisDenom]
  ring

private theorem reverseAxis_row_affine {r s : ℕ} (i : Fin r)
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue (((r + s : ℕ) : ℝ) + 2)
      (Fin.addCases (fun k ↦ -1 - if k = i then 1 else 0) (fun _ ↦ -1))
      (Fin.addCases z w) = reverseAxisDenom z w - boolToReal (z i) := by
  simp [affineValue, Fin.sum_univ_add, reverseAxisDenom, sub_mul,
    Finset.sum_sub_distrib, ite_mul]
  ring

/-- The complete score is a sum of `r + 1` admissible atoms, with no bias,
no extra input coordinates, and no relaxation of atom admissibility. -/
theorem exists_reverseAxis_atoms {r s : ℕ} (M : Fin r → Fin s → ℝ) :
    ∃ φ : Fin (r + 1) → FracAtom (r + s), ∀ z w,
      (∑ h, (φ h).eval (Fin.addCases z w)) = reverseAxisScore M z w := by
  let c : ℝ := ((r + s : ℕ) : ℝ) + 2
  have hc : 0 < c := by dsimp [c]; positivity
  let nums : Fin r → Fin (r + s) → ℝ := fun i ↦
    Fin.addCases (fun _ ↦ 0)
      (fun j ↦ ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) * M i j)
  let slopes : Fin r → Fin (r + s) → ℝ := fun i ↦
    Fin.addCases (fun k ↦ -1 - if k = i then 1 else 0) (fun _ ↦ -1)
  have hs : ∀ i k, slopes i k < 0 := by
    intro i k
    refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k
    · simp only [slopes, Fin.addCases_left]
      split_ifs <;> norm_num
    · norm_num [slopes]
  have hmargin : ∀ i, (∑ k, -(slopes i k)) < c := by
    intro i
    simp [slopes, c, Fin.sum_univ_add, neg_sub, Nat.cast_add]
    linarith
  have hbmargin : (∑ _k : Fin (r + s), -(-1 : ℝ)) < c := by
    simp [c]
  have row_exists : ∀ i : Fin r, ∃ φ : FracAtom (r + s), ∀ z w,
      φ.eval (Fin.addCases z w) = reverseAxisNumerator M i w /
        (reverseAxisDenom z w - boolToReal (z i)) := by
    intro i
    refine ⟨FracAtom.ofNegativeAffineRatio 0 (nums i) c (slopes i)
      hc (hs i) (hmargin i), ?_⟩
    intro z w
    rw [FracAtom.ofNegativeAffineRatio_eval]
    change affineValue 0 (Fin.addCases (fun _ ↦ 0)
      (fun j ↦ ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) * M i j))
      (Fin.addCases z w) / affineValue (((r + s : ℕ) : ℝ) + 2)
      (Fin.addCases (fun k ↦ -1 - if k = i then 1 else 0) (fun _ ↦ -1))
      (Fin.addCases z w) = _
    rw [reverseAxis_num_affine, reverseAxis_row_affine]
  choose rows hrow using row_exists
  have common_exists : ∃ φ : FracAtom (r + s), ∀ z w,
      φ.eval (Fin.addCases z w) =
        -(∑ i, reverseAxisNumerator M i w) / reverseAxisDenom z w := by
    refine ⟨FracAtom.ofNegativeAffineRatio 0 (fun k ↦ -∑ i, nums i k)
      c (fun _ ↦ -1) hc (by intro; norm_num) hbmargin, ?_⟩
    intro z w
    rw [FracAtom.ofNegativeAffineRatio_eval]
    rw [show affineValue c (fun _ ↦ -1) (Fin.addCases z w) =
      reverseAxisDenom z w from reverseAxis_base_affine z w]
    congr 1
    simp only [affineValue, zero_add, neg_mul, Finset.sum_neg_distrib]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [affineValue, zero_add] using reverseAxis_num_affine M i z w
  obtain ⟨common, hcommon⟩ := common_exists
  refine ⟨Fin.cases common rows, fun z w ↦ ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  simp_rw [hrow]
  rw [hcommon]
  simp only [reverseAxisScore, neg_div]
  ring

/-- Every real table is interpolated exactly by `r + 1` actual atoms, with
simultaneous exact zeros on the two Boolean coordinate axes. -/
theorem exists_reverseAxis_exact_compiler {r s : ℕ}
    (M : Fin r → Fin s → ℝ) :
    ∃ φ : Fin (r + 1) → FracAtom (r + s),
      (∀ i j, (∑ h, (φ h).eval (Fin.addCases (reverseAxisOneHot i)
        (reverseAxisOneHot j))) = M i j) ∧
      (∀ w, (∑ h, (φ h).eval (Fin.addCases (fun _ ↦ false) w)) = 0) ∧
      (∀ z, (∑ h, (φ h).eval (Fin.addCases z (fun _ ↦ false))) = 0) := by
  obtain ⟨φ, hφ⟩ := exists_reverseAxis_atoms M
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro i j
    rw [hφ, reverseAxisScore_oneHot]
  · intro w
    rw [hφ, reverseAxisScore_zero_left]
  · intro z
    rw [hφ, reverseAxisScore_zero_right]

end HeadComplexity
