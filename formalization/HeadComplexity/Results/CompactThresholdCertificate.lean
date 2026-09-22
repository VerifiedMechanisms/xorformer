import HeadComplexity.Results.DeterminantFeatureBridge

set_option linter.style.header false

/-!
# Compact threshold determinant certificates

This file specializes the determinant-feature bridge to the explicit
denominator and feature-selection formulas in theorem note 25.  The only
remaining premises are the ten finite modular determinant computations.  They
are stated as exact equalities to the residues recorded in the note, rather
than trusted as external conclusions.
-/

namespace HeadComplexity

open Finset

/-- The dimension-counting head value from theorem note 25. -/
def compactHeadCount (n : ℕ) : ℕ :=
  ((2 ^ n - 1) + n - 1) / n

/-- Number of features taken from the final denominator block. -/
def compactResidualCount (n : ℕ) : ℕ :=
  2 ^ n - (1 + n * (compactHeadCount n - 1))

/-- The constant coefficient of every generated denominator. -/
def compactDenConst (n : ℕ) : Fin (compactHeadCount n) → ℤ :=
  fun _ ↦ 1

/-- The one-based modular coefficient formula from theorem note 25, translated
to Lean's zero-based finite indices. -/
def compactDenCoeff (n : ℕ) :
    Fin (compactHeadCount n) → Fin n → ℤ :=
  fun h i ↦ ((1 +
    (((h.val + 3) ^ (i.val + 2) + 13 * (i.val + 1)) % 997) % 99 : ℕ) : ℤ)

/-- The selected cleared features in the order used by the determinant
certificate: the full product, followed blockwise by `1, x₁, ..., xₙ₋₁`.
The last block is automatically truncated by the size of the cube index. -/
def compactSelected (n : ℕ) :
    BooleanCubeIndex n → ClearedFeatureIndex n (compactHeadCount n) := by
  classical
  intro column
  by_cases hn : 0 < n
  · by_cases hzero : column.val = 0
    · exact none
    · let block := (column.val - 1) / n
      let offset := (column.val - 1) % n
      by_cases hblock : block < compactHeadCount n
      · refine some (⟨block, hblock⟩, ?_)
        by_cases hoffset : offset = 0
        · exact none
        · exact some ⟨offset - 1, by
            have hlt : offset < n := Nat.mod_lt _ hn
            omega⟩
      · exact none
  · exact none

/-- Recorded determinant residue modulo `1000003`. Outside dimensions three
through twelve, zero is used because theorem note 25 makes no claim. -/
def compactDeterminantResidue : ℕ → ℕ
  | 3 => 517804
  | 4 => 364478
  | 5 => 833072
  | 6 => 319656
  | 7 => 831708
  | 8 => 685472
  | 9 => 46734
  | 10 => 954493
  | 11 => 163187
  | 12 => 205507
  | _ => 0

/-- The ten dimension-counting values displayed in theorem note 25. -/
theorem compactHeadCount_values :
    compactHeadCount 3 = 3 ∧ compactHeadCount 4 = 4 ∧
      compactHeadCount 5 = 7 ∧ compactHeadCount 6 = 11 ∧
      compactHeadCount 7 = 19 ∧ compactHeadCount 8 = 32 ∧
      compactHeadCount 9 = 57 ∧ compactHeadCount 10 = 103 ∧
      compactHeadCount 11 = 187 ∧ compactHeadCount 12 = 342 := by
  norm_num [compactHeadCount]

/-- The final-block sizes displayed in theorem note 25. -/
theorem compactResidualCount_values :
    compactResidualCount 3 = 1 ∧ compactResidualCount 4 = 3 ∧
      compactResidualCount 5 = 1 ∧ compactResidualCount 6 = 3 ∧
      compactResidualCount 7 = 1 ∧ compactResidualCount 8 = 7 ∧
      compactResidualCount 9 = 7 ∧ compactResidualCount 10 = 3 ∧
      compactResidualCount 11 = 1 ∧ compactResidualCount 12 = 3 := by
  norm_num [compactResidualCount, compactHeadCount]

theorem compactDenConst_pos (n : ℕ) (h : Fin (compactHeadCount n)) :
    0 < compactDenConst n h := by
  simp [compactDenConst]

theorem compactDenCoeff_pos (n : ℕ) (h : Fin (compactHeadCount n))
    (i : Fin n) : 0 < compactDenCoeff n h i := by
  unfold compactDenCoeff
  have hpos : 0 < 1 +
      (((h.val + 3) ^ (i.val + 2) + 13 * (i.val + 1)) % 997) % 99 := by
    omega
  exact_mod_cast hpos

/-- Each recorded residue is nonzero in the stated finite ring. -/
theorem compactDeterminantResidue_ne_zero
    (n : ℕ) (hlower : 3 ≤ n) (hupper : n ≤ 12) :
    (compactDeterminantResidue n : ZMod 1000003) ≠ 0 := by
  interval_cases n <;> decide

/-- The exact, dimension-specific numerical premise still to be supplied by a
kernel certificate. -/
def CompactDeterminantChecked (n : ℕ) : Prop :=
  (clearedFeatureMatrix
      (fun h ↦ (compactDenConst n h : ZMod 1000003))
      (fun h i ↦ (compactDenCoeff n h i : ZMod 1000003))
      (compactSelected n)).det =
    (compactDeterminantResidue n : ZMod 1000003)

/-- **Theorem 25, exact conditional form.** The explicit generated feature
matrix and its recorded modular residue imply the compact universal head
bound. All structural and positivity obligations are discharged here; only
the finite determinant equality remains a premise. -/
theorem HStar_le_compact_of_checked_determinant
    (n : ℕ) (hlower : 3 ≤ n) (hupper : n ≤ 12)
    (hchecked : CompactDeterminantChecked n)
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ compactHeadCount n := by
  apply ClearedFeatureDeterminantCertificate.HStar_le_of_integer_zmod_feature_det
    1000003 (compactDenConst n) (compactDenCoeff n)
    (compactDenConst_pos n) (compactDenCoeff_pos n) (compactSelected n)
  · rw [hchecked]
    exact compactDeterminantResidue_ne_zero n hlower hupper

/-- A modular right inverse for the explicit matrix is an alternative compact
kernel witness for the same universal conclusion. -/
theorem HStar_le_compact_of_rightInverse
    (n : ℕ)
    (rightInverse : MatrixRightInverseCertificate
      (clearedFeatureMatrix
        (fun h ↦ (compactDenConst n h : ZMod 1000003))
        (fun h i ↦ (compactDenCoeff n h i : ZMod 1000003))
        (compactSelected n)))
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ compactHeadCount n := by
  letI : Fact (1 < 1000003) := ⟨by norm_num⟩
  exact
    ClearedFeatureDeterminantCertificate.HStar_le_of_integer_zmod_feature_rightInverse
      1000003 (compactDenConst n) (compactDenCoeff n)
      (compactDenConst_pos n) (compactDenCoeff_pos n) (compactSelected n)
      rightInverse f

end HeadComplexity
