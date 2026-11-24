import HeadComplexity.Results.CubeStarTransfer

set_option linter.style.header false

/-!
# Admissible joint permutation banks

Every column chooses its permutation independently. One bank has H heads,
irrespective of the number of columns. All slopes are strictly negative,
all full-cube denominators are positive, and the zero-column axis is exact.
This construction asserts no orthant-covering property of the permutations.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

noncomputable def jointFamilyPermutationWeight {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (π : Fin s → Equiv.Perm (Fin H))
    (h : Fin H) : Fin (k + s) → ℝ :=
  Fin.addCases (d h) (fun j ↦ ((π j h).val + 1 : ℝ))

noncomputable def jointFamilyPermutationCap {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) : ℝ :=
  (∑ h : Fin H, ∑ i : Fin k, d h i) + (s : ℝ) * H

theorem jointFamilyPermutationWeight_pos {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (h : Fin H) (i : Fin (k + s)) :
    0 < jointFamilyPermutationWeight d π h i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [jointFamilyPermutationWeight, Fin.addCases_left] using hd h j
  · intro j
    simp only [jointFamilyPermutationWeight, Fin.addCases_right]
    positivity

theorem jointFamilyPermutationWeight_bound {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (h : Fin H) (bits : Fin (k + s) → Bool) :
    (∑ i, jointFamilyPermutationWeight d π h i * boolToReal (bits i)) ≤
      jointFamilyPermutationCap (s := s) d := by
  have hrow : (∑ i : Fin k, d h i) ≤ ∑ h' : Fin H, ∑ i : Fin k, d h' i := by
    exact Finset.single_le_sum
      (fun h' _ ↦ Finset.sum_nonneg (fun i _ ↦ (hd h' i).le)) (Finset.mem_univ h)
  have hcol : (∑ j : Fin s, ((π j h).val + 1 : ℝ)) ≤ (s : ℝ) * H := by
    calc
      _ ≤ ∑ _j : Fin s, (H : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact_mod_cast Nat.succ_le_of_lt (π j h).isLt
      _ = _ := by simp
  calc
    _ ≤ ∑ i, jointFamilyPermutationWeight d π h i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_right
        (jointFamilyPermutationWeight_pos d hd π h i).le (boolToReal_le_one _)
    _ = (∑ i : Fin k, d h i) + ∑ j : Fin s, ((π j h).val + 1 : ℝ) := by
      simp only [Fin.sum_univ_add, jointFamilyPermutationWeight,
        Fin.addCases_left, Fin.addCases_right]
    _ ≤ jointFamilyPermutationCap (s := s) d := add_le_add hrow hcol

/-- A common base denominator works for every independently selected column
permutation, including simultaneous multihot column inputs. -/
noncomputable def jointFamilyPermutationBankData {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (c : Fin H → Fin s → ℝ)
    (ε : ℝ) (hε : 0 < ε) : ReverseCubeStarData k s H where
  a₀ := fun _ ↦ 0
  b₀ := fun _ ↦ 1 + ε * jointFamilyPermutationCap (s := s) d
  a := fun h ↦ Fin.addCases (fun _ ↦ 0) (c h)
  b := fun h i ↦ -ε * jointFamilyPermutationWeight d π h i
  positive := by
    intro h bits
    have hb := jointFamilyPermutationWeight_bound d hd π h bits
    simp only [affineValue, neg_mul, Finset.sum_neg_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    nlinarith
  negative := fun h i ↦ mul_neg_of_neg_of_pos (neg_neg_of_pos hε)
    (jointFamilyPermutationWeight_pos d hd π h i)
  zero_column := by
    intro x
    apply Finset.sum_eq_zero
    intro h _
    have hn : affineValue 0 (Fin.addCases (fun _ : Fin k ↦ 0) (c h))
        (Fin.addCases x (fun _ : Fin s ↦ false)) = 0 := by
      simp [affineValue, Fin.sum_univ_add, boolToReal]
    rw [hn, zero_div]

theorem jointFamilyPermutationBankData_score {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (c : Fin H → Fin s → ℝ)
    (ε : ℝ) (hε : 0 < ε) (x : Fin k → Bool) (j : Fin s) :
    (jointFamilyPermutationBankData d hd π c ε hε).score (cubeStarInput x j) =
      ∑ h, c h j / (1 + ε * jointFamilyPermutationCap (s := s) d -
        ε * ((∑ i : Fin k, d h i * boolToReal (x i)) + ((π j h).val + 1 : ℝ))) := by
  unfold ReverseCubeStarData.score jointFamilyPermutationBankData
  apply Finset.sum_congr rfl
  intro h _
  have hn : affineValue 0 (Fin.addCases (fun _ : Fin k ↦ 0) (c h))
      (cubeStarInput x j) = c h j := by
    simp [affineValue, cubeStarInput, Fin.sum_univ_add, boolToReal]
  rw [hn]
  congr 1
  simp only [affineValue, cubeStarInput, Fin.sum_univ_add, jointFamilyPermutationWeight,
    Fin.addCases_left, Fin.addCases_right]
  simp only [neg_mul, Finset.sum_neg_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp [boolToReal]
  ring

/-- Concatenation keeps the exact zero axis and the full-cube denominator
conditions. In particular subtracting a fixed H-head reference costs H
additional heads shared over all independently chosen columns. -/
noncomputable def jointFamilyAppendData {k s H K : ℕ}
    (L : ReverseCubeStarData k s H) (M : ReverseCubeStarData k s K) :
    ReverseCubeStarData k s (H + K) where
  a₀ := Fin.addCases L.a₀ M.a₀
  b₀ := Fin.addCases L.b₀ M.b₀
  a := Fin.addCases L.a M.a
  b := Fin.addCases L.b M.b
  positive := by
    intro h bits
    refine Fin.addCases ?_ ?_ h
    · intro i
      simpa only [Fin.addCases_left] using L.positive i bits
    · intro i
      simpa only [Fin.addCases_right] using M.positive i bits
  negative := by
    intro h i
    refine Fin.addCases ?_ ?_ h
    · intro j
      simpa only [Fin.addCases_left] using L.negative j i
    · intro j
      simpa only [Fin.addCases_right] using M.negative j i
  zero_column := by
    intro x
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [L.zero_column, M.zero_column, add_zero]

theorem jointFamilyAppendData_score {k s H K : ℕ}
    (L : ReverseCubeStarData k s H) (M : ReverseCubeStarData k s K)
    (bits : Fin (k + s) → Bool) :
    (jointFamilyAppendData L M).score bits = L.score bits + M.score bits := by
  simp only [ReverseCubeStarData.score, jointFamilyAppendData,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

/-- The fixed reference permutation is shared by all columns. The chosen
permutations remain completely independent. -/
noncomputable def jointFamilyPermutationDifferenceData {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (σ : Equiv.Perm (Fin H))
    (ε : ℝ) (hε : 0 < ε) : ReverseCubeStarData k s (H + H) :=
  jointFamilyAppendData
    (jointFamilyPermutationBankData d hd π (fun _ _ ↦ 1) ε hε)
    (jointFamilyPermutationBankData d hd (fun _ ↦ σ) (fun _ _ ↦ -1) ε hε)

theorem jointFamilyPermutationDifferenceData_score {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (σ : Equiv.Perm (Fin H))
    (ε : ℝ) (hε : 0 < ε) (x : Fin k → Bool) (j : Fin s) :
    (jointFamilyPermutationDifferenceData d hd π σ ε hε).score (cubeStarInput x j) =
      (∑ h, 1 / (1 + ε * jointFamilyPermutationCap (s := s) d -
        ε * ((∑ i : Fin k, d h i * boolToReal (x i)) + ((π j h).val + 1 : ℝ)))) -
      (∑ h, 1 / (1 + ε * jointFamilyPermutationCap (s := s) d -
        ε * ((∑ i : Fin k, d h i * boolToReal (x i)) + ((σ h).val + 1 : ℝ)))) := by
  rw [jointFamilyPermutationDifferenceData, jointFamilyAppendData_score,
    jointFamilyPermutationBankData_score, jointFamilyPermutationBankData_score]
  simp only [neg_div, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Every column has an exact additional zero at the all-zero row, because
permutations preserve the reciprocal histogram there. -/
theorem jointFamilyPermutationDifferenceData_zero_row {k s H : ℕ}
    (d : Fin H → Fin k → ℝ) (hd : ∀ h i, 0 < d h i)
    (π : Fin s → Equiv.Perm (Fin H)) (σ : Equiv.Perm (Fin H))
    (ε : ℝ) (hε : 0 < ε) (j : Fin s) :
    (jointFamilyPermutationDifferenceData d hd π σ ε hε).score
      (cubeStarInput (fun _ ↦ false) j) = 0 := by
  rw [jointFamilyPermutationDifferenceData_score]
  simp only [boolToReal, Bool.false_eq_true, ite_false, mul_zero,
    Finset.sum_const_zero, zero_add]
  let f : Fin H → ℝ := fun h ↦
    1 / (1 + ε * jointFamilyPermutationCap (s := s) d - ε * (h.val + 1 : ℝ))
  change (∑ h, f (π j h)) - (∑ h, f (σ h)) = 0
  rw [Equiv.sum_comp (π j) f, Equiv.sum_comp σ f, sub_self]

end HeadComplexity.AxisZeroGluing
