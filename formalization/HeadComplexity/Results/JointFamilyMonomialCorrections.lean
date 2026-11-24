import HeadComplexity.Results.CubeStarTransfer
import HeadComplexity.Atoms.AffineMonomialApproximation

set_option linter.style.header false

/-!
# Shared monomial corrections for full-cube row families

Each chosen positive monomial costs one reverse head, even when its coefficient
is chosen independently in every column. The zero-column axis is exact, and
all denominator slopes are negative with positive denominators on the entire
ambient Boolean cube. This makes the cost of cancelling a shared finite
feature space explicit; it does not assert that any residual family shatters.
-/

namespace HeadComplexity.AxisZeroGluing

open Filter
open scoped BigOperators

noncomputable def jointFamilyMissing {n : ℕ} (S : Finset (Fin n))
    (bits : Fin n → Bool) : ℝ :=
  ∑ i ∈ S, (1 - boolToReal (bits i))

theorem jointFamilyMissing_nonneg {n : ℕ} (S : Finset (Fin n))
    (bits : Fin n → Bool) : 0 ≤ jointFamilyMissing S bits := by
  exact Finset.sum_nonneg fun i _ ↦ sub_nonneg.mpr (boolToReal_le_one (bits i))

noncomputable def jointFamilyFaceBase {n : ℕ} (S : Finset (Fin n)) (t : ℝ) : ℝ :=
  1 + t * S.card + t⁻¹ * n

noncomputable def jointFamilyFaceSlope {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    (i : Fin n) : ℝ := -(t * (if i ∈ S then 1 else 0) + t⁻¹)

theorem jointFamilyFace_denominator {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    (bits : Fin n → Bool) :
    affineValue (jointFamilyFaceBase S t) (jointFamilyFaceSlope S t) bits =
      1 + t * jointFamilyMissing S bits + t⁻¹ * jointFamilyMissing Finset.univ bits := by
  classical
  have hsum : (∑ i : Fin n, (if i ∈ S then (1 : ℝ) else 0) * boolToReal (bits i)) =
      ∑ i ∈ S, boolToReal (bits i) := by
    simp only [ite_mul, one_mul, zero_mul]
    simp
  simp only [affineValue, jointFamilyFaceBase, jointFamilyFaceSlope,
    jointFamilyMissing, neg_mul, add_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hsum]
  ring

theorem jointFamilyFace_positive {n : ℕ} (S : Finset (Fin n)) {t : ℝ}
    (ht : 0 < t) (bits : Fin n → Bool) :
    0 < affineValue (jointFamilyFaceBase S t) (jointFamilyFaceSlope S t) bits := by
  rw [jointFamilyFace_denominator]
  have h₁ := mul_nonneg ht.le (jointFamilyMissing_nonneg S bits)
  have h₂ := mul_nonneg (inv_pos.mpr ht).le (jointFamilyMissing_nonneg Finset.univ bits)
  linarith

theorem jointFamilyFace_negative {n : ℕ} (S : Finset (Fin n)) {t : ℝ}
    (ht : 0 < t) (i : Fin n) : jointFamilyFaceSlope S t i < 0 := by
  unfold jointFamilyFaceSlope
  have hi : 0 ≤ (if i ∈ S then (1 : ℝ) else 0) := by split <;> norm_num
  exact neg_neg_of_pos (add_pos_of_nonneg_of_pos (mul_nonneg ht.le hi) (inv_pos.mpr ht))

/-- A face denominator converges to its monomial selector after inversion. -/
theorem jointFamilyFace_limit {n : ℕ} (S : Finset (Fin n))
    (bits : Fin n → Bool) (c : ℝ) :
    Tendsto (fun t : ℝ ↦ c /
      affineValue (jointFamilyFaceBase S t) (jointFamilyFaceSlope S t) bits)
      atTop (nhds (c * squarefreeMonomial S bits)) := by
  classical
  simp_rw [jointFamilyFace_denominator]
  have hsmall : Tendsto (fun t : ℝ ↦ t⁻¹ * jointFamilyMissing Finset.univ bits)
      atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const (jointFamilyMissing Finset.univ bits)
  by_cases hall : ∀ i ∈ S, bits i = true
  · have hmissing : jointFamilyMissing S bits = 0 := by
      unfold jointFamilyMissing
      exact Finset.sum_eq_zero fun i hi ↦ by simp [hall i hi, boolToReal]
    have hmono : squarefreeMonomial S bits = 1 := by
      unfold squarefreeMonomial
      exact Finset.prod_eq_one fun i hi ↦ by simp [hall i hi, boolToReal]
    rw [hmissing, hmono, mul_one]
    have hden : Tendsto (fun t : ℝ ↦ 1 + t⁻¹ * jointFamilyMissing Finset.univ bits)
        atTop (nhds 1) := by simpa using tendsto_const_nhds.add hsmall
    have hquot := (tendsto_const_nhds (x := c)).div hden (by norm_num : (1 : ℝ) ≠ 0)
    convert hquot using 1 <;> simp
    rfl
  · push Not at hall
    obtain ⟨i, hi, hifalse⟩ := hall
    have hbit : bits i = false := by
      cases hb : bits i
      · rfl
      · exact (hifalse hb).elim
    have hmono : squarefreeMonomial S bits = 0 := by
      unfold squarefreeMonomial
      exact Finset.prod_eq_zero hi (by simp [hbit, boolToReal])
    have hmissing : 0 < jointFamilyMissing S bits := by
      have hterm : (1 : ℝ) ≤ jointFamilyMissing S bits := by
        simpa [jointFamilyMissing, hbit, boolToReal] using
          (Finset.single_le_sum
            (fun j (_ : j ∈ S) ↦ sub_nonneg.mpr (boolToReal_le_one (bits j))) hi)
      linarith
    rw [hmono, mul_zero]
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_const_nhds.add_atTop (tendsto_id.atTop_mul_const hmissing)).atTop_add hsmall

/-- One reverse head for each selected monomial, with all independent column
coefficients stored together in its affine numerator. -/
noncomputable def jointFamilyMonomialData {k s H : ℕ}
    (S : Fin H → Finset (Fin (k + s))) (c : Fin H → Fin s → ℝ)
    (t : ℝ) (ht : 0 < t) : ReverseCubeStarData k s H where
  a₀ := fun _ ↦ 0
  b₀ := fun h ↦ jointFamilyFaceBase (S h) t
  a := fun h ↦ Fin.addCases (fun _ ↦ 0) (c h)
  b := fun h ↦ jointFamilyFaceSlope (S h) t
  positive := fun h bits ↦ jointFamilyFace_positive (S h) ht bits
  negative := fun h i ↦ jointFamilyFace_negative (S h) ht i
  zero_column := by
    intro x
    apply Finset.sum_eq_zero
    intro h _
    have hn : affineValue 0 (Fin.addCases (fun _ : Fin k ↦ 0) (c h))
        (Fin.addCases x (fun _ : Fin s ↦ false)) = 0 := by
      simp [affineValue, Fin.sum_univ_add, boolToReal]
    rw [hn, zero_div]

theorem jointFamilyMonomialData_score {k s H : ℕ}
    (S : Fin H → Finset (Fin (k + s))) (c : Fin H → Fin s → ℝ)
    (t : ℝ) (ht : 0 < t) (x : Fin k → Bool) (j : Fin s) :
    (jointFamilyMonomialData S c t ht).score (cubeStarInput x j) =
      ∑ h, c h j / affineValue (jointFamilyFaceBase (S h) t)
        (jointFamilyFaceSlope (S h) t) (cubeStarInput x j) := by
  unfold ReverseCubeStarData.score jointFamilyMonomialData
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  simp [affineValue, cubeStarInput, Fin.sum_univ_add, boolToReal]

/-- Adding any fixed strict-sign residual is stable under the simultaneous
one-head-per-feature approximation. The same positive parameter works for
all rows and independently labelled columns. -/
theorem jointFamily_monomial_correction_preserves_signs {k s H : ℕ}
    (S : Fin H → Finset (Fin (k + s))) (c : Fin H → Fin s → ℝ)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + ∑ h, c h j * squarefreeMonomial (S h) (cubeStarInput x j))) :
    ∃ L : ReverseCubeStarData k s H, ∀ x j,
      0 < outputSign (table x j) * (G x j + L.score (cubeStarInput x j)) := by
  classical
  have hev : ∀ᶠ t : ℝ in atTop, ∀ x j,
      0 < outputSign (table x j) * (G x j + ∑ h, c h j /
        affineValue (jointFamilyFaceBase (S h) t) (jointFamilyFaceSlope (S h) t)
          (cubeStarInput x j)) := by
    apply Filter.eventually_all.mpr
    intro x
    apply Filter.eventually_all.mpr
    intro j
    have hlim := (tendsto_finsetSum Finset.univ fun h _ ↦
      jointFamilyFace_limit (S h) (cubeStarInput x j) (c h j))
    exact ((tendsto_const_nhds.add hlim).const_mul (outputSign (table x j))).eventually
      (eventually_gt_nhds (hstrict x j))
  obtain ⟨t, ht, hsign⟩ := ((eventually_gt_atTop (0 : ℝ)).and hev).exists
  refine ⟨jointFamilyMonomialData S c t ht, fun x j ↦ ?_⟩
  rw [jointFamilyMonomialData_score]
  exact hsign x j

/-- The correction family may be shared over row coordinates alone. Every
column still has its own completely unrestricted real coefficient vector. -/
theorem jointFamily_row_monomial_correction_preserves_signs {k s H : ℕ}
    (S : Fin H → Finset (Fin k)) (c : Fin H → Fin s → ℝ)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + ∑ h, c h j * squarefreeMonomial (S h) x)) :
    ∃ L : ReverseCubeStarData k s H, ∀ x j,
      0 < outputSign (table x j) * (G x j + L.score (cubeStarInput x j)) := by
  classical
  let T : Fin H → Finset (Fin (k + s)) := fun h ↦ (S h).image (Fin.castAdd s)
  apply jointFamily_monomial_correction_preserves_signs T c G table
  intro x j
  convert hstrict x j using 1
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  unfold squarefreeMonomial T
  rw [Finset.prod_image]
  · simp [cubeStarInput]
  · intro i _ l _ hil
    exact Fin.castAdd_inj.mp hil

end HeadComplexity.AxisZeroGluing
