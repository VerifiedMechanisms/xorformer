import HeadComplexity.Results.JointFamilyPermutationData
import HeadComplexity.Results.JointFamilyMonomialCorrections

set_option linter.style.header false

/-! Face gating of independently programmed column memories. Main and reference
banks cost `H+H` heads. The zero-column axis is exact, and full-cube positivity
and strict negative slopes hold before taking limits. This is a local
construction, not a cover or an unconditional decoder theorem. -/
namespace HeadComplexity.AxisZeroGluing
open Filter
open scoped BigOperators

noncomputable def jointFamilyGatedBase {n : ℕ} (b₀ : ℝ)
    (S : Finset (Fin n)) (t : ℝ) : ℝ := b₀ + jointFamilyFaceBase S t - 1
noncomputable def jointFamilyGatedSlope {n : ℕ} (b : Fin n → ℝ)
    (S : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  b i + jointFamilyFaceSlope S t i

theorem jointFamilyGated_denominator {n : ℕ} (b₀ : ℝ) (b : Fin n → ℝ)
    (S : Finset (Fin n)) (t : ℝ) (bits : Fin n → Bool) :
    affineValue (jointFamilyGatedBase b₀ S t) (jointFamilyGatedSlope b S t) bits =
      affineValue b₀ b bits + t * jointFamilyMissing S bits +
        t⁻¹ * jointFamilyMissing Finset.univ bits := by
  have he := jointFamilyFace_denominator S t bits
  simp only [affineValue, jointFamilyGatedBase, jointFamilyGatedSlope,
    add_mul, Finset.sum_add_distrib] at ⊢
  simp only [affineValue] at he
  linarith

theorem jointFamilyGated_positive {n : ℕ} (b₀ : ℝ) (b : Fin n → ℝ)
    (S : Finset (Fin n)) {t : ℝ} (ht : 0 < t) (bits : Fin n → Bool)
    (hbase : 0 < affineValue b₀ b bits) :
    0 < affineValue (jointFamilyGatedBase b₀ S t) (jointFamilyGatedSlope b S t) bits := by
  rw [jointFamilyGated_denominator]
  have h₁ := mul_nonneg ht.le (jointFamilyMissing_nonneg S bits)
  have h₂ := mul_nonneg (inv_pos.mpr ht).le (jointFamilyMissing_nonneg Finset.univ bits)
  linarith

theorem jointFamilyGated_negative {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≤ 0) (S : Finset (Fin n)) {t : ℝ} (ht : 0 < t)
    (i : Fin n) : jointFamilyGatedSlope b S t i < 0 := by
  exact add_neg_of_nonpos_of_neg (hb i) (jointFamilyFace_negative S ht i)

/-- A gated fraction tends to its original value on the selected face and
zero elsewhere; strict reverse slopes hold at every positive parameter. -/
theorem jointFamilyGated_fraction_limit {n : ℕ} (b₀ : ℝ) (b : Fin n → ℝ)
    (S : Finset (Fin n)) (bits : Fin n → Bool) (c : ℝ)
    (hbase : 0 < affineValue b₀ b bits) :
    Tendsto (fun t : ℝ ↦ c /
      affineValue (jointFamilyGatedBase b₀ S t) (jointFamilyGatedSlope b S t) bits)
      atTop (nhds (c / affineValue b₀ b bits * squarefreeMonomial S bits)) := by
  classical
  simp_rw [jointFamilyGated_denominator]
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
    have hden : Tendsto (fun t : ℝ ↦ affineValue b₀ b bits +
        t⁻¹ * jointFamilyMissing Finset.univ bits)
        atTop (nhds (affineValue b₀ b bits)) := by
      simpa using tendsto_const_nhds.add hsmall
    convert (tendsto_const_nhds (x := c)).div hden hbase.ne' using 1 <;> simp
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
    exact (tendsto_const_nhds.add_atTop
      (tendsto_id.atTop_mul_const hmissing)).atTop_add hsmall

/-- Main and reference fractions share their row numerator and denominator.
All column memories are unrestricted apart from explicit positivity and weak
reverse slope conditions. -/
structure JointFamilyDifferenceBank (k s H : ℕ) where
  a₀ : Fin H → ℝ
  a : Fin H → Fin k → ℝ
  c : Fin H → Fin s → ℝ
  b₀ : Fin H → ℝ
  b : Fin H → Fin k → ℝ
  d : Fin H → Fin s → ℝ
  e : Fin H → Fin s → ℝ
  row_nonpos : ∀ h i, b h i ≤ 0
  main_nonpos : ∀ h j, d h j ≤ 0
  ref_nonpos : ∀ h j, e h j ≤ 0
  main_positive : ∀ h bits,
    0 < affineValue (b₀ h) (Fin.addCases (b h) (d h)) bits
  ref_positive : ∀ h bits,
    0 < affineValue (b₀ h) (Fin.addCases (b h) (e h)) bits

noncomputable def JointFamilyDifferenceBank.mainNumerator {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H) (h : Fin H) : Fin (k + s) → ℝ :=
  Fin.addCases (B.a h) (B.c h)
noncomputable def JointFamilyDifferenceBank.refNumerator {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H) (h : Fin H) : Fin (k + s) → ℝ :=
  Fin.addCases (B.a h) (fun _ ↦ 0)

noncomputable def JointFamilyDifferenceBank.gatedData {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H)
    (S : Fin H → Finset (Fin (k + s))) (t : ℝ) (ht : 0 < t) :
    ReverseCubeStarData k s (H + H) where
  a₀ := Fin.addCases B.a₀ (fun h ↦ -B.a₀ h)
  a := Fin.addCases B.mainNumerator (fun h i ↦ -B.refNumerator h i)
  b₀ := Fin.addCases (fun h ↦ jointFamilyGatedBase (B.b₀ h) (S h) t)
    (fun h ↦ jointFamilyGatedBase (B.b₀ h) (S h) t)
  b := Fin.addCases
    (fun h ↦ jointFamilyGatedSlope (Fin.addCases (B.b h) (B.d h)) (S h) t)
    (fun h ↦ jointFamilyGatedSlope (Fin.addCases (B.b h) (B.e h)) (S h) t)
  positive := by
    intro h bits
    refine Fin.addCases ?_ ?_ h
    · intro l
      simpa only [Fin.addCases_left] using
        jointFamilyGated_positive _ _ (S l) ht bits (B.main_positive l bits)
    · intro l
      simpa only [Fin.addCases_right] using
        jointFamilyGated_positive _ _ (S l) ht bits (B.ref_positive l bits)
  negative := by
    intro h i
    refine Fin.addCases ?_ ?_ h
    · intro l
      simp only [Fin.addCases_left, Fin.addCases_right]
      apply jointFamilyGated_negative _ ?_ (S l) ht i
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simpa only [Fin.addCases_left] using B.row_nonpos l i
      · intro j
        simpa only [Fin.addCases_right] using B.main_nonpos l j
    · intro l
      simp only [Fin.addCases_left, Fin.addCases_right]
      apply jointFamilyGated_negative _ ?_ (S l) ht i
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simpa only [Fin.addCases_left] using B.row_nonpos l i
      · intro j
        simpa only [Fin.addCases_right] using B.ref_nonpos l j
  zero_column := by
    intro x
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro h _
    have hnum : affineValue (-B.a₀ h) (fun i ↦ -B.refNumerator h i)
        (Fin.addCases x (fun _ : Fin s ↦ false)) =
        -affineValue (B.a₀ h) (B.mainNumerator h)
          (Fin.addCases x (fun _ : Fin s ↦ false)) := by
      have hn : affineValue (B.a₀ h) (B.refNumerator h)
          (Fin.addCases x (fun _ : Fin s ↦ false)) =
          affineValue (B.a₀ h) (B.mainNumerator h)
            (Fin.addCases x (fun _ : Fin s ↦ false)) := by
        simp [affineValue, JointFamilyDifferenceBank.mainNumerator,
          JointFamilyDifferenceBank.refNumerator, Fin.sum_univ_add, boolToReal]
      rw [← hn]
      simp [affineValue, neg_mul, Finset.sum_neg_distrib, add_comm]
    have hden : affineValue (jointFamilyGatedBase (B.b₀ h) (S h) t)
        (jointFamilyGatedSlope (Fin.addCases (B.b h) (B.e h)) (S h) t)
        (Fin.addCases x (fun _ : Fin s ↦ false)) =
        affineValue (jointFamilyGatedBase (B.b₀ h) (S h) t)
        (jointFamilyGatedSlope (Fin.addCases (B.b h) (B.d h)) (S h) t)
        (Fin.addCases x (fun _ : Fin s ↦ false)) := by
      simp [affineValue, jointFamilyGatedSlope, Fin.sum_univ_add, boolToReal]
    rw [hnum, hden, neg_div, add_neg_cancel]

noncomputable def JointFamilyDifferenceBank.gatedScore {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H)
    (S : Fin H → Finset (Fin (k + s))) (t : ℝ) (bits : Fin (k + s) → Bool) : ℝ :=
  ∑ h, (affineValue (B.a₀ h) (B.mainNumerator h) bits /
      affineValue (jointFamilyGatedBase (B.b₀ h) (S h) t)
        (jointFamilyGatedSlope (Fin.addCases (B.b h) (B.d h)) (S h) t) bits -
    affineValue (B.a₀ h) (B.refNumerator h) bits /
      affineValue (jointFamilyGatedBase (B.b₀ h) (S h) t)
        (jointFamilyGatedSlope (Fin.addCases (B.b h) (B.e h)) (S h) t) bits)

theorem JointFamilyDifferenceBank.gatedData_score {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H)
    (S : Fin H → Finset (Fin (k + s))) (t : ℝ) (ht : 0 < t)
    (bits : Fin (k + s) → Bool) :
    (B.gatedData S t ht).score bits = B.gatedScore S t bits := by
  simp only [ReverseCubeStarData.score, JointFamilyDifferenceBank.gatedData,
    Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    JointFamilyDifferenceBank.gatedScore]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  have hn : affineValue (-B.a₀ h) (fun i ↦ -B.refNumerator h i) bits =
      -affineValue (B.a₀ h) (B.refNumerator h) bits := by
    simp [affineValue, neg_mul, Finset.sum_neg_distrib, add_comm]
  rw [hn, neg_div, sub_eq_add_neg]

noncomputable def JointFamilyDifferenceBank.selectedScore {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H)
    (S : Fin H → Finset (Fin (k + s))) (bits : Fin (k + s) → Bool) : ℝ :=
  ∑ h, (affineValue (B.a₀ h) (B.mainNumerator h) bits /
        affineValue (B.b₀ h) (Fin.addCases (B.b h) (B.d h)) bits -
      affineValue (B.a₀ h) (B.refNumerator h) bits /
        affineValue (B.b₀ h) (Fin.addCases (B.b h) (B.e h)) bits) *
    squarefreeMonomial (S h) bits

theorem JointFamilyDifferenceBank.gatedScore_tendsto {k s H : ℕ}
    (B : JointFamilyDifferenceBank k s H)
    (S : Fin H → Finset (Fin (k + s))) (bits : Fin (k + s) → Bool) :
    Tendsto (fun t : ℝ ↦ B.gatedScore S t bits)
      atTop (nhds (B.selectedScore S bits)) := by
  unfold JointFamilyDifferenceBank.gatedScore JointFamilyDifferenceBank.selectedScore
  apply tendsto_finsetSum
  intro h _
  have hm := jointFamilyGated_fraction_limit (B.b₀ h)
    (Fin.addCases (B.b h) (B.d h)) (S h) bits
    (affineValue (B.a₀ h) (B.mainNumerator h) bits) (B.main_positive h bits)
  have hr := jointFamilyGated_fraction_limit (B.b₀ h)
    (Fin.addCases (B.b h) (B.e h)) (S h) bits
    (affineValue (B.a₀ h) (B.refNumerator h) bits) (B.ref_positive h bits)
  simpa only [sub_mul] using hm.sub hr

/-- One gate scale preserves every strict sign in a finite query family and
all independently programmed columns. An arbitrary prior score and `K`
monomial corrections are included at a total cost of `H+H+K` heads. -/
theorem jointFamily_gated_difference_with_correction_preserves_signs
    {Q : Type*} [Fintype Q] {k s H K : ℕ}
    (query : Q → Fin k → Bool) (B : JointFamilyDifferenceBank k s H)
    (S : Fin H → Finset (Fin (k + s)))
    (T : Fin K → Finset (Fin (k + s))) (c : Fin K → Fin s → ℝ)
    (G : Q → Fin s → ℝ) (table : Q → Fin s → Bool)
    (hstrict : ∀ q j, 0 < outputSign (table q j) *
      (G q j + B.selectedScore S (cubeStarInput (query q) j) +
        ∑ h, c h j * squarefreeMonomial (T h) (cubeStarInput (query q) j))) :
    ∃ L : ReverseCubeStarData k s (H + H + K), ∀ q j,
      0 < outputSign (table q j) * (G q j + L.score (cubeStarInput (query q) j)) := by
  classical
  have hev : ∀ᶠ t : ℝ in atTop, ∀ q j,
      0 < outputSign (table q j) *
        (G q j + B.gatedScore S t (cubeStarInput (query q) j) +
          ∑ h, c h j / affineValue (jointFamilyFaceBase (T h) t)
            (jointFamilyFaceSlope (T h) t) (cubeStarInput (query q) j)) := by
    apply Filter.eventually_all.mpr
    intro q
    apply Filter.eventually_all.mpr
    intro j
    have hm := tendsto_finsetSum Finset.univ fun h _ ↦
      jointFamilyFace_limit (T h) (cubeStarInput (query q) j) (c h j)
    have hl := ((tendsto_const_nhds (x := G q j)).add
      (B.gatedScore_tendsto S (cubeStarInput (query q) j))).add hm
    exact (hl.const_mul (outputSign (table q j))).eventually
      (eventually_gt_nhds (hstrict q j))
  obtain ⟨t, ht, hsign⟩ := ((eventually_gt_atTop (0 : ℝ)).and hev).exists
  refine ⟨jointFamilyAppendData (B.gatedData S t ht) (jointFamilyMonomialData T c t ht),
    fun q j ↦ ?_⟩
  rw [jointFamilyAppendData_score, B.gatedData_score, jointFamilyMonomialData_score]
  simpa only [add_assoc] using hsign q j

end HeadComplexity.AxisZeroGluing
