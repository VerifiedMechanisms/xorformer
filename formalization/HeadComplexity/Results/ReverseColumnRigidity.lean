import HeadComplexity.Results.ReverseAxisCompiler

set_option linter.style.header false

/-!
# A whole-cube obstruction to reverse Cauchy column tables

Three singleton values of a positive affine denominator with nonpositive
slopes constrain its value at the union of two singleton vertices. This
rules out two large pole departures from a common minimum pole. The result
concerns denominator admissibility, not a lower bound for unrestricted
head complexity.
-/

namespace HeadComplexity

open scoped BigOperators

/-- The Boolean vertex supported on two prescribed coordinates. -/
def reverseColumnTwoHot {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun i ↦ decide (i = a ∨ i = b)

@[simp] theorem affineValue_reverseAxisOneHot {n : ℕ}
    (c : ℝ) (cs : Fin n → ℝ) (a : Fin n) :
    affineValue c cs (reverseAxisOneHot a) = c + cs a := by
  simp [affineValue, reverseAxisOneHot, boolToReal]

theorem affineValue_reverseColumnTwoHot {n : ℕ}
    (c : ℝ) (cs : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    affineValue c cs (reverseColumnTwoHot a b) = c + cs a + cs b := by
  have hbit (i : Fin n) :
      boolToReal (reverseColumnTwoHot a b i) =
        boolToReal (reverseAxisOneHot a i) + boolToReal (reverseAxisOneHot b i) := by
    by_cases hia : i = a
    · subst i
      simp [reverseColumnTwoHot, reverseAxisOneHot, boolToReal, hab]
    · by_cases hib : i = b
      · subst i
        simp [reverseColumnTwoHot, reverseAxisOneHot, boolToReal, hia]
      · simp [reverseColumnTwoHot, reverseAxisOneHot, boolToReal, hia, hib]
  simp_rw [affineValue, hbit, mul_add, Finset.sum_add_distrib]
  simp [reverseAxisOneHot, boolToReal]
  ring

/-- A reverse affine denominator cannot have two singleton pole departures
whose total exceeds the positivity margin available at a third singleton. -/
theorem reverseAffine_two_outliers_lt {n : ℕ}
    (c D u₀ u₁ u₂ : ℝ) (cs : Fin n → ℝ) (m a b : Fin n)
    (hab : a ≠ b) (hm : cs m ≤ 0)
    (hpos : ∀ bits, 0 < affineValue c cs bits)
    (hzero : affineValue c cs (reverseAxisOneHot m) = D - u₀)
    (hone : affineValue c cs (reverseAxisOneHot a) = D - u₁)
    (htwo : affineValue c cs (reverseAxisOneHot b) = D - u₂) :
    u₁ + u₂ < D + u₀ := by
  have hpair := hpos (reverseColumnTwoHot a b)
  rw [affineValue_reverseColumnTwoHot c cs a b hab] at hpair
  simp only [affineValue_reverseAxisOneHot] at hzero hone htwo
  linarith

/-- An explicit nonpositive pair vertex rules out whole-cube positivity. -/
theorem reverseAffine_not_positive_of_two_outliers {n : ℕ}
    (c D u₀ u₁ u₂ : ℝ) (cs : Fin n → ℝ) (m a b : Fin n)
    (hab : a ≠ b) (hm : cs m ≤ 0)
    (hzero : affineValue c cs (reverseAxisOneHot m) = D - u₀)
    (hone : affineValue c cs (reverseAxisOneHot a) = D - u₁)
    (htwo : affineValue c cs (reverseAxisOneHot b) = D - u₂)
    (hbudget : D + u₀ ≤ u₁ + u₂) :
    ¬ ∀ bits, 0 < affineValue c cs bits := by
  intro hpos
  exact (not_lt_of_ge hbudget)
    (reverseAffine_two_outliers_lt c D u₀ u₁ u₂ cs m a b hab hm hpos hzero hone htwo)

/-- Geometrically separated poles admit at most one upward departure from a
head's smallest column pole in a whole-cube positive reverse denominator. -/
theorem reverseAffine_not_positive_of_geometric_outliers {n : ℕ}
    (c D u₀ u₁ u₂ ε δ L : ℝ) (cs : Fin n → ℝ) (m a b : Fin n)
    (hab : a ≠ b) (hm : cs m ≤ 0)
    (hzero : affineValue c cs (reverseAxisOneHot m) = D - u₀)
    (hone : affineValue c cs (reverseAxisOneHot a) = D - u₁)
    (htwo : affineValue c cs (reverseAxisOneHot b) = D - u₂)
    (hε : 0 < ε) (hL : 4 ≤ L) (hδ : δ ≤ ε / L)
    (hmargin : D - u₀ = δ + ε)
    (hgap₁ : ε * (1 - 1 / L ^ 2) ≤ u₁ - u₀)
    (hgap₂ : ε * (1 - 1 / L ^ 2) ≤ u₂ - u₀) :
    ¬ ∀ bits, 0 < affineValue c cs bits := by
  apply reverseAffine_not_positive_of_two_outliers c D u₀ u₁ u₂ cs m a b
    hab hm hzero hone htwo
  have hLpos : 0 < L := by linarith
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
  have hrecip : 1 / L ≤ (1 / 4 : ℝ) := by
    exact (div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 4)).2 (by linarith)
  have hrecipsq : 1 / L ^ 2 ≤ (1 / 16 : ℝ) := by
    apply (div_le_div_iff₀ hLsq (by norm_num : (0 : ℝ) < 16)).2
    nlinarith
  have hδ' : δ ≤ ε / 4 := by
    calc
      δ ≤ ε / L := hδ
      _ = ε * (1 / L) := by ring
      _ ≤ ε * (1 / 4) := mul_le_mul_of_nonneg_left hrecip hε.le
      _ = ε / 4 := by ring
  have hgap : ε * (15 / 16) ≤ ε * (1 - 1 / L ^ 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  linarith

/-- With at least three permutation columns, requiring every row minimum
to occur in all but at most one column freezes every column permutation. -/
theorem permutations_eq_of_no_two_larger {H S : ℕ} (hS : 2 < S)
    (π : Fin S → Equiv.Perm (Fin H))
    (hmin : ∀ h m a b, a ≠ b →
      ¬ (π m h < π a h ∧ π m h < π b h)) :
    ∀ j k, π j = π k := by
  have hfrozen : ∀ q : ℕ, ∀ h j, (π j h).val = q → ∀ k, π k h = π j h := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      have hfloor : ∀ h j, (π j h).val = q → ∀ t, π j h ≤ π t h := by
        intro h j hj t
        by_contra hnot
        have hlt' : (π t h).val < (π j h).val := lt_of_not_ge hnot
        have hlt : (π t h).val < q := by simpa [hj] using hlt'
        have heq := ih (π t h).val hlt h t rfl j
        have hval := congrArg Fin.val heq
        omega
      intro h j hj k
      by_contra hneq
      have hjk : j ≠ k := by
        intro heq
        subst k
        exact hneq rfl
      obtain ⟨l, hlj, hlk⟩ := Fin.exists_ne_and_ne_of_two_lt j k hS
      have hjklt : π j h < π k h :=
        lt_of_le_of_ne (hfloor h j hj k) (Ne.symm hneq)
      have hl : π l h = π j h := by
        by_contra hne
        exact hmin h j k l hlk.symm
          ⟨hjklt, lt_of_le_of_ne (hfloor h j hj l) (Ne.symm hne)⟩
      let h' : Fin H := (π k).symm (π j h)
      have hk' : π k h' = π j h := (π k).apply_symm_apply _
      have hh' : h' ≠ h := by
        intro heq
        apply hneq
        simpa [heq] using hk'
      have hj'ne : π j h' ≠ π k h' := by
        intro heq
        apply hh'
        apply (π j).injective
        exact heq.trans hk'
      have hk'val : (π k h').val = q := by rw [hk', hj]
      have hj'lt : π k h' < π j h' :=
        lt_of_le_of_ne (hfloor h' k hk'val j) (Ne.symm hj'ne)
      have hl' : π l h' = π k h' := by
        by_contra hne
        exact hmin h' k j l hlj.symm
          ⟨hj'lt, lt_of_le_of_ne (hfloor h' k hk'val l) (Ne.symm hne)⟩
      apply hh'
      apply (π l).injective
      exact hl'.trans (hk'.trans hl.symm)
  intro j k
  apply Equiv.ext
  intro h
  exact (hfrozen (π j h).val h j rfl k).symm

/-- A separated common Cauchy pole library cannot encode different column
permutations in positive reverse affine denominators on three or more columns.
The separation assumption is exactly the margin violated by two larger poles. -/
theorem reverseAffine_permutation_columns_frozen {H S : ℕ} (hS : 2 < S)
    (π : Fin S → Equiv.Perm (Fin H)) (D : ℝ) (poles : Fin H → ℝ)
    (c : Fin H → ℝ) (cs : Fin H → Fin S → ℝ)
    (hsep : ∀ k a b, k < a → k < b → D + poles k ≤ poles a + poles b)
    (hslopes : ∀ h j, cs h j ≤ 0)
    (hpos : ∀ h bits, 0 < affineValue (c h) (cs h) bits)
    (hgrid : ∀ h j, affineValue (c h) (cs h) (reverseAxisOneHot j) =
      D - poles (π j h)) :
    ∀ j k, π j = π k := by
  apply permutations_eq_of_no_two_larger hS π
  intro h m a b hab hout
  exact reverseAffine_not_positive_of_two_outliers
    (c h) D (poles (π m h)) (poles (π a h)) (poles (π b h)) (cs h) m a b hab
    (hslopes h m) (hgrid h m) (hgrid h a) (hgrid h b)
    (hsep _ _ _ hout.1 hout.2) (hpos h)

/-- The same rigidity allows arbitrary positive scaling of each head's
singleton table. Thus rescaling the affine denominator cannot repair it. -/
theorem reverseAffine_scaled_permutation_columns_frozen {H S : ℕ} (hS : 2 < S)
    (π : Fin S → Equiv.Perm (Fin H)) (D : ℝ) (poles : Fin H → ℝ)
    (c scale : Fin H → ℝ) (cs : Fin H → Fin S → ℝ)
    (hscale : ∀ h, 0 < scale h)
    (hsep : ∀ k a b, k < a → k < b → D + poles k ≤ poles a + poles b)
    (hslopes : ∀ h j, cs h j ≤ 0)
    (hpos : ∀ h bits, 0 < affineValue (c h) (cs h) bits)
    (hgrid : ∀ h j, affineValue (c h) (cs h) (reverseAxisOneHot j) =
      scale h * (D - poles (π j h))) :
    ∀ j k, π j = π k := by
  have hnorm (h : Fin H) (bits : Fin S → Bool) :
      affineValue (c h / scale h) (fun j ↦ cs h j / scale h) bits =
        affineValue (c h) (cs h) bits / scale h := by
    simpa only [div_eq_inv_mul] using
      affineValue_smul (scale h)⁻¹ (c h) (cs h) bits
  apply reverseAffine_permutation_columns_frozen hS π D poles
    (fun h ↦ c h / scale h) (fun h j ↦ cs h j / scale h) hsep
  · intro h j
    exact div_nonpos_of_nonpos_of_nonneg (hslopes h j) (hscale h).le
  · intro h bits
    rw [hnorm]
    exact div_pos (hpos h bits) (hscale h)
  · intro h j
    rw [hnorm, hgrid]
    exact mul_div_cancel_left₀ _ (hscale h).ne'

end HeadComplexity
