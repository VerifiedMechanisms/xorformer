import HeadComplexity.Results.JointFamilyRidgeCorrections
import HeadComplexity.Results.ReverseMomentGerms

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open Filter
open scoped BigOperators

noncomputable def jointFamilyJetWeight {R : ℕ} (r : ℕ) (h : Fin (R + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (fun i : Fin (R + 1) ↦ (i.val : ℝ)) h).coeff r

theorem jointFamilyJetWeight_extract {R : ℕ} (r : ℕ)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ R) :
    (∑ h : Fin (R + 1), jointFamilyJetWeight r h * P.eval (h.val : ℝ)) = P.coeff r := by
  have hv : Function.Injective (fun i : Fin (R + 1) ↦ (i.val : ℝ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℝ) = j.val at h
    exact_mod_cast h
  have hdeg : P.degree < (Finset.univ : Finset (Fin (R + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hP)
      (by exact_mod_cast Nat.lt_succ_self R)
  have he := congrArg (fun Q : Polynomial ℝ ↦ Q.coeff r)
    (Lagrange.eq_interpolate hv.injOn hdeg)
  simpa [jointFamilyJetWeight, Lagrange.interpolate_apply,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, mul_comm] using he.symm

private theorem linear_natDegree_le (U V : ℝ) :
    (Polynomial.C U + Polynomial.C V * Polynomial.X).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le (by simp)
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem jointFamilyJetWeight_moment {R : ℕ} (r l : ℕ)
    (hl : l ≤ R) (U V : ℝ) :
    (∑ h : Fin (R + 1), jointFamilyJetWeight r h * (U + h.val * V) ^ l) =
      ((Polynomial.C U + Polynomial.C V * Polynomial.X) ^ l).coeff r := by
  have hdeg : ((Polynomial.C U + Polynomial.C V * Polynomial.X) ^ l).natDegree ≤ R := by
    exact (Polynomial.natDegree_pow_le_of_le l (linear_natDegree_le U V)).trans
      (by simpa using hl)
  simpa only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_comm] using jointFamilyJetWeight_extract r
    ((Polynomial.C U + Polynomial.C V * Polynomial.X) ^ l) hdeg

theorem jointFamilyJetWeight_lower_moment {R : ℕ} {r l : ℕ}
    (hr : r ≤ R) (hl : l < r) (U V : ℝ) :
    (∑ h : Fin (R + 1), jointFamilyJetWeight r h * (U + h.val * V) ^ l) = 0 := by
  rw [jointFamilyJetWeight_moment r l (hl.le.trans hr) U V]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact (Polynomial.natDegree_pow_le_of_le l (linear_natDegree_le U V)).trans_lt
    (by simpa using hl)

theorem jointFamilyJetWeight_top_moment {R : ℕ} {r : ℕ}
    (hr : r ≤ R) (U V : ℝ) :
    (∑ h : Fin (R + 1), jointFamilyJetWeight r h * (U + h.val * V) ^ r) = V ^ r := by
  rw [jointFamilyJetWeight_moment r r hr U V]
  have h := Polynomial.coeff_pow_of_natDegree_le
    (m := r) (linear_natDegree_le U V)
  simpa using h

/-- Signed row statistics are recovered by divergent residues, while the
actual row directions can all remain strictly positive. -/
theorem jointFamily_signed_jet_limit {R : ℕ} {r : ℕ} (hr : r ≤ R) (U V : ℝ) :
    Tendsto (fun T : ℝ ↦ T ^ (r + 1) *
      ∑ h : Fin (R + 1), jointFamilyJetWeight r h / (T - (U + h.val * V)))
      atTop (nhds (V ^ r)) := by
  let p : Fin (R + 1) → ℝ := fun h ↦ U + h.val * V
  have hlim : Tendsto (fun T : ℝ ↦ ∑ h : Fin (R + 1),
      jointFamilyJetWeight r h * p h ^ r * (T / (T - p h)))
      atTop (nhds (V ^ r)) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin (R + 1)))
      (fun h _ ↦ (jointFamilyRidgePole_ratio_limit (H := 1) (0 : Fin 1) (p h)).const_mul
        (jointFamilyJetWeight r h * p h ^ r))
    simpa [jointFamilyRidgePole, p, jointFamilyJetWeight_top_moment hr U V] using h
  apply hlim.congr'
  have hev : ∀ᶠ T : ℝ in atTop, T ≠ 0 ∧ ∀ h, T - p h ≠ 0 := by
    apply (eventually_gt_atTop (0 : ℝ)).and ?_ |>.mono
    · intro T h
      exact ⟨ne_of_gt h.1, h.2⟩
    · apply Filter.eventually_all.mpr
      intro h
      exact (eventually_gt_atTop (p h)).mono (fun T hT ↦ ne_of_gt (sub_pos.mpr hT))
  filter_upwards [hev] with T hT
  have he := cauchy_moment_remainder (jointFamilyJetWeight r) p r T 1 hT.1
    (by simpa using hT.2) (fun l hl ↦ jointFamilyJetWeight_lower_moment hr hl U V)
  simp only [one_mul] at he
  rw [he, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [pow_succ]
  simp only [one_div, inv_pow]
  field_simp [hT.1, hT.2 h]


noncomputable def jointFamilySignedJetBase {k : ℕ} (R : ℕ) (v : Fin k → ℝ)
    (i : Fin k) : ℝ := R * |v i| + 1

noncomputable def jointFamilySignedJetSlope {k R : ℕ} (v : Fin k → ℝ)
    (h : Fin (R + 1)) (i : Fin k) : ℝ := jointFamilySignedJetBase R v i + h.val * v i

private theorem signedJetSlope_bounds {k R : ℕ} (v : Fin k → ℝ)
    (h : Fin (R + 1)) (i : Fin k) :
    0 < jointFamilySignedJetSlope v h i ∧
      jointFamilySignedJetSlope v h i ≤ 2 * R * |v i| + 1 := by
  have hh : (h.val : ℝ) ≤ R := by exact_mod_cast Nat.le_of_lt_succ h.isLt
  have hn : (0 : ℝ) ≤ h.val := Nat.cast_nonneg _
  have ha := abs_nonneg (v i)
  have hlow := mul_le_mul_of_nonneg_left (neg_abs_le (v i)) hn
  have hupp := mul_le_mul_of_nonneg_left (le_abs_self (v i)) hn
  have hm := mul_le_mul_of_nonneg_right hh ha
  dsimp [jointFamilySignedJetSlope, jointFamilySignedJetBase]
  constructor <;> nlinarith

noncomputable def jointFamilySignedJetData {k s R : ℕ}
    (v : Fin k → ℝ) (c : Fin (R + 1) → Fin s → ℝ)
    (T : ℝ) (hT : (∑ i, (2 * R * |v i| + 1)) + (s : ℝ) < T) :
    ReverseCubeStarData k s (R + 1) where
  a₀ := fun _ ↦ 0
  b₀ := fun _ ↦ T + 1
  a := fun h ↦ Fin.addCases (fun _ ↦ 0) (c h)
  b := fun h ↦ Fin.addCases (fun i ↦ -jointFamilySignedJetSlope v h i) (fun _ ↦ -1)
  positive := by
    intro h bits
    have hr : (∑ i : Fin k, jointFamilySignedJetSlope v h i *
        boolToReal (bits (Fin.castAdd s i))) ≤ ∑ i, (2 * R * |v i| + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (mul_le_of_le_one_right (signedJetSlope_bounds v h i).1.le
        (boolToReal_le_one _)).trans (signedJetSlope_bounds v h i).2
    have hc : (∑ j : Fin s, boolToReal (bits (Fin.natAdd k j))) ≤ (s : ℝ) := by
      calc
        _ ≤ ∑ _j : Fin s, (1 : ℝ) := Finset.sum_le_sum (fun j _ ↦ boolToReal_le_one _)
        _ = _ := by simp
    simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_mul, one_mul, Finset.sum_neg_distrib]
    linarith
  negative := by
    intro h i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using neg_neg_of_pos (signedJetSlope_bounds v h j).1
    · intro j
      simp only [Fin.addCases_right]
      norm_num
  zero_column := by
    intro x
    apply Finset.sum_eq_zero
    intro h _
    have hn : affineValue 0 (Fin.addCases (fun _ : Fin k ↦ 0) (c h))
        (Fin.addCases x (fun _ : Fin s ↦ false)) = 0 := by
      simp [affineValue, Fin.sum_univ_add, boolToReal]
    rw [hn, zero_div]

theorem jointFamilySignedJetData_score {k s R : ℕ}
    (v : Fin k → ℝ) (c : Fin (R + 1) → Fin s → ℝ)
    (T : ℝ) (hT : (∑ i, (2 * R * |v i| + 1)) + (s : ℝ) < T)
    (x : Fin k → Bool) (j : Fin s) :
    (jointFamilySignedJetData v c T hT).score (cubeStarInput x j) =
      ∑ h, c h j / (T - (jointFamilyRidgeValue (jointFamilySignedJetBase R v) x +
        h.val * jointFamilyRidgeValue v x)) := by
  unfold ReverseCubeStarData.score jointFamilySignedJetData
  apply Finset.sum_congr rfl
  intro h _
  have hn : affineValue 0 (Fin.addCases (fun _ : Fin k ↦ 0) (c h))
      (cubeStarInput x j) = c h j := by
    simp [affineValue, cubeStarInput, Fin.sum_univ_add, boolToReal]
  rw [hn]
  congr 1
  simp only [affineValue, cubeStarInput, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, neg_mul,
    Finset.sum_neg_distrib]
  have he : (∑ i : Fin k, if x i = true then
      jointFamilySignedJetBase R v i + h.val * v i else 0) =
      (∑ i : Fin k, if x i = true then jointFamilySignedJetBase R v i else 0) +
        h.val * ∑ i : Fin k, if x i = true then v i else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> ring
  simp [boolToReal, jointFamilySignedJetSlope, jointFamilyRidgeValue, he]
  ring

noncomputable def jointFamilySignedJetResidue {s R : ℕ}
    (P : Fin s → Polynomial ℝ) (T : ℝ) (h : Fin (R + 1)) (j : Fin s) : ℝ :=
  ∑ r : Fin (R + 1), (P j).coeff r.val * T ^ (r.val + 1) * jointFamilyJetWeight r.val h

theorem jointFamily_signed_polynomial_limit {s R : ℕ}
    (P : Fin s → Polynomial ℝ) (hP : ∀ j, (P j).natDegree ≤ R)
    (U V : ℝ) (j : Fin s) :
    Tendsto (fun T : ℝ ↦ ∑ h : Fin (R + 1), jointFamilySignedJetResidue P T h j /
      (T - (U + h.val * V))) atTop (nhds ((P j).eval V)) := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin (R + 1)))
    (fun r _ ↦ (jointFamily_signed_jet_limit
      (Nat.le_of_lt_succ r.isLt) U V).const_mul ((P j).coeff r.val))
  have heval : (∑ r : Fin (R + 1), (P j).coeff r.val * V ^ r.val) = (P j).eval V := by
    rw [Fin.sum_univ_eq_sum_range (fun r ↦ (P j).coeff r * V ^ r)]
    exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP j)) (x := V)).symm
  rw [heval] at hlim
  apply hlim.congr
  intro T
  simp only [jointFamilySignedJetResidue, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- A degree-R polynomial in an arbitrary signed affine row statistic costs
R+1 heads in the strict-sign closure. All column polynomials are independent.
Actual slopes have the required reverse sign on every coordinate. -/
theorem jointFamily_signed_polynomial_correction_preserves_signs {k s R : ℕ}
    (v : Fin k → ℝ) (P : Fin s → Polynomial ℝ)
    (hP : ∀ j, (P j).natDegree ≤ R)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + (P j).eval (jointFamilyRidgeValue v x))) :
    ∃ L : ReverseCubeStarData k s (R + 1), ∀ x j,
      0 < outputSign (table x j) * (G x j + L.score (cubeStarInput x j)) := by
  have hev : ∀ᶠ T : ℝ in atTop, ∀ x j,
      0 < outputSign (table x j) * (G x j +
        ∑ h : Fin (R + 1), jointFamilySignedJetResidue P T h j /
          (T - (jointFamilyRidgeValue (jointFamilySignedJetBase R v) x +
            h.val * jointFamilyRidgeValue v x))) := by
    apply Filter.eventually_all.mpr
    intro x
    apply Filter.eventually_all.mpr
    intro j
    have hlim := jointFamily_signed_polynomial_limit P hP
      (jointFamilyRidgeValue (jointFamilySignedJetBase R v) x)
      (jointFamilyRidgeValue v x) j
    exact ((tendsto_const_nhds.add hlim).const_mul (outputSign (table x j))).eventually
      (eventually_gt_nhds (hstrict x j))
  obtain ⟨T, hT, hsign⟩ := ((eventually_gt_atTop
    ((∑ i, (2 * R * |v i| + 1)) + (s : ℝ))).and hev).exists
  refine ⟨jointFamilySignedJetData v (jointFamilySignedJetResidue P T) T hT, ?_⟩
  intro x j
  rw [jointFamilySignedJetData_score]
  exact hsign x j

end HeadComplexity.AxisZeroGluing
