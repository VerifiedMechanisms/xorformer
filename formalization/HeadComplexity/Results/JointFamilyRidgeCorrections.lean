import HeadComplexity.Results.JointFamilyPermutationData
import HeadComplexity.Results.ExteriorCauchyInterpolation

set_option linter.style.header false

/-!
# Shared polynomial corrections in a positive linear row statistic

A degree-R polynomial, chosen independently in every column, costs R+1
reverse heads. Its numerical values are approximated simultaneously on the
entire row cube. All full-cube denominator and zero-axis conditions hold.
-/

namespace HeadComplexity.AxisZeroGluing

open Filter
open scoped BigOperators

noncomputable def jointFamilyRidgeValue {k : ℕ} (w : Fin k → ℝ)
    (x : Fin k → Bool) : ℝ := ∑ i, w i * boolToReal (x i)

theorem jointFamilyRidgeValue_le {k : ℕ} (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) (x : Fin k → Bool) :
    jointFamilyRidgeValue w x ≤ ∑ i, w i := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_of_le_one_right (hw i).le (boolToReal_le_one _)

noncomputable def jointFamilyRidgeData {k s H : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (c : Fin H → Fin s → ℝ)
    (T : ℝ) (hT : (∑ i, w i) + (s : ℝ) < T) : ReverseCubeStarData k s H where
  a₀ := fun _ ↦ 0
  b₀ := fun h ↦ T + h.val + 1
  a := fun h ↦ Fin.addCases (fun _ ↦ 0) (c h)
  b := fun _ ↦ Fin.addCases (fun i ↦ -w i) (fun _ ↦ -1)
  positive := by
    intro h bits
    have hr := jointFamilyRidgeValue_le w hw (fun i ↦ bits (Fin.castAdd s i))
    have hc : (∑ j : Fin s, boolToReal (bits (Fin.natAdd k j))) ≤ (s : ℝ) := by
      calc
        _ ≤ ∑ _j : Fin s, (1 : ℝ) := Finset.sum_le_sum (fun j _ ↦ boolToReal_le_one _)
        _ = _ := by simp
    simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_mul, one_mul, Finset.sum_neg_distrib]
    unfold jointFamilyRidgeValue at hr
    have hh : (0 : ℝ) ≤ h.val := Nat.cast_nonneg _
    linarith
  negative := by
    intro h i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using neg_neg_of_pos (hw j)
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

theorem jointFamilyRidgeData_score {k s H : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (c : Fin H → Fin s → ℝ)
    (T : ℝ) (hT : (∑ i, w i) + (s : ℝ) < T) (x : Fin k → Bool) (j : Fin s) :
    (jointFamilyRidgeData w hw c T hT).score (cubeStarInput x j) =
      ∑ h, c h j / (T + h.val - jointFamilyRidgeValue w x) := by
  unfold ReverseCubeStarData.score jointFamilyRidgeData
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
  simp [boolToReal, jointFamilyRidgeValue]
  ring

noncomputable def jointFamilyRidgePole {H : ℕ} (T : ℝ) (h : Fin H) : ℝ := T + h.val

theorem jointFamilyRidgePole_injective {H : ℕ} (T : ℝ) :
    Function.Injective (jointFamilyRidgePole (H := H) T) := by
  intro i j hij
  apply Fin.ext
  exact_mod_cast add_left_cancel hij

noncomputable def jointFamilyRidgeResidue {s R : ℕ}
    (P : Fin s → Polynomial ℝ) (T : ℝ) (h : Fin (R + 1)) (j : Fin s) : ℝ :=
  -(Lagrange.nodal Finset.univ (jointFamilyRidgePole (H := R + 1) T)).eval 0 *
    (P j).eval (jointFamilyRidgePole T h) *
    Lagrange.nodalWeight Finset.univ (jointFamilyRidgePole T) h

theorem jointFamilyRidgeResidue_score {s R : ℕ}
    (P : Fin s → Polynomial ℝ) (hP : ∀ j, (P j).natDegree ≤ R)
    (T v : ℝ) (hv : ∀ h : Fin (R + 1), v ≠ jointFamilyRidgePole T h) (j : Fin s) :
    (∑ h : Fin (R + 1), jointFamilyRidgeResidue P T h j /
      (jointFamilyRidgePole T h - v)) =
      (P j).eval v * ∏ h : Fin (R + 1),
        jointFamilyRidgePole T h / (jointFamilyRidgePole T h - v) := by
  let p : Fin (R + 1) → ℝ := jointFamilyRidgePole T
  let N := (Lagrange.nodal Finset.univ p).eval 0
  have hdeg : (P j).degree < (R + 1 : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le (hP j))
      (by exact_mod_cast Nat.lt_succ_self R)
  have hterm (h : Fin (R + 1)) : jointFamilyRidgeResidue P T h j / (p h - v) =
      N * ((P j).eval (p h) * Lagrange.nodalWeight Finset.univ p h / (v - p h)) := by
    change (-N * (P j).eval (p h) * _) / (p h - v) = _
    rw [show p h - v = -(v - p h) by ring, div_neg]
    ring
  change (∑ h, jointFamilyRidgeResidue P T h j / (p h - v)) =
    (P j).eval v * ∏ h, p h / (p h - v)
  simp_rw [hterm]
  rw [← Finset.mul_sum, exterior_cauchy_barycentric p
    (jointFamilyRidgePole_injective T) (P j) hdeg v hv]
  have hprod : N / (Lagrange.nodal Finset.univ p).eval v =
      ∏ h : Fin (R + 1), p h / (p h - v) := by
    simp only [N, Lagrange.nodal, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro h _
    rw [show p h - v = -(v - p h) by ring, div_neg, neg_div]
  calc
    _ = (P j).eval v * (N / (Lagrange.nodal Finset.univ p).eval v) := by ring
    _ = _ := by rw [hprod]

theorem jointFamilyRidgePole_ratio_limit {H : ℕ} (h : Fin H) (v : ℝ) :
    Tendsto (fun T : ℝ ↦ jointFamilyRidgePole T h /
      (jointFamilyRidgePole T h - v)) atTop (nhds 1) := by
  have hden : Tendsto (fun T : ℝ ↦ jointFamilyRidgePole T h - v) atTop atTop := by
    simpa [jointFamilyRidgePole, sub_eq_add_neg, add_assoc] using
      tendsto_atTop_add_const_right atTop ((h.val : ℝ) - v) tendsto_id
  have hsmall := (tendsto_const_nhds (x := v)).div_atTop hden
  have hlim : Tendsto (fun T : ℝ ↦ 1 + v / (jointFamilyRidgePole T h - v))
      atTop (nhds 1) := by simpa using tendsto_const_nhds.add hsmall
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (v - (h.val : ℝ))] with T hT
  have hne : jointFamilyRidgePole T h - v ≠ 0 := by
    unfold jointFamilyRidgePole
    linarith
  field_simp
  ring

/-- A numerical polynomial correction is approximated with R+1 heads,
uniformly over every row and every independent column polynomial. -/
theorem jointFamily_polynomial_ridge_correction_preserves_signs {k s R : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (P : Fin s → Polynomial ℝ) (hP : ∀ j, (P j).natDegree ≤ R)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + (P j).eval (jointFamilyRidgeValue w x))) :
    ∃ L : ReverseCubeStarData k s (R + 1), ∀ x j,
      0 < outputSign (table x j) * (G x j + L.score (cubeStarInput x j)) := by
  classical
  have hev : ∀ᶠ T : ℝ in atTop, ∀ x j,
      0 < outputSign (table x j) * (G x j + (P j).eval (jointFamilyRidgeValue w x) *
        ∏ h : Fin (R + 1), jointFamilyRidgePole T h /
          (jointFamilyRidgePole T h - jointFamilyRidgeValue w x)) := by
    apply Filter.eventually_all.mpr
    intro x
    apply Filter.eventually_all.mpr
    intro j
    have hlim := tendsto_finsetProd (Finset.univ : Finset (Fin (R + 1))) (fun h _ ↦
      jointFamilyRidgePole_ratio_limit h (jointFamilyRidgeValue w x))
    have hlim' : Tendsto (fun T : ℝ ↦ (P j).eval (jointFamilyRidgeValue w x) *
        ∏ h : Fin (R + 1), jointFamilyRidgePole T h /
          (jointFamilyRidgePole T h - jointFamilyRidgeValue w x))
        atTop (nhds ((P j).eval (jointFamilyRidgeValue w x))) := by
      simpa using hlim.const_mul ((P j).eval (jointFamilyRidgeValue w x))
    exact ((tendsto_const_nhds.add hlim').const_mul (outputSign (table x j))).eventually
      (eventually_gt_nhds (hstrict x j))
  obtain ⟨T, hT, hsign⟩ := ((eventually_gt_atTop ((∑ i, w i) + (s : ℝ))).and hev).exists
  refine ⟨jointFamilyRidgeData w hw (jointFamilyRidgeResidue P T) T hT, fun x j ↦ ?_⟩
  rw [jointFamilyRidgeData_score]
  have hv : ∀ h : Fin (R + 1), jointFamilyRidgeValue w x ≠ jointFamilyRidgePole T h := by
    intro h
    have hb := jointFamilyRidgeValue_le w hw x
    have hh : (0 : ℝ) ≤ h.val := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    unfold jointFamilyRidgePole
    linarith
  change 0 < outputSign (table x j) * (G x j +
    ∑ h, jointFamilyRidgeResidue P T h j / (jointFamilyRidgePole T h - jointFamilyRidgeValue w x))
  rw [jointFamilyRidgeResidue_score P hP T _ hv j]
  exact hsign x j

/-- A family of m positive row statistics and arbitrary independent
degree-R column polynomials costs exactly m(R+1) correction heads. -/
theorem jointFamily_polynomial_ridge_family_correction_preserves_signs {k s R m : ℕ}
    (w : Fin m → Fin k → ℝ) (hw : ∀ t i, 0 < w t i)
    (P : Fin m → Fin s → Polynomial ℝ) (hP : ∀ t j, (P t j).natDegree ≤ R)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + ∑ t, (P t j).eval (jointFamilyRidgeValue (w t) x))) :
    ∃ L : ReverseCubeStarData k s (m * (R + 1)), ∀ x j,
      0 < outputSign (table x j) * (G x j + L.score (cubeStarInput x j)) := by
  classical
  induction m generalizing G with
  | zero =>
    rw [Nat.zero_mul]
    let L : ReverseCubeStarData k s 0 := {
      a₀ := Fin.elim0
      b₀ := Fin.elim0
      a := Fin.elim0
      b := Fin.elim0
      positive := fun h ↦ Fin.elim0 h
      negative := fun h ↦ Fin.elim0 h
      zero_column := fun _ ↦ by simp }
    refine ⟨L, fun x j ↦ ?_⟩
    simpa [ReverseCubeStarData.score] using hstrict x j
  | succ m ih =>
    have hs₀ : ∀ x j, 0 < outputSign (table x j) *
        ((G x j + ∑ t : Fin m,
          (P t.succ j).eval (jointFamilyRidgeValue (w t.succ) x)) +
          (P 0 j).eval (jointFamilyRidgeValue (w 0) x)) := by
      intro x j
      simpa only [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hstrict x j
    obtain ⟨L₀, hL₀⟩ := jointFamily_polynomial_ridge_correction_preserves_signs
      (w 0) (hw 0) (P 0) (hP 0)
      (fun x j ↦ G x j + ∑ t : Fin m,
        (P t.succ j).eval (jointFamilyRidgeValue (w t.succ) x)) table hs₀
    have hsr : ∀ x j, 0 < outputSign (table x j) *
        ((G x j + L₀.score (cubeStarInput x j)) + ∑ t : Fin m,
          (P t.succ j).eval (jointFamilyRidgeValue (w t.succ) x)) := by
      intro x j
      simpa only [add_assoc, add_left_comm, add_comm] using hL₀ x j
    obtain ⟨Lr, hLr⟩ := ih (fun t ↦ w t.succ) (fun t ↦ hw t.succ)
      (fun t ↦ P t.succ) (fun t ↦ hP t.succ)
      (fun x j ↦ G x j + L₀.score (cubeStarInput x j)) hsr
    rw [Nat.succ_mul]
    refine ⟨jointFamilyAppendData Lr L₀, fun x j ↦ ?_⟩
    rw [jointFamilyAppendData_score]
    simpa only [add_assoc, add_left_comm, add_comm] using hLr x j

end HeadComplexity.AxisZeroGluing
