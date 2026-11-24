import HeadComplexity.Results.JointFamilyRidgeCorrections

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- An isolated level of a positive affine statistic admits an exact shared
point repair. Every column has its own arbitrary amplitude, while the
entire bank has positive denominators and strictly negative local slopes. -/
theorem jointFamily_isolated_level_repair {k s R : ℕ}
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (code : (Fin k → Bool) → Fin (R + 1))
    (hcode : ∀ x, jointFamilyRidgeValue w x = (code x).val)
    (x₀ : Fin k → Bool) (hiso : ∀ x, code x = code x₀ → x = x₀)
    (c : Fin s → ℝ) :
    ∃ L : ReverseCubeStarData k s (R + 1), ∀ x j,
      L.score (cubeStarInput x j) = if x = x₀ then c j else 0 := by
  classical
  let T : ℝ := (∑ i, w i) + s + 1
  have hT : (∑ i, w i) + (s : ℝ) < T := by dsimp [T]; linarith
  let v : Fin (R + 1) → ℝ := fun i ↦ i.val
  have hv : Function.Injective v := by
    intro i j h
    apply Fin.ext
    dsimp [v] at h
    exact_mod_cast h
  let Q : Polynomial ℝ := Lagrange.basis Finset.univ v (code x₀)
  have hQdeg : Q.natDegree ≤ R := by
    have h := Lagrange.natDegree_basis hv.injOn (Finset.mem_univ (code x₀))
    simpa [Q] using h.le
  let F : ℝ := ∏ h : Fin (R + 1), jointFamilyRidgePole T h /
    (jointFamilyRidgePole T h - jointFamilyRidgeValue w x₀)
  have hden (x : Fin k → Bool) (h : Fin (R + 1)) :
      0 < jointFamilyRidgePole T h - jointFamilyRidgeValue w x := by
    have hx := jointFamilyRidgeValue_le w hw x
    have hh : (0 : ℝ) ≤ h.val := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    dsimp [jointFamilyRidgePole]
    linarith
  have hTpos : 0 < T := by
    have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ ↦ (hw i).le)
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    dsimp [T]
    linarith
  have hF : F ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro h _
    apply div_pos _ (hden x₀ h)
    dsimp [jointFamilyRidgePole]
    positivity
  let P : Fin s → Polynomial ℝ := fun j ↦ Polynomial.C (c j / F) * Q
  have hP : ∀ j, (P j).natDegree ≤ R := by
    intro j
    exact (Polynomial.natDegree_C_mul_le _ _).trans hQdeg
  refine ⟨jointFamilyRidgeData w hw (jointFamilyRidgeResidue P T) T hT, ?_⟩
  intro x j
  rw [jointFamilyRidgeData_score]
  change (∑ h, jointFamilyRidgeResidue P T h j /
    (jointFamilyRidgePole T h - jointFamilyRidgeValue w x)) = _
  rw [jointFamilyRidgeResidue_score P hP T _
    (fun h ↦ ne_of_lt (by linarith [hden x h])) j]
  simp only [P, Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hx : x = x₀
  · subst x
    have hQ : Q.eval (jointFamilyRidgeValue w x₀) = 1 := by
      rw [hcode]
      exact Lagrange.eval_basis_self hv.injOn (Finset.mem_univ (code x₀))
    rw [hQ]
    simp only [mul_one, ite_true]
    change c j / F * F = c j
    exact div_mul_cancel₀ _ hF
  · have hc : code x₀ ≠ code x := by
      intro h
      exact hx (hiso x h.symm)
    have hQ : Q.eval ((code x).val : ℝ) = 0 :=
      Lagrange.eval_basis_of_ne (v := v) hc (Finset.mem_univ (code x))
    rw [hcode, hQ]
    simp [hx]


private def pointWeight {k : ℕ} (x₀ : Fin k → Bool) (i : Fin k) : ℕ :=
  if x₀ i then 1 else k + 1

private def pointCode {k : ℕ} (x₀ x : Fin k → Bool) : ℕ :=
  ∑ i, if x i then pointWeight x₀ i else 0

private theorem pointCode_le {k : ℕ} (x₀ x : Fin k → Bool) :
    pointCode x₀ x ≤ k * (k + 1) := by
  calc
    _ ≤ ∑ _i : Fin k, (k + 1) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [pointWeight]
      cases x i <;> cases x₀ i <;> simp
    _ = _ := by simp

private theorem pointCode_self_le {k : ℕ} (x₀ : Fin k → Bool) :
    pointCode x₀ x₀ ≤ k := by
  calc
    _ ≤ ∑ _i : Fin k, 1 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [pointWeight]
      cases x₀ i <;> simp
    _ = _ := by simp

private theorem pointCode_isolates {k : ℕ} (x₀ x : Fin k → Bool)
    (heq : pointCode x₀ x = pointCode x₀ x₀) : x = x₀ := by
  have hsub (i : Fin k) (hi : x₀ i = false) : x i = false := by
    by_contra hx
    have hxt : x i = true := by simpa using hx
    have hs : k + 1 ≤ pointCode x₀ x := by
      have hh := Finset.single_le_sum
        (f := fun j ↦ if x j then pointWeight x₀ j else 0)
        (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      simpa [pointWeight, pointCode, hi, hxt] using hh
    have := pointCode_self_le x₀
    omega
  have hle (i : Fin k) (_ : i ∈ (Finset.univ : Finset (Fin k))) :
      (if x i then pointWeight x₀ i else 0) ≤
      (if x₀ i then pointWeight x₀ i else 0) := by
    cases hi : x₀ i
    · simp [hsub i hi]
    · cases x i <;> simp
  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  funext i
  have h := hpoint i (Finset.mem_univ i)
  cases hx : x i <;> cases hi : x₀ i <;> simp_all [pointWeight]

/-- Every row point has an exact indicator bank with at most quadratic
cost. Its arbitrary amplitudes on all independent columns share the bank.
No exceptions on other row inputs are introduced. -/
theorem jointFamily_point_repair {k s : ℕ}
    (x₀ : Fin k → Bool) (c : Fin s → ℝ) :
    ∃ L : ReverseCubeStarData k s (k * (k + 1) + 1), ∀ x j,
      L.score (cubeStarInput x j) = if x = x₀ then c j else 0 := by
  let w : Fin k → ℝ := fun i ↦ pointWeight x₀ i
  have hw : ∀ i, 0 < w i := by
    intro i
    dsimp [w, pointWeight]
    split <;> positivity
  let code : (Fin k → Bool) → Fin (k * (k + 1) + 1) := fun x ↦
    ⟨pointCode x₀ x, Nat.lt_succ_of_le (pointCode_le x₀ x)⟩
  have hcode : ∀ x, jointFamilyRidgeValue w x = (code x).val := by
    intro x
    dsimp [jointFamilyRidgeValue, code, pointCode]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [w, boolToReal]
  apply jointFamily_isolated_level_repair w hw code hcode x₀ ?_ c
  intro x hx
  apply pointCode_isolates x₀ x
  exact congrArg Fin.val hx


/-- A list of exceptional row points is repaired with a quadratic cost per
row, independent of the number of independently labeled columns. -/
theorem jointFamily_point_family_repair {k s m : ℕ}
    (x₀ : Fin m → Fin k → Bool) (c : Fin m → Fin s → ℝ) :
    ∃ L : ReverseCubeStarData k s (m * (k * (k + 1) + 1)), ∀ x j,
      L.score (cubeStarInput x j) = ∑ h, if x = x₀ h then c h j else 0 := by
  classical
  induction m with
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
    refine ⟨L, ?_⟩
    intro x j
    simp [ReverseCubeStarData.score]
  | succ m ih =>
    obtain ⟨L₀, hL₀⟩ := jointFamily_point_repair (x₀ 0) (c 0)
    obtain ⟨Lr, hLr⟩ := ih (fun h ↦ x₀ h.succ) (fun h ↦ c h.succ)
    rw [Nat.succ_mul]
    refine ⟨jointFamilyAppendData Lr L₀, ?_⟩
    intro x j
    rw [jointFamilyAppendData_score, hLr, hL₀, Fin.sum_univ_succ]
    exact add_comm _ _

end HeadComplexity.AxisZeroGluing
