import HeadComplexity.Results.JointFamilySignedJets

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private def pointDistance {k : ℕ} (x₀ x : Fin k → Bool) : ℕ :=
  ∑ i, if x i = x₀ i then 0 else 1

private theorem pointDistance_le {k : ℕ} (x₀ x : Fin k → Bool) :
    pointDistance x₀ x ≤ k := by
  calc
    _ ≤ ∑ _i : Fin k, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> omega
    _ = _ := by simp

private theorem pointDistance_eq_zero_iff {k : ℕ} (x₀ x : Fin k → Bool) :
    pointDistance x₀ x = 0 ↔ x = x₀ := by
  simp only [pointDistance, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h
    funext i
    simpa using h i
  · intro h i
    simp [h]

private noncomputable def pointSignedSlope {k : ℕ} (x₀ : Fin k → Bool) (i : Fin k) : ℝ :=
  if x₀ i then -1 else 1

private def pointShift {k : ℕ} (x₀ : Fin k → Bool) : ℕ :=
  ∑ i, if x₀ i then 1 else 0

private theorem pointSignedSlope_value {k : ℕ} (x₀ x : Fin k → Bool) :
    jointFamilyRidgeValue (pointSignedSlope x₀) x =
      (pointDistance x₀ x : ℝ) - pointShift x₀ := by
  simp only [jointFamilyRidgeValue, pointDistance, pointShift, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero, Nat.cast_one, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> cases hi : x₀ i <;> norm_num [pointSignedSlope, boolToReal, hx, hi]

/-- Arbitrary numerical repair at one row costs k+1 heads while preserving
all specified strict signs on every row and column. This is an approximation
statement, so it does not claim exact zeros outside the repaired row. -/
theorem jointFamily_point_correction_preserves_signs {k s : ℕ}
    (x₀ : Fin k → Bool) (c : Fin s → ℝ)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + if x = x₀ then c j else 0)) :
    ∃ L : ReverseCubeStarData k s (k + 1), ∀ x j,
      0 < outputSign (table x j) * (G x j + L.score (cubeStarInput x j)) := by
  classical
  let nodes : Fin (k + 1) → ℝ := fun r ↦ r.val - (pointShift x₀ : ℝ)
  have hnodes : Function.Injective nodes := by
    intro i j h
    apply Fin.ext
    dsimp [nodes] at h
    have he : (i.val : ℝ) = j.val := by linarith
    exact_mod_cast he
  let Q : Polynomial ℝ := Lagrange.basis Finset.univ nodes (0 : Fin (k + 1))
  let P : Fin s → Polynomial ℝ := fun j ↦ Polynomial.C (c j) * Q
  have hQ : Q.natDegree ≤ k := by
    have h := Lagrange.natDegree_basis hnodes.injOn
      (Finset.mem_univ (0 : Fin (k + 1)))
    simpa [Q] using h.le
  have hP : ∀ j, (P j).natDegree ≤ k := by
    intro j
    exact (Polynomial.natDegree_C_mul_le _ _).trans hQ
  apply jointFamily_signed_polynomial_correction_preserves_signs
    (pointSignedSlope x₀) P hP G table
  intro x j
  have hval : (P j).eval (jointFamilyRidgeValue (pointSignedSlope x₀) x) =
      if x = x₀ then c j else 0 := by
    let d : Fin (k + 1) := ⟨pointDistance x₀ x, Nat.lt_succ_of_le (pointDistance_le x₀ x)⟩
    have hd : jointFamilyRidgeValue (pointSignedSlope x₀) x = nodes d :=
      pointSignedSlope_value x₀ x
    rw [hd]
    simp only [P, Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hx : x = x₀
    · have hd0 : d = 0 := by
        apply Fin.ext
        exact (pointDistance_eq_zero_iff x₀ x).2 hx
      rw [hd0]
      have hq : Q.eval (nodes 0) = 1 := Lagrange.eval_basis_self hnodes.injOn
        (Finset.mem_univ (0 : Fin (k + 1)))
      rw [hq]
      simp [hx]
    · have hd0 : (0 : Fin (k + 1)) ≠ d := by
        intro hh
        apply hx
        apply (pointDistance_eq_zero_iff x₀ x).1
        exact (congrArg Fin.val hh).symm
      have hq : Q.eval (nodes d) = 0 := Lagrange.eval_basis_of_ne
        (v := nodes) hd0 (Finset.mem_univ d)
      rw [hq]
      simp [hx]
  rw [hval]
  exact hstrict x j


/-- An arbitrary finite family of row exceptions costs k+1 heads per row.
All prior strict signs survive the approximation, on every required input. -/
theorem jointFamily_point_family_correction_preserves_signs {k s m : ℕ}
    (x₀ : Fin m → Fin k → Bool) (c : Fin m → Fin s → ℝ)
    (G : (Fin k → Bool) → Fin s → ℝ)
    (table : (Fin k → Bool) → Fin s → Bool)
    (hstrict : ∀ x j, 0 < outputSign (table x j) *
      (G x j + ∑ h, if x = x₀ h then c h j else 0)) :
    ∃ L : ReverseCubeStarData k s (m * (k + 1)), ∀ x j,
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
    refine ⟨L, ?_⟩
    intro x j
    simpa [ReverseCubeStarData.score] using hstrict x j
  | succ m ih =>
    have hs₀ : ∀ x j, 0 < outputSign (table x j) *
        ((G x j + ∑ h : Fin m, if x = x₀ h.succ then c h.succ j else 0) +
          if x = x₀ 0 then c 0 j else 0) := by
      intro x j
      simpa only [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hstrict x j
    obtain ⟨L₀, hL₀⟩ := jointFamily_point_correction_preserves_signs (x₀ 0) (c 0)
      (fun x j ↦ G x j + ∑ h : Fin m, if x = x₀ h.succ then c h.succ j else 0)
      table hs₀
    have hsr : ∀ x j, 0 < outputSign (table x j) *
        ((G x j + L₀.score (cubeStarInput x j)) +
          ∑ h : Fin m, if x = x₀ h.succ then c h.succ j else 0) := by
      intro x j
      simpa only [add_assoc, add_left_comm, add_comm] using hL₀ x j
    obtain ⟨Lr, hLr⟩ := ih (fun h ↦ x₀ h.succ) (fun h ↦ c h.succ)
      (fun x j ↦ G x j + L₀.score (cubeStarInput x j)) hsr
    rw [Nat.succ_mul]
    refine ⟨jointFamilyAppendData Lr L₀, ?_⟩
    intro x j
    rw [jointFamilyAppendData_score]
    simpa only [add_assoc, add_left_comm, add_comm] using hLr x j

end HeadComplexity.AxisZeroGluing
