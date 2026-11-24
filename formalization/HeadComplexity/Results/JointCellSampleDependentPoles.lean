import HeadComplexity.Results.JointCellRankRepair

set_option linter.style.header false

/-! An exact sample-dependent pole interface. This permits arbitrary finite
label data to affect every memory point's pole pencil without increasing the
head count. It does not assert that the resulting decoder has more capacity. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- Each memory point may choose its own pole pencil and column tokens.
The pencils and tokens may depend on all labels. The row residues remain
shared across memory points, so the line aggregation still factors. -/
theorem jointCell_exists_affinePlane_point_poles {F : Type*} [Field F] [Fintype F]
    {r s : ℕ} (δ : ℝ) (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (pole : (F × F) → F → ℝ) (token : (F × F) → Fin s → ℝ)
    (hpole : ∀ g a, 1 - δ < pole g a ∧ pole g a < 1)
    (htoken : ∀ g j, 0 < token g j ∧ token g j < δ)
    (point : Fin r → F × F)
    (η : Fin r → F → ℝ) (rowBias : Fin r → ℝ) :
    ∃ Q : ReverseAxisData r s (3 * Fintype.card (F × F) + 4),
      ∀ i j, Q.score (localGrid i j) =
        rowBias i + ∑ a : F, η i a / (pole (point i) a - token (point i) j) := by
  classical
  let N := Fintype.card (F × F)
  let e : Fin N ≃ (F × F) := (Fintype.equivFin (F × F)).symm
  let Z : (F × F) → Fin s → ℝ := fun L j ↦
    ∑ g : F × F, if g.2 = L.1 * g.1 + L.2 then
      1 / (pole g L.1 - token g j) else 0
  let f : Fin N → Fin r → ℝ := fun l i ↦
    if (e l).2 = (point i).2 - (e l).1 * (point i).1 then η i (e l).1 else 0
  let off : Fin r → Fin s → ℝ := fun i j ↦
    ∑ g : F × F, if g.1 ≠ (point i).1 then
      η i (affinePlaneSlope (point i) g) /
        (pole g (affinePlaneSlope (point i) g) - token g j) else 0
  have hline (i : Fin r) (j : Fin s) :
      (∑ l : Fin N, f l i * Z (e l) j) =
        (∑ a : F, η i a / (pole (point i) a - token (point i) j)) + off i j := by
    have hReindex : (∑ l : Fin N, f l i * Z (e l) j) =
        ∑ L : F × F,
          (if L.2 = (point i).2 - L.1 * (point i).1 then η i L.1 else 0) * Z L j :=
      e.sum_comp (fun L : F × F ↦
        (if L.2 = (point i).2 - L.1 * (point i).1 then η i L.1 else 0) * Z L j)
    rw [hReindex, affinePlane_line_rank_identity]
    have hInc := affinePlane_weighted_pencil_identity (point i) (η i)
      (fun a g ↦ 1 / (pole g a - token g j))
    dsimp [Z]
    simp only [mul_one_div] at hInc
    exact hInc
  let A : (F × F) → Fin r → ℝ := fun g i ↦
    if g.1 ≠ (point i).1 then -η i (affinePlaneSlope (point i) g) else 0
  let D : (F × F) → Fin r → ℝ := fun g i ↦ pole g (affinePlaneSlope (point i) g)
  have hCorr (i : Fin r) (j : Fin s) :
      (∑ l : Fin N, A (e l) i / (D (e l) i - token (e l) j)) = -off i j := by
    have hReindex : (∑ l : Fin N, A (e l) i /
        (D (e l) i - token (e l) j)) =
        ∑ g : F × F, A g i / (D g i - token g j) :=
      e.sum_comp (fun g : F × F ↦ A g i / (D g i - token g j))
    rw [hReindex]
    dsimp [off]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro g _
    dsimp [A, D]
    split_ifs <;> simp only [neg_div, zero_div, neg_zero]
  have hex := exists_reverse_axis_rank_cauchy_grid_joint δ f (fun l ↦ Z (e l))
    (fun l ↦ A (e l)) (fun l ↦ D (e l)) (fun l j ↦ token (e l) j)
    rowBias (fun _ ↦ 0) 0 hδ hsize (fun l i ↦ hpole (e l) _) (fun l j ↦ htoken (e l) j)
  have hcount : N + 2 * N + 4 = 3 * Fintype.card (F × F) + 4 := by dsimp [N]; omega
  rw [hcount] at hex
  obtain ⟨Q, hQ⟩ := hex
  refine ⟨Q, ?_⟩
  intro i j
  rw [hQ, hline, hCorr]
  ring

end HeadComplexity.AxisZeroGluing
