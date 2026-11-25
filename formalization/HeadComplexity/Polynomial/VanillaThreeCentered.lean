import HeadComplexity.Results.RoPETwoHeads
import HeadComplexity.Polynomial.RoPECrossBlockCoefficients

set_option linter.style.header false

/-!
# Strict centered cubic factors extracted from vanilla attention

The free threshold provides the strict finite-cube margin. The original
vanilla definitions and exact affine-fraction normal form are unchanged.
-/

namespace HeadComplexity.VanillaThreeCentered

open MvPolynomial RoPECrossBlockCoefficients
open scoped BigOperators

structure Data (σ : Type*) where
  denominatorConstant : Fin 3 → ℝ
  numeratorConstant : Fin 3 → ℝ
  denominatorSlope : Fin 3 → σ → ℝ
  numeratorSlope : Fin 3 → σ → ℝ

noncomputable def Data.polynomial {σ : Type*} [Fintype σ] (a : Data σ) :
    MvPolynomial σ ℝ :=
  let D h := affine (a.denominatorConstant h) (a.denominatorSlope h)
  let N h := affine (a.numeratorConstant h) (a.numeratorSlope h)
  N 0 * D 1 * D 2 + N 1 * D 0 * D 2 + N 2 * D 0 * D 1

def Oriented {σ : Type*} (v : σ → ℝ) : Prop :=
  (∀ i, 0 < v i) ∨ (∀ i, v i < 0) ∨ (∀ i, v i = 0)

theorem affine_totalDegree_le {σ : Type*} [Fintype σ] (c : ℝ) (v : σ → ℝ) :
    (affine c v).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem Data.totalDegree_le {σ : Type*} [Fintype σ] (a : Data σ) :
    a.polynomial.totalDegree ≤ 3 := by
  have hprod (c₁ c₂ c₃ : ℝ) (v₁ v₂ v₃ : σ → ℝ) :
      (affine c₁ v₁ * affine c₂ v₂ * affine c₃ v₃).totalDegree ≤ 3 := by
    apply (totalDegree_mul _ _).trans
    have h := totalDegree_mul (affine c₁ v₁) (affine c₂ v₂)
    have h₁ := affine_totalDegree_le c₁ v₁
    have h₂ := affine_totalDegree_le c₂ v₂
    have h₃ := affine_totalDegree_le c₃ v₃
    omega
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (hprod _ _ _ _ _ _) (hprod _ _ _ _ _ _)))
    (hprod _ _ _ _ _ _))

theorem centered_affine_eval {σ : Type*} [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (L : CubeAffine n) (x : σ → Bool) :
    eval (fun i ↦ 2 * boolToReal (x i) - 1)
      (affine (L.const + ∑ i, L.slope i / 2) (fun i ↦ L.slope (e i) / 2)) =
      L.eval (fun i ↦ x (e.symm i)) := by
  simp only [affine, map_add, map_sum, map_mul, eval_C, eval_X, CubeAffine.eval]
  rw [← e.sum_comp (fun i ↦ L.slope i / 2),
    ← e.sum_comp (fun i ↦ L.slope i * boolToReal (x (e.symm i)))]
  simp only [Equiv.symm_apply_apply]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every actual vanilla three-head classifier has a strict centered cubic
whose denominator rows retain the original global orientation. -/
theorem exists_data_of_vanilla {n : ℕ} {σ : Type*} [Fintype σ]
    (e : σ ≃ Fin n) (f : (Fin n → Bool) → Bool)
    (hf : computableWithSharedHeadsN n 3 f) :
    ∃ a : Data σ, (∀ h, Oriented (a.denominatorSlope h)) ∧
      ∀ x : σ → Bool,
        (0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ↔
          f (fun i ↦ x (e.symm i)) = true) ∧
        eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ≠ 0 := by
  classical
  obtain ⟨r, c, hr, hclass⟩ :=
    (computableWithSharedHeadsN_iff_affineFractionComputable 3 f).mp hf
  obtain ⟨δ, _, hδ⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (r h).eval x)
  let c' := c - δ
  let N : Fin 3 → CubeAffine n :=
    ![CubeAffine.combine 1 (r 0).numForm c' (r 0).denForm,
      (r 1).numForm, (r 2).numForm]
  let D : Fin 3 → CubeAffine n := fun h ↦ (r h).denForm
  let a : Data σ := {
    denominatorConstant := fun h ↦ (D h).const + ∑ i, (D h).slope i / 2
    numeratorConstant := fun h ↦ (N h).const + ∑ i, (N h).slope i / 2
    denominatorSlope := fun h i ↦ (D h).slope (e i) / 2
    numeratorSlope := fun h i ↦ (N h).slope (e i) / 2 }
  refine ⟨a, ?_, ?_⟩
  · intro h
    rcases (hr h).2.1 with hp | hn | hz
    · exact Or.inl (fun i ↦ div_pos (hp (e i)) (by norm_num))
    · exact Or.inr (Or.inl (fun i ↦ div_neg_of_neg_of_pos (hn (e i)) (by norm_num)))
    · exact Or.inr (Or.inr (fun i ↦ by change (r h).C (e i) / 2 = 0; rw [hz, zero_div]))
  · intro x
    let y : Fin n → Bool := fun i ↦ x (e.symm i)
    have hpos (h : Fin 3) : 0 < (r h).denominator y := (hr h).1 y
    have hp := mul_pos (mul_pos (hpos 0) (hpos 1)) (hpos 2)
    have he : eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial =
        (r 0).denominator y * (r 1).denominator y * (r 2).denominator y *
          ((c + ∑ h, (r h).eval y) - δ) := by
      simp only [Data.polynomial, a, map_add, map_mul,
        centered_affine_eval e (N 0) x, centered_affine_eval e (N 1) x,
        centered_affine_eval e (N 2) x, centered_affine_eval e (D 0) x,
        centered_affine_eval e (D 1) x, centered_affine_eval e (D 2) x]
      change (N 0).eval y * (D 1).eval y * (D 2).eval y +
        (N 1).eval y * (D 0).eval y * (D 2).eval y +
        (N 2).eval y * (D 0).eval y * (D 1).eval y = _
      simp only [N, D, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, CubeAffine.combine_eval, one_mul,
        AffineFraction.numForm_eval, AffineFraction.denForm_eval,
        Fin.sum_univ_three, AffineFraction.eval]
      dsimp [c']
      field_simp [(hpos 0).ne', (hpos 1).ne', (hpos 2).ne']
      ring
    rw [he]
    exact ⟨(mul_pos_iff_of_pos_left hp).trans ((hδ y).1.trans (hclass y)),
      mul_ne_zero hp.ne' (hδ y).2⟩

end HeadComplexity.VanillaThreeCentered
