import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false

/-!
A product of two positive-slope affine forms has a two-head sign representation.
The first head has a constant denominator, so its positive numerator slopes are
checked explicitly rather than assuming arbitrary affine constant-denominator heads.
-/

noncomputable section
namespace HeadComplexity.TwoHeadAffineProduct
open scoped BigOperators

variable {n : ℕ}

def positiveAffineAtom (c : ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    FracAtom n where
  η := c * (1 + ∑ i, a i)
  δ := 1 + ∑ i, a i
  γ := 1
  α := 1
  ρ := a
  m := fun _ ↦ 0
  hγ := by norm_num
  hα := by norm_num
  hρ := ha

theorem positiveAffineAtom_eval (c : ℝ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (x : Fin n → Bool) :
    (positiveAffineAtom c a ha).eval x = affineValue c a x := by
  have hD : 0 < 1 + ∑ i, a i :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ ↦ (ha i).le)
  have hs : (∑ i, a i * (if x i then 1 + ∑ j, a j else 0)) =
      (1 + ∑ j, a j) * ∑ i, a i * boolToReal (x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [boolToReal] <;> ring
  simp only [FracAtom.eval, FracAtom.wt, positiveAffineAtom, ite_self,
    mul_one, zero_add]
  rw [hs]
  unfold affineValue
  field_simp

def productAtoms (c d K : ℝ) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hK : 0 < K + d) :
    Fin 2 → FracAtom n :=
  ![positiveAffineAtom c a ha,
    FracAtom.ofPositiveAffineRatio (-K * c) (fun i ↦ -K * a i)
      (K + d) b hK hb]

/-- Exact product score with a denominator positive on the full Boolean cube. -/
theorem productAtoms_score (c d K : ℝ) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hK : 0 < K + d)
    (x : Fin n → Bool) :
    ∑ h, (productAtoms c d K a b ha hb hK h).eval x =
      affineValue c a x * affineValue d b x / (K + affineValue d b x) := by
  have hden : 0 < K + affineValue d b x := by
    simpa only [← affineValue_const_add] using affineValue_pos (K+d) b hK hb x
  simp only [Fin.sum_univ_two, productAtoms, Matrix.cons_val_zero,
    Matrix.cons_val_one, positiveAffineAtom_eval, FracAtom.ofPositiveAffineRatio_eval,
    affineValue_smul, affineValue_const_add]
  field_simp
  ring

/-- The two-head construction is in the unchanged original model. -/
theorem product_fracComputable (c d K : ℝ) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hK : 0 < K + d)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < affineValue c a x * affineValue d b x ↔ f x = true) :
    fracComputable n 2 f := by
  refine ⟨productAtoms c d K a b ha hb hK, 0, fun x ↦ ?_⟩
  rw [zero_add, productAtoms_score]
  have hden : 0 < K + affineValue d b x := by
    simpa only [← affineValue_const_add] using affineValue_pos (K+d) b hK hb x
  rw [div_pos_iff_of_pos_right hden]
  exact hf x

end HeadComplexity.TwoHeadAffineProduct
