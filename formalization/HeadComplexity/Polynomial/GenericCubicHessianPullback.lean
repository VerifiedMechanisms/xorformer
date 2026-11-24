import HeadComplexity.Polynomial.GenericCubicHessian

set_option linter.style.header false

/-!
# Hessians of arbitrary linear pullbacks of the generic cubic

These identities concern actual iterated polynomial derivatives. No independence,
nonzero condition, or orientation assumption is imposed on the six linear forms.
-/

namespace HeadComplexity.GenericCubicHessianPullback

noncomputable section
open scoped BigOperators Matrix
open MvPolynomial

def linearPolynomial {n : ℕ} (a : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, C (a i) * X i

def linearValue {n : ℕ} (a z : Fin n → ℝ) : ℝ := ∑ i, a i * z i

@[simp] theorem eval_linearPolynomial {n : ℕ} (a z : Fin n → ℝ) :
    eval z (linearPolynomial a) = linearValue a z := by
  simp [linearPolynomial, linearValue]

@[simp] theorem pderiv_linearPolynomial {n : ℕ} (a : Fin n → ℝ) (j : Fin n) :
    pderiv j (linearPolynomial a) = C (a j) := by
  classical
  simp [linearPolynomial, map_sum, Pi.single_apply]

def cubic {n : ℕ} (S B : Fin 3 → Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  linearPolynomial (S 0) * linearPolynomial (B 1) * linearPolynomial (B 2) +
    linearPolynomial (S 1) * linearPolynomial (B 0) * linearPolynomial (B 2) +
    linearPolynomial (S 2) * linearPolynomial (B 0) * linearPolynomial (B 1)

def slopes {n : ℕ} (S B : Fin 3 → Fin n → ℝ) : Matrix (Fin n) (Fin 3 ⊕ Fin 3) ℝ :=
  fun i ↦ Sum.elim (fun h ↦ S h i) (fun h ↦ B h i)

def polynomialHessian {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (z : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦ eval z (pderiv i (pderiv j p))

theorem eval_cubic {n : ℕ} (S B : Fin 3 → Fin n → ℝ) (z : Fin n → ℝ) :
    eval z (cubic S B) =
      linearValue (S 0) z * linearValue (B 1) z * linearValue (B 2) z +
      linearValue (S 1) z * linearValue (B 0) z * linearValue (B 2) z +
      linearValue (S 2) z * linearValue (B 0) z * linearValue (B 1) z := by
  simp [cubic]

theorem hessian_pullback {n : ℕ} (S B : Fin 3 → Fin n → ℝ) (z : Fin n → ℝ) :
    polynomialHessian (cubic S B) z =
      slopes S B * GenericCubicHessian.hessian
        (fun h ↦ linearValue (S h) z) (fun h ↦ linearValue (B h) z) * (slopes S B)ᵀ := by
  ext i j
  simp [polynomialHessian, cubic, map_add,
    Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
    GenericCubicHessian.hessian, GenericCubicHessian.offDiagonal,
    Matrix.fromBlocks, Matrix.transpose_apply, slopes]
  ring

theorem hessian_rank_le_six {n : ℕ} (S B : Fin 3 → Fin n → ℝ) (z : Fin n → ℝ) :
    (polynomialHessian (cubic S B) z).rank ≤ 6 := by
  rw [hessian_pullback]
  calc
    _ ≤ (slopes S B * GenericCubicHessian.hessian
        (fun h ↦ linearValue (S h) z) (fun h ↦ linearValue (B h) z)).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ (slopes S B).rank := Matrix.rank_mul_le_left _ _
    _ ≤ 6 := by simpa using Matrix.rank_le_card_width (slopes S B)

theorem linearPolynomial_add_smul {n : ℕ} (a b : Fin n → ℝ) (c : ℝ) :
    linearPolynomial (fun i ↦ a i + c * b i) =
      linearPolynomial a + C c * linearPolynomial b := by
  simp [linearPolynomial, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- The readout constant can be absorbed into the first numerator, including at
the homogeneous cubic level relevant to the lower-bound argument. -/
theorem cubic_add_readout {n : ℕ} (S B : Fin 3 → Fin n → ℝ) (c : ℝ) :
    cubic S B + C c * linearPolynomial (B 0) *
        linearPolynomial (B 1) * linearPolynomial (B 2) =
      cubic ![fun i ↦ S 0 i + c * B 0 i, S 1, S 2] B := by
  simp [cubic, linearPolynomial_add_smul]
  ring

theorem hessian_rank_le_six_with_readout {n : ℕ}
    (S B : Fin 3 → Fin n → ℝ) (c : ℝ) (z : Fin n → ℝ) :
    (polynomialHessian (cubic S B + C c * linearPolynomial (B 0) *
      linearPolynomial (B 1) * linearPolynomial (B 2)) z).rank ≤ 6 := by
  rw [cubic_add_readout]
  exact hessian_rank_le_six _ _ _

end
end HeadComplexity.GenericCubicHessianPullback
