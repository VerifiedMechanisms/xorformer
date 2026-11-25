import HeadComplexity.Polynomial.BlockCoefficientProjection
import HeadComplexity.Polynomial.RoPEGeneralPolarization
import HeadComplexity.Polynomial.VanillaBlockDerivatives

set_option linter.style.header false

/-!
# Mixed block coefficients equal projected directional derivatives

This interface connects the coefficients preserved by Boolean replica averaging
to the derivative contraction used in the algebraic rank obstruction.
-/

noncomputable section

namespace HeadComplexity.BlockCoefficientDerivatives

open MvPolynomial RoPEGeneralDerivative BlockCoefficientProjection
open RoPEGeneralPolarization
open scoped BigOperators

variable {β σ A : Type*}

theorem coeff_pderiv_formula [CommRing A] (i : β) (d : β →₀ ℕ)
    (P : MvPolynomial β A) :
    coeff d (pderiv i P) = ((d i + 1 : ℕ) : A) * coeff (d + Finsupp.single i 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [pderiv_monomial]
    by_cases hzero : e i = 0
    · have hne : e ≠ d + Finsupp.single i 1 := by
        intro h
        have hi := congrArg (fun a : β →₀ ℕ ↦ a i) h
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, hzero] at hi
        omega
      simp [hzero, coeff_monomial, hne]
    · have hle : Finsupp.single i 1 ≤ e := by
        rw [Finsupp.single_le_iff]
        omega
      by_cases he : e = d + Finsupp.single i 1
      · subst e
        simp only [add_tsub_cancel_right, coeff_monomial, if_true,
          Finsupp.add_apply, Finsupp.single_eq_same]
        ring
      · have hne : e - Finsupp.single i 1 ≠ d := by
          intro he'
          have hx := congrArg (fun a : β →₀ ℕ ↦ a + Finsupp.single i 1) he'
          rw [tsub_add_cancel_of_le hle] at hx
          exact he hx
        simp only [coeff_monomial, if_neg hne, if_neg he, mul_zero]
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]

theorem weightedMap_X [CommRing A] [Algebra ℝ A]
    (g : β × σ → A) (p : β × σ) :
    weightedMap g (X p) = C (g p) * X p.1 := by
  simp only [weightedMap, eval₂Hom_X', C_mul_X_eq_monomial]

theorem weightedMap_directional [CommRing A] [Algebra ℝ A] [DecidableEq β]
    (b : β) (v : σ → ℝ) (g : β × σ → A)
    (hg : ∀ i, g (b, i) = algebraMap ℝ A (v i))
    (P : MvPolynomial (β × σ) ℝ) :
    weightedMap g (directional (VanillaBlockDerivatives.blockDirection b v) P) =
      pderiv b (weightedMap g P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [weightedMap]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
      directional_X, hP, weightedMap_X, pderiv_C, mul_zero]
    have he : weightedMap g
        (C (VanillaBlockDerivatives.blockDirection b v p)) =
        C (g p) * pderiv b (X p.1) := by
      rcases p with ⟨b', i⟩
      by_cases hb : b' = b
      · subst b'
        simp [weightedMap, VanillaBlockDerivatives.blockDirection, hg]
      · simp [weightedMap, VanillaBlockDerivatives.blockDirection, hb, pderiv_X]
    rw [he]
    ring

def contractionWeight (m : ℕ) (v w : σ → ℝ) :
    Block m × σ → MvPolynomial σ ℝ
  | (none, i) => C (v i)
  | (some none, i) => C (w i)
  | (some (some _), i) => X i

def remaining (m : ℕ) : Fin m → Block m := fun b ↦ some (some b)

theorem remaining_injective (m : ℕ) : Function.Injective (remaining m) := by
  intro a b h
  simpa only [remaining, Option.some.injEq] using h


def remainingExponent (m : ℕ) : Block m →₀ ℕ :=
  (BlockCoefficientProjection.allOnes : Fin m →₀ ℕ).mapDomain (remaining m)

@[simp] theorem remainingExponent_none (m : ℕ) : remainingExponent m none = 0 := by
  apply Finsupp.mapDomain_notin_range
  simp [remaining]

@[simp] theorem remainingExponent_some_none (m : ℕ) :
    remainingExponent m (some none) = 0 := by
  apply Finsupp.mapDomain_notin_range
  simp [remaining]

@[simp] theorem remainingExponent_some_some (m : ℕ) (b : Fin m) :
    remainingExponent m (some (some b)) = 1 := by
  exact (Finsupp.mapDomain_apply (remaining_injective m) _ b).trans
    (BlockCoefficientProjection.allOnes_apply b)

theorem remainingExponent_complete (m : ℕ) :
    remainingExponent m + Finsupp.single (some none) 1 + Finsupp.single none 1 =
      (BlockCoefficientProjection.allOnes : Block m →₀ ℕ) := by
  classical
  ext b
  rcases b with _ | b
  · simp
  · rcases b with _ | b <;> simp

theorem coeff_kill_double_pderiv [CommRing A] (m : ℕ)
    (P : MvPolynomial (Block m) A) :
    coeff (BlockCoefficientProjection.allOnes : Fin m →₀ ℕ)
      (killCompl (remaining_injective m) (pderiv (some none) (pderiv none P))) =
      coeff (BlockCoefficientProjection.allOnes : Block m →₀ ℕ) P := by
  rw [coeff_killCompl]
  change coeff (remainingExponent m) (pderiv (some none) (pderiv none P)) = _
  rw [coeff_pderiv_formula, coeff_pderiv_formula, remainingExponent_complete]
  simp

theorem kill_remaining_X [CommRing A] (m : ℕ) (b : Block m) :
    killCompl (R := A) (remaining_injective m) (X b) =
      match b with
      | none => 0
      | some none => 0
      | some (some i) => X i := by
  classical
  rcases b with _ | b
  · simp [killCompl, remaining]
  · rcases b with _ | b
    · simp [killCompl, remaining]
    · change killCompl (remaining_injective m) (X (remaining m b)) = X b
      rw [← rename_X (remaining m) b, killCompl_rename_app]

theorem kill_weightedMap (m : ℕ) (v w : σ → ℝ) (P : BlockPoly m σ) :
    killCompl (remaining_injective m) (weightedMap (contractionWeight m v w) P) =
      collapse m P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [weightedMap, collapse]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
    rw [map_mul, map_mul, hP, weightedMap_X, map_mul, killCompl_C, kill_remaining_X]
    rcases p with ⟨b, i⟩
    rcases b with _ | b
    · simp [collapse, collapseVariable, contractionWeight]
    · rcases b with _ | b
      · simp [collapse, collapseVariable, contractionWeight]
      · simp [collapse, collapseVariable, contractionWeight, mul_comm]

/-- The parameter coefficient preserved by averaging is exactly the projected
second derivative used by the source and vanilla rank calculations. -/
theorem projection_eq_contractDiagonal (m : ℕ) (P : BlockPoly m σ)
    (v w : σ → ℝ) :
    BlockCoefficientProjection.projection (contractionWeight m v w) P =
      contractDiagonal m P v w := by
  classical
  let g := contractionWeight m v w
  have hfirst := weightedMap_directional none v g (fun i ↦ rfl) P
  have hsecond := weightedMap_directional (some none) w g (fun i ↦ rfl)
    (directional (VanillaBlockDerivatives.blockDirection none v) P)
  rw [hfirst] at hsecond
  have hc := coeff_kill_double_pderiv m (weightedMap g P)
  rw [← hsecond, kill_weightedMap] at hc
  exact hc.symm

/-- Top-squarefree coefficient agreement therefore preserves every diagonal
contraction, without a coefficient-size or factor-size assumption. -/
theorem contractDiagonal_eq_of_top_coeff_eq (m : ℕ) (P Q : BlockPoly m σ)
    (h : ∀ e : Block m × σ →₀ ℕ, (∀ p, e p ≤ 1) →
      e.sum (fun _ k ↦ k) = m + 2 → coeff e P = coeff e Q)
    (v w : σ → ℝ) : contractDiagonal m P v w = contractDiagonal m Q v w := by
  rw [← projection_eq_contractDiagonal, ← projection_eq_contractDiagonal]
  apply projection_eq_of_top_coeff_eq
  intro e he hdeg
  apply h e he
  simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc] using hdeg

end HeadComplexity.BlockCoefficientDerivatives
