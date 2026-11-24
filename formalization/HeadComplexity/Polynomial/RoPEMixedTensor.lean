import HeadComplexity.Polynomial.BoundedCoefficientLimit
import Mathlib.Data.Matrix.Basic

set_option linter.style.header false

/-!
# The mixed cubic tensor of an eighteen-variable polynomial

The tensor retains one group coordinate from each six-coordinate block.
-/

namespace HeadComplexity.RoPEMixedTensor

open MvPolynomial
open scoped Topology
open Filter

def blockIndex (b : Fin 3) (i : Fin 6) : Fin 18 := ⟨6 * b.val + i.val, by omega⟩

noncomputable def mixedExponent (i j k : Fin 6) : Fin 18 →₀ ℕ :=
  Finsupp.single (blockIndex 0 i) 1 + Finsupp.single (blockIndex 1 j) 1 +
    Finsupp.single (blockIndex 2 k) 1

theorem mixedExponent_degree (i j k : Fin 6) :
    Finsupp.degree (mixedExponent i j k) = 3 := by
  simp [mixedExponent, map_add, Finsupp.degree_single]

theorem mixedExponent_squarefree (i j k : Fin 6) (a : Fin 18) :
    mixedExponent i j k a ≤ 1 := by
  simp only [mixedExponent, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all [blockIndex, Fin.ext_iff] <;> omega

noncomputable def mixedTensor (P : MvPolynomial (Fin 18) ℝ) :
    Fin 6 → Matrix (Fin 6) (Fin 6) ℝ := fun i j k ↦ P.coeff (mixedExponent i j k)

theorem mixedTensor_smul (a : ℝ) (P : MvPolynomial (Fin 18) ℝ) :
    mixedTensor (a • P) = a • mixedTensor P := by
  ext i j k
  simp [mixedTensor, coeff_smul]

theorem mixedTensor_C_mul (a : ℝ) (P : MvPolynomial (Fin 18) ℝ) :
    mixedTensor (C a * P) = a • mixedTensor P := by
  ext i j k
  simp [mixedTensor, coeff_C_mul]

theorem mixedTensor_reconstruct_continuous :
    Continuous (fun a : BoundedCoefficientLimit.Exponent 18 3 → ℝ ↦
      mixedTensor (BoundedCoefficientLimit.reconstruct a)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  change Continuous (fun a ↦ (BoundedCoefficientLimit.reconstruct a).coeff
    (mixedExponent i j k))
  have he := mixedExponent_degree i j k
  simp only [BoundedCoefficientLimit.coeff_reconstruct (e := ⟨mixedExponent i j k, he.le⟩)]
  exact continuous_apply _

theorem tendsto_mixedTensor_of_coefficients
    (P : ℕ → MvPolynomial (Fin 18) ℝ) (Q : MvPolynomial (Fin 18) ℝ)
    (h : ∀ e, Tendsto (fun k ↦ (P k).coeff e) atTop (𝓝 (Q.coeff e))) :
    Tendsto (fun k ↦ mixedTensor (P k)) atTop (𝓝 (mixedTensor Q)) := by
  exact tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦
    tendsto_pi_nhds.mpr fun k ↦ h (mixedExponent i j k)

end HeadComplexity.RoPEMixedTensor
