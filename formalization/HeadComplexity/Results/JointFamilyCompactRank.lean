import HeadComplexity.Results.CubeStarTransfer
import Mathlib.Topology.Instances.Matrix

set_option linter.style.header false

/-!
# A fixed nonsingular compact dictionary misses a strict orthant

This is a local obstruction for a fixed dictionary at a regular center.
Directions tuned toward a singular center as the allowed pole interval
shrinks are outside its hypotheses.
-/

namespace HeadComplexity.AxisZeroGluing

open Matrix Filter
open scoped BigOperators

/-- A strict signed dual vector excludes its own strict orthant from a
linear feature span. Coefficients may be arbitrarily large. -/
theorem jointFamily_dual_excludes_orthant {X I : Type*}
    [Fintype X] [Nonempty X] [Fintype I]
    (A : Matrix X I ℝ) (z : X → ℝ) (table : X → Bool)
    (hz : ∀ x, 0 < outputSign (table x) * z x)
    (hann : A.transpose *ᵥ z = 0) :
    ¬ ∃ a : I → ℝ, ∀ x, 0 < outputSign (table x) * (A *ᵥ a) x := by
  classical
  rintro ⟨a, ha⟩
  have hpos : 0 < ∑ x, z x * (A *ᵥ a) x := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro x _
    have hprod := mul_pos (hz x) (ha x)
    cases ht : table x <;> simp [outputSign, ht] at hprod ⊢ <;> nlinarith
  have hzero : (∑ x, z x * (A *ᵥ a) x) = 0 := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congrFun hann i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.transpose_apply] at hi
    calc
      (∑ x, z x * (A x i * a i)) = (∑ x, A x i * z x) * a i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hi, zero_mul]
  linarith

/-- Polynomial dual projection, avoiding division even at singular matrices. -/
noncomputable def jointFamilyGramDual {X I : Type*}
    [Fintype X] [Fintype I] [DecidableEq I]
    (A : Matrix X I ℝ) (z : X → ℝ) : X → ℝ :=
  let G := A.transpose * A
  G.det • z - A *ᵥ (G.adjugate *ᵥ (A.transpose *ᵥ z))

theorem jointFamilyGramDual_annihilates {X I : Type*}
    [Fintype X] [Fintype I] [DecidableEq I]
    (A : Matrix X I ℝ) (z : X → ℝ) :
    A.transpose *ᵥ jointFamilyGramDual A z = 0 := by
  unfold jointFamilyGramDual
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

/-- Near a regular fixed feature dictionary, a strict dual obstruction
persists uniformly. Extra fixed correction features may be included among
its columns. This does not apply to dictionaries changing with the radius. -/
theorem jointFamily_compact_regular_dictionary_obstruction
    {P X I : Type*} [TopologicalSpace P]
    [Fintype X] [Nonempty X] [Fintype I] [DecidableEq I]
    (A : P → Matrix X I ℝ) (hA : Continuous A) (p₀ : P)
    (z : X → ℝ) (table : X → Bool)
    (hdet : 0 < ((A p₀).transpose * A p₀).det)
    (hz : ∀ x, 0 < outputSign (table x) * z x)
    (hann : (A p₀).transpose *ᵥ z = 0) :
    ∀ᶠ p in nhds p₀,
      ¬ ∃ a : I → ℝ, ∀ x, 0 < outputSign (table x) * (A p *ᵥ a) x := by
  have hG : Continuous (fun p ↦ (A p).transpose * A p) :=
    hA.matrix_transpose.matrix_mul hA
  have hdual : Continuous (fun p ↦ jointFamilyGramDual (A p) z) := by
    unfold jointFamilyGramDual
    exact (hG.matrix_det.smul continuous_const).sub
      (hA.matrix_mulVec (hG.matrix_adjugate.matrix_mulVec
        (hA.matrix_transpose.matrix_mulVec continuous_const)))
  have hcenter : jointFamilyGramDual (A p₀) z =
      ((A p₀).transpose * A p₀).det • z := by
    simp [jointFamilyGramDual, hann]
  have hev : ∀ᶠ p in nhds p₀, ∀ x,
      0 < outputSign (table x) * jointFamilyGramDual (A p) z x := by
    apply Filter.eventually_all.mpr
    intro x
    have hp : 0 < outputSign (table x) * jointFamilyGramDual (A p₀) z x := by
      rw [hcenter]
      simpa [Pi.smul_apply, smul_eq_mul, mul_left_comm] using mul_pos hdet (hz x)
    exact (((continuous_apply x).comp hdual).const_mul (outputSign (table x))).continuousAt
      (eventually_gt_nhds hp)
  filter_upwards [hev] with p hp
  exact jointFamily_dual_excludes_orthant (A p) (jointFamilyGramDual (A p) z)
    table hp (jointFamilyGramDual_annihilates (A p) z)

end HeadComplexity.AxisZeroGluing
