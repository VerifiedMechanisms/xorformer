import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

set_option linter.style.header false

/-! If an affine-spanning sample has only two coordinate patterns outside
an exceptional set, its coordinate dimension is at most one plus that set. -/

noncomputable section
namespace HeadComplexity.AffineTwoPatternRank
open scoped BigOperators

variable {ι κ : Type*} [Fintype κ]

def affineEval (v : ℝ × (κ → ℝ)) (x : κ → ℝ) : ℝ :=
  v.1 + ∑ i, v.2 i * x i

def testMap (points : ι → κ → ℝ) (E : Finset ι) (p q : κ → ℝ) :
    (ℝ × (κ → ℝ)) →ₗ[ℝ] (ℝ × ℝ × ({j // j ∈ E} → ℝ)) where
  toFun v := (affineEval v p, affineEval v q, fun e => affineEval v (points e))
  map_add' := by
    intro a b
    ext <;> simp [affineEval, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro c a
    ext <;> simp [affineEval, mul_add, mul_assoc, Finset.mul_sum]

/-- The exceptional samples and the two common patterns determine every affine
functional, so there cannot be more coordinate degrees of freedom. -/
theorem card_le_of_two_patterns (points : ι → κ → ℝ) (E : Finset ι) (p q : κ → ℝ)
    (hspan : ∀ v : ℝ × (κ → ℝ), (∀ j, affineEval v (points j) = 0) → v = 0)
    (hpatterns : ∀ j, j ∉ E → points j = p ∨ points j = q) :
    Fintype.card κ ≤ E.card + 1 := by
  classical
  let L := testMap points E p q
  have hzero : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    apply hspan v
    intro j
    by_cases hj : j ∈ E
    · have he := congrArg (fun z : ℝ × ℝ × ({j // j ∈ E} → ℝ) => z.2.2 ⟨j, hj⟩) hv
      simpa [L, testMap] using he
    · rcases hpatterns j hj with hp | hq
      · rw [hp]
        have he := congrArg (fun z : ℝ × ℝ × ({j // j ∈ E} → ℝ) => z.1) hv
        simpa [L, testMap] using he
      · rw [hq]
        have he := congrArg (fun z : ℝ × ℝ × ({j // j ∈ E} → ℝ) => z.2.1) hv
        simpa [L, testMap] using he
  have hinj : Function.Injective L := by
    intro a b hab
    have hz : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hzero _ hz)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
    Fintype.card_coe] at hdim
  omega

end HeadComplexity.AffineTwoPatternRank
