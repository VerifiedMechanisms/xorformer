import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-! Fixed-direction reciprocal decoders with finitely many input levels admit
polynomial reparameterizations of degree equal to the number of levels, rather
than the number of heads. This is the algebraic input to a separate sign-count
argument. No sign-counting theorem or new bound on W is asserted here. -/

namespace HeadComplexity
namespace LargeDomain

open scoped BigOperators

/-- Cancel one selected denominator against the complete product of input
levels. Repeated levels are harmless and do not require injectivity. -/
theorem reciprocal_eq_level_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (level : ι → ℝ) (a b : ℝ) (i : ι)
    (hden : ∀ j, b + level j ≠ 0) :
    a / (b + level i) =
      (a / ∏ j, (b + level j)) * ∏ j ∈ Finset.univ.erase i, (b + level j) := by
  have hp : (∏ j, (b + level j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
    intro j _
    exact hden j)
  symm
  apply (eq_div_iff (hden i)).mpr
  rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact div_mul_cancel₀ _ hp

/-- One offset and one rescaled numerator per head, plus a score bias. -/
abbrev FiniteLevelVariables (H : ℕ) := Option (Fin H × Bool)

noncomputable def finiteLevelScorePolynomial {α : Type*} {H L : ℕ}
    (level : Fin H → Fin L → ℝ) (query : Fin H → α → Fin L) (x : α) :
    MvPolynomial (FiniteLevelVariables H) ℝ :=
  MvPolynomial.X none + ∑ h : Fin H,
    MvPolynomial.X (some (h, true)) *
      ∏ i ∈ Finset.univ.erase (query h x),
        (MvPolynomial.X (some (h, false)) + MvPolynomial.C (level h i))

/-- The degree bound is L, even if the number of heads is much larger. -/
theorem finiteLevelScorePolynomial_totalDegree_le {α : Type*} {H L : ℕ}
    (level : Fin H → Fin L → ℝ) (query : Fin H → α → Fin L) (x : α)
    (hL : 1 ≤ L) :
    (finiteLevelScorePolynomial level query x).totalDegree ≤ L := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simpa using hL
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro h _
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hp : (∏ i ∈ Finset.univ.erase (query h x),
        (MvPolynomial.X (some (h, false)) + MvPolynomial.C (level h i) :
          MvPolynomial (FiniteLevelVariables H) ℝ)).totalDegree ≤ L - 1 := by
      apply (MvPolynomial.totalDegree_finsetProd _ _).trans
      calc
        (∑ i ∈ Finset.univ.erase (query h x),
            (MvPolynomial.X (some (h, false)) + MvPolynomial.C (level h i) :
              MvPolynomial (FiniteLevelVariables H) ℝ).totalDegree) ≤
            ∑ _i ∈ Finset.univ.erase (query h x), 1 := by
          apply Finset.sum_le_sum
          intro i _
          exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
        _ = L - 1 := by simp
    simpa using (Nat.add_le_add_left hp 1).trans (by omega)

noncomputable def finiteLevelParameters {H L : ℕ}
    (level : Fin H → Fin L → ℝ) (a b : Fin H → ℝ) (bias : ℝ) :
    FiniteLevelVariables H → ℝ
  | none => bias
  | some (h, false) => b h
  | some (h, true) => a h / ∏ i, (b h + level h i)

/-- Every reciprocal score with fixed level maps is an evaluation of the
polynomial family. Positivity is stronger than the nonzero premise used here. -/
theorem finiteLevelScorePolynomial_eval {α : Type*} {H L : ℕ}
    (level : Fin H → Fin L → ℝ) (query : Fin H → α → Fin L)
    (a b : Fin H → ℝ) (bias : ℝ)
    (hden : ∀ h i, b h + level h i ≠ 0) (x : α) :
    MvPolynomial.eval (finiteLevelParameters level a b bias)
      (finiteLevelScorePolynomial level query x) =
      bias + ∑ h, a h / (b h + level h (query h x)) := by
  simp only [finiteLevelScorePolynomial, MvPolynomial.eval_add,
    MvPolynomial.eval_X, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_prod, MvPolynomial.eval_C, finiteLevelParameters]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  exact (reciprocal_eq_level_product (level h) (a h) (b h) (query h x) (hden h)).symm

end LargeDomain
end HeadComplexity
