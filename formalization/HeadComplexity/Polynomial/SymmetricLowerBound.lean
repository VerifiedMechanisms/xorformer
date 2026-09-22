import HeadComplexity.Polynomial.StrictSign
import HeadComplexity.Polynomial.UnivariateSignChanges

set_option linter.style.header false

/-!
# L12 lower bound chain.

Assembling `HStar n (symmetricFn F) ≥ signChanges n F` from:
* `signReprDegLe_of_computableWithHeadsN` (L6): `H` heads → degree-≤H sign rep;
* strictification (here): turn `0 < eval ↔ f` into a strict sign representation;
* symmetrization (here): average over `Equiv.Perm` to a symmetric polynomial;
* univariate reduction (`Polynomial/UnivariateReduction.lean`): a symmetric polynomial of
  total degree `≤ H` on the cube is a univariate polynomial of degree `≤ H` in the
  Hamming weight (no multilinearity is assumed, since any cube polynomial reduces);
* `signChanges_le_natDegree` (`Polynomial/UnivariateSignChanges.lean`): degree ≥ sign changes.

The chain is complete: `signChanges_le_of_computableWithHeadsN`
(`Polynomial/UnivariateReduction.lean`) discharges the lower bound, and together with the
upper bound it yields the unconditional `HStar_symmetricFn` in `Results/SymmetricComplexity.lean`.
-/

namespace HeadComplexity

open MvPolynomial

variable {n : ℕ}

/-! ## Symmetrization (Phase 3a) -/

open scoped BigOperators

/-- Hamming weight is invariant under permuting coordinates. -/
theorem hammingWeight_comp_perm (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    hammingWeight (fun i => x (σ i)) = hammingWeight x := by
  unfold hammingWeight
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp σ (fun j => if x j = true then 1 else 0)

/-- Average over all coordinate permutations. -/
noncomputable def symmetrize (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ σ : Equiv.Perm (Fin n), rename σ P

theorem symmetrize_totalDegree_le {P : MvPolynomial (Fin n) ℝ} {H : ℕ}
    (hP : P.totalDegree ≤ H) : (symmetrize P).totalDegree ≤ H :=
  totalDegree_finsetSum_le (fun _ _ => (totalDegree_rename_le _ _).trans hP)

theorem symmetrize_isSymmetric (P : MvPolynomial (Fin n) ℝ) :
    (symmetrize P).IsSymmetric := by
  intro τ
  unfold symmetrize
  rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => rename (σ : Fin n → Fin n) P)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [rename_rename]
  congr 1

/-- Symmetrization preserves a strict sign representation of a symmetric function. -/
theorem symmetrize_strictSignRep {F : ℕ → Bool} {P : MvPolynomial (Fin n) ℝ}
    (hP : StrictSignRep P (symmetricFn F)) :
    StrictSignRep (symmetrize P) (symmetricFn F) := by
  have key : ∀ (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)),
      symmetricFn F (fun i => x (σ i)) = symmetricFn F x := by
    intro x σ; simp only [symmetricFn]; rw [hammingWeight_comp_perm]
  have hcomp : ∀ (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)),
      cubePoint x ∘ (σ : Fin n → Fin n) = cubePoint (fun i => x (σ i)) := fun x σ => rfl
  intro x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · unfold symmetrize
    rw [map_sum]
    refine Finset.sum_pos (fun σ _ => ?_) Finset.univ_nonempty
    rw [eval_rename, hcomp x σ]
    exact (hP (fun i => x (σ i))).1 ((key x σ).trans hx)
  · unfold symmetrize
    rw [map_sum]
    refine Finset.sum_neg (fun σ _ => ?_) Finset.univ_nonempty
    rw [eval_rename, hcomp x σ]
    exact (hP (fun i => x (σ i))).2 ((key x σ).trans hx)

end HeadComplexity
