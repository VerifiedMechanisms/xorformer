import HeadComplexity.Research.RadialMomentTransfer

set_option linter.style.header false

/-!
A finite projection-moment criterion for exact ghosts.  The general positive
simplex-grid lifting theorem is currently a written proof.  This module checks
the step which turns finitely many matched moments into an identity for every
scalar kernel, without a regularity assumption on that kernel.
-/

noncomputable section
namespace HeadComplexity.FilteredMomentLift

open Finset
open HeadComplexity.RadialMomentTransfer

variable {ι : Type*} [Fintype ι]

/-- If a signed cloud has at most `r+1` prescribed distinct projection values,
vanishing moments through `r` annihilate every function of that projection. -/
theorem sum_kernel_eq_zero_of_finite_moments
    (a C : ι → ℝ) (r : ℕ) (nodes : Fin (r + 1) → ℝ)
    (hinj : Function.Injective nodes)
    (hC : ∀ h, ∃ j, C h = nodes j)
    (hz : ∀ k ≤ r, moment a C k = 0) (F : ℝ → ℝ) :
    ∑ h, a h * F (C h) = 0 := by
  classical
  let P : Polynomial ℝ := Lagrange.interpolate univ nodes (fun j => F (nodes j))
  have hi : Set.InjOn nodes (univ : Finset (Fin (r + 1))) :=
    fun _ _ _ _ h => hinj h
  have hd : P.degree < (r + 1 : ℕ) := by
    simpa [P] using Lagrange.degree_interpolate_lt (fun j => F (nodes j)) hi
  have hp : ∀ h, P.eval (C h) = F (C h) := by
    intro h
    obtain ⟨j, hj⟩ := hC h
    rw [hj]
    exact Lagrange.eval_interpolate_at_node (fun j => F (nodes j)) hi (mem_univ j)
  simp_rw [← hp, Polynomial.eval_eq_sum, Polynomial.sum_def, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro k hk
  have hk0 : P.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  have hP0 : P ≠ 0 := by
    intro hP
    simp [hP] at hk0
  have hkn : k ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero hk0
  have hnd : P.natDegree < r + 1 :=
    (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hd
  have hkr : k ≤ r := by omega
  calc
    (∑ h, a h * (P.coeff k * C h ^ k)) = P.coeff k * moment a C k := by
      unfold moment
      rw [mul_sum]
      apply sum_congr rfl
      intro h _
      ring
    _ = 0 := by rw [hz k hkr, mul_zero]

/-- Integer projection values in a translate of `{0,...,r}` meet the preceding
criterion.  Multiplicities and zero residues are allowed. -/
theorem sum_kernel_eq_zero_of_integer_projection
    (a C : ι → ℝ) (r : ℕ) (base : ℝ)
    (hC : ∀ h, ∃ j : Fin (r + 1), C h = base + (j : ℕ))
    (hz : ∀ k ≤ r, moment a C k = 0) (F : ℝ → ℝ) :
    ∑ h, a h * F (C h) = 0 := by
  apply sum_kernel_eq_zero_of_finite_moments a C r (fun j => base + (j : ℕ))
  · intro i j hij
    have hij' : (i.val : ℝ) = (j.val : ℝ) := add_left_cancel hij
    exact Fin.ext (Nat.cast_injective hij')
  · exact hC
  · exact hz

end HeadComplexity.FilteredMomentLift
