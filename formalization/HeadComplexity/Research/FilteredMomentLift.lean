import HeadComplexity.Research.RadialMomentTransfer
import HeadComplexity.Research.SimplexPolynomialInterpolation

set_option linter.style.header false

/-!
A finite projection-moment criterion for exact ghosts, and a finite-order lift
onto a fixed translated integer simplex.  No regularity assumption is imposed
on the scalar kernel, and no relative-margin conclusion is asserted.
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

section SimplexLift

open MvPolynomial SimplexPolynomialInterpolation

variable {σ : Type*} [Fintype σ]

def gridNode (v : σ → ℝ) {r : ℕ} (β : Grid (σ := σ) r) : σ → ℝ :=
  fun i => v i + (β.val i : ℝ)

def gridResidue (r : ℕ) (v : σ → ℝ) (a : ι → ℝ) (w : ι → σ → ℝ)
    (β : Grid (σ := σ) r) : ℝ :=
  ∑ h, a h * eval (fun i => w h i - v i) (cardinalPoly r β)

/-- The grid correction matches every ordinary polynomial moment of degree at most `r`.
No Boolean-projection hypothesis is required for this identity. -/
theorem gridResidue_matches_polynomial (r : ℕ) (v : σ → ℝ)
    (a : ι → ℝ) (w : ι → σ → ℝ) (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ r) :
    (∑ h, a h * eval (w h) p) =
      ∑ β : Grid (σ := σ) r, gridResidue r v a w β * eval (gridNode v β) p := by
  classical
  calc
    (∑ h, a h * eval (w h) p) = ∑ h, ∑ β : Grid (σ := σ) r,
        a h * (eval (gridNode v β) p *
          eval (fun i => w h i - v i) (cardinalPoly r β)) := by
      apply sum_congr rfl
      intro h _
      rw [translated_interpolation_eval r p hp v (w h), mul_sum]
      rfl
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro β _
      unfold gridResidue
      rw [sum_mul]
      apply sum_congr rfl
      intro h _
      ring

def booleanProjection (w : σ → ℝ) (x : σ → Bool) : ℝ :=
  ∑ i, if x i then w i else 0

def projectionPoly (x : σ → Bool) : MvPolynomial σ ℝ :=
  ∑ i, if x i then X i else 0

theorem eval_projectionPoly (w : σ → ℝ) (x : σ → Bool) :
    eval w (projectionPoly x) = booleanProjection w x := by
  simp [projectionPoly, booleanProjection, apply_ite]

theorem totalDegree_projectionPoly_le (x : σ → Bool) :
    (projectionPoly x).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  split <;> simp

theorem gridNode_projection_range (r : ℕ) (v : σ → ℝ)
    (x : σ → Bool) (β : Grid (σ := σ) r) :
    ∃ j : Fin (r + 1), booleanProjection (gridNode v β) x =
      booleanProjection v x + (j : ℕ) := by
  let k : ℕ := ∑ i, if x i then β.val i else 0
  have hk : k ≤ r := by
    apply le_trans (show k ≤ size β.val from ?_) β.property
    apply sum_le_sum
    intro i _
    split <;> omega
  refine ⟨⟨k, by omega⟩, ?_⟩
  change booleanProjection (gridNode v β) x = booleanProjection v x + (k : ℝ)
  simp only [booleanProjection, gridNode, k, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split <;> simp_all

theorem gridResidue_matches_projection_moment (r : ℕ) (v : σ → ℝ)
    (a : ι → ℝ) (w : ι → σ → ℝ) (x : σ → Bool) (k : ℕ) (hk : k ≤ r) :
    moment a (fun h => booleanProjection (w h) x) k =
      moment (gridResidue r v a w) (fun β => booleanProjection (gridNode v β) x) k := by
  have hd' : k * (projectionPoly x).totalDegree ≤ k := by
    simpa using Nat.mul_le_mul_left k (totalDegree_projectionPoly_le x)
  have hd : (projectionPoly x ^ k).totalDegree ≤ r :=
    (totalDegree_pow _ _).trans (hd'.trans hk)
  simpa only [moment, map_pow, eval_projectionPoly] using
    gridResidue_matches_polynomial r v a w (projectionPoly x ^ k) hd

/-- A cloud whose Boolean projection moments vanish through `r` admits an exact
ghost on the fixed positive grid.  The same residues also match all ordinary
moments through `r`, by `gridResidue_matches_polynomial`. -/
theorem gridResidue_is_exact_ghost (r : ℕ) (v : σ → ℝ)
    (a : ι → ℝ) (w : ι → σ → ℝ) (x : σ → Bool)
    (hz : ∀ k ≤ r, moment a (fun h => booleanProjection (w h) x) k = 0)
    (F : ℝ → ℝ) :
    ∑ β : Grid (σ := σ) r,
      gridResidue r v a w β * F (booleanProjection (gridNode v β) x) = 0 := by
  apply sum_kernel_eq_zero_of_integer_projection _ _ r (booleanProjection v x)
  · exact gridNode_projection_range r v x
  · intro k hk
    rw [← gridResidue_matches_projection_moment r v a w x k hk]
    exact hz k hk

theorem gridNode_positive (r : ℕ) (v : σ → ℝ) (hv : ∀ i, 0 < v i)
    (β : Grid (σ := σ) r) (i : σ) : 0 < gridNode v β i := by
  exact add_pos_of_pos_of_nonneg (hv i) (Nat.cast_nonneg _)

end SimplexLift

end HeadComplexity.FilteredMomentLift
