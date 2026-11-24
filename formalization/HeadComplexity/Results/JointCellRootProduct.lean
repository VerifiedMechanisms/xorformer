import HeadComplexity.Results.JointCellSquaredCauchy
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option linter.style.header false

/-! Exact partial fractions for independently movable real roots. Differentiation
turns the column-dependent residues into squared Cauchy kernels. The separate
two-head theorem handles their row times column numerator weights. -/

namespace HeadComplexity.AxisZeroGluing

open Filter Topology Polynomial
open scoped BigOperators

/-- Distinct root tokens have an exact simple-pole expansion. -/
theorem rootProduct_partial_fractions {c : ℕ} (hc : 0 < c)
    (u : Fin c → ℝ) (hu : Function.Injective u) (x : ℝ)
    (hx : ∀ i, x ≠ u i) :
    (∏ i, (x - u i))⁻¹ =
      ∑ i, Lagrange.nodalWeight Finset.univ u i * (x - u i)⁻¹ := by
  have hs : (Finset.univ : Finset (Fin c)).Nonempty :=
    ⟨⟨0, hc⟩, Finset.mem_univ _⟩
  have hi := Lagrange.eval_interpolate_not_at_node (s := Finset.univ)
    (v := u) (x := x) (1 : Fin c → ℝ) (fun i _ ↦ hx i)
  rw [Lagrange.interpolate_one hu.injOn hs] at hi
  simp only [Polynomial.eval_one, Lagrange.eval_nodal, Pi.one_apply, mul_one] at hi
  have hn : (∏ i, (x - u i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ sub_ne_zero.mpr (hx i))
  apply (mul_left_cancel₀ hn)
  rw [mul_inv_cancel₀ hn]
  exact hi

/-- The derivative of the product inverse is a sum of weighted squared kernels.
This is an identity, not a universal decoder or a head-count improvement. -/
theorem rootProduct_squared_partial_fractions {c : ℕ} (hc : 0 < c)
    (u : Fin c → ℝ) (hu : Function.Injective u) (x : ℝ)
    (hx : ∀ i, x ≠ u i) :
    (Lagrange.nodal Finset.univ u).derivative.eval x /
        (∏ i, (x - u i)) ^ 2 =
      ∑ i, Lagrange.nodalWeight Finset.univ u i / (x - u i) ^ 2 := by
  let p : Polynomial ℝ := Lagrange.nodal Finset.univ u
  have hn : p.eval x ≠ 0 := by
    simpa only [p, Lagrange.eval_nodal] using
      (Finset.prod_ne_zero_iff.mpr (fun i (_ : i ∈ (Finset.univ : Finset (Fin c))) ↦
        sub_ne_zero.mpr (hx i)))
  have hp := (p.hasDerivAt x).inv hn
  have hsum : HasDerivAt
      (fun y : ℝ ↦ ∑ i, Lagrange.nodalWeight Finset.univ u i * (y - u i)⁻¹)
      (∑ i, Lagrange.nodalWeight Finset.univ u i * (-1 / (x - u i) ^ 2)) x := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (((hasDerivAt_id x).sub_const (u i)).inv
      (sub_ne_zero.mpr (hx i))).const_mul _
  have heq : (fun y : ℝ ↦ (p.eval y)⁻¹) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ ∑ i, Lagrange.nodalWeight Finset.univ u i * (y - u i)⁻¹) := by
    have havoid : ∀ᶠ y in 𝓝 x, ∀ i, y ≠ u i := by
      apply Filter.eventually_all.mpr
      intro i
      exact isOpen_compl_singleton.mem_nhds (hx i)
    filter_upwards [havoid] with y hy
    simpa only [p, Lagrange.eval_nodal] using rootProduct_partial_fractions hc u hu y hy
  have hder := hp.unique (hsum.congr_of_eventuallyEq heq)
  simp only [p, Lagrange.eval_nodal, neg_div, mul_neg, mul_one_div,
    Finset.sum_neg_distrib] at hder
  exact neg_injective hder

/-- Every column may choose its roots independently. The derivative product
kernel, multiplied by an arbitrary row coefficient, costs exactly two heads
per root while retaining exact Boolean axes and all prescribed strict signs. -/
theorem rootProduct_preserves_signs {r s c : ℕ} (hc : 0 < c)
    (δ : ℝ) (A D : Fin r → ℝ) (u : Fin s → Fin c → ℝ)
    (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (hD : ∀ i, 1 - δ < D i ∧ D i < 1)
    (hu : ∀ j l, 0 < u j l ∧ u j l < δ)
    (hinj : ∀ j, Function.Injective (u j))
    (σ prior : Fin r → Fin s → ℝ)
    (hstrict : ∀ i j, 0 < σ i j * (prior i j +
      A i * (Lagrange.nodal Finset.univ (u j)).derivative.eval (D i) /
        (∏ l, (D i - u j l)) ^ 2)) :
    ∃ Q : ReverseAxisData r s (2 * c), ∀ i j,
      0 < σ i j * (prior i j + Q.score (localGrid i j)) := by
  apply squaredCauchy_preserves_signs δ (fun _ i ↦ A i) (fun _ i ↦ D i)
    (fun l j ↦ u j l) (fun l j ↦ Lagrange.nodalWeight Finset.univ (u j) l)
    hδ hsize (fun _ ↦ hD) (fun l j ↦ hu j l) σ prior
  intro i j
  have hdim : (2 : ℝ) ≤ ((r + s : ℕ) : ℝ) := by
    have hr : 1 ≤ r := Fin.pos_iff_nonempty.mpr ⟨i⟩
    have hs : 1 ≤ s := Fin.pos_iff_nonempty.mpr ⟨j⟩
    exact_mod_cast (show 2 ≤ r + s by omega)
  have hδsmall := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdim hδ.le) hsize
  have hx : ∀ l, D i ≠ u j l := by
    intro l
    have : u j l < D i := by linarith [(hD i).1, (hu j l).2]
    exact this.ne'
  have heq := rootProduct_squared_partial_fractions hc (u j) (hinj j) (D i) hx
  have hscore : squaredCauchyScore (fun _ i ↦ A i) (fun _ i ↦ D i)
      (fun l j ↦ u j l) (fun l j ↦ Lagrange.nodalWeight Finset.univ (u j) l) i j =
      A i * (Lagrange.nodal Finset.univ (u j)).derivative.eval (D i) /
        (∏ l, (D i - u j l)) ^ 2 := by
    unfold squaredCauchyScore
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum, ← heq]
  rw [hscore]
  exact hstrict i j

end HeadComplexity.AxisZeroGluing
