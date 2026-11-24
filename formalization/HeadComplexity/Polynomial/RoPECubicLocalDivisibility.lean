import HeadComplexity.Polynomial.RoPECubicIrreducible
import Mathlib.RingTheory.Polynomial.ScaleRoots
import HeadComplexity.Foundation.FiniteFeatureSignLimit
import Mathlib.Topology.Algebra.MvPolynomial
import HeadComplexity.Polynomial.SignLimitProportionality

set_option linter.style.header false

/-!
# Local vanishing implies divisibility by the source cubic

The distinguished variable is the sixth numerator coordinate. A scaled-root
substitution clears its denominator without passing to a fraction field.
-/

namespace HeadComplexity.RoPECubic

open MvPolynomial
open scoped Topology
open Filter

noncomputable def slope : Poly := X 0 * X 1

noncomputable def remainder : Poly := X 2 * (X 3 * X 1 + X 4 * X 0)

/-- Regard the sixth variable as the univariate indeterminate. The other
seventeen variables remain in the coefficient ring. -/
noncomputable def univariate (Q : Poly) : Polynomial Poly :=
  eval₂ (Polynomial.C.comp C)
    (fun i ↦ if i = 5 then Polynomial.X else Polynomial.C (X i)) Q

theorem univariate_eval (Q : Poly) :
    (univariate Q).eval (X 5) = Q := by
  unfold univariate
  rw [← Polynomial.coe_evalRingHom, eval₂_comp_left]
  have hc : (Polynomial.evalRingHom (X 5 : Poly)).comp (Polynomial.C.comp C) = C := by
    ext a
    simp
  rw [hc]
  have hx : (Polynomial.evalRingHom (X 5 : Poly)) ∘
      (fun i : Fin 18 ↦ if i = 5 then Polynomial.X else Polynomial.C (X i)) = X := by
    funext i
    by_cases hi : i = 5 <;> simp [hi]
  rw [hx, eval₂_eta]

/-- The polynomial obtained after substituting the rational zero graph and
clearing a power of its denominator. -/
noncomputable def clearedSubstitution (Q : Poly) : Poly :=
  ((univariate Q).scaleRoots slope).eval (-remainder)

theorem core_dvd_cleared_difference (Q : Poly) :
    core ∣ slope ^ (univariate Q).natDegree * Q - clearedSubstitution Q := by
  have h := Polynomial.sub_dvd_eval_sub (slope * X 5) (-remainder)
    ((univariate Q).scaleRoots slope)
  rw [Polynomial.scaleRoots_eval_mul, univariate_eval] at h
  have hc : slope * X 5 - -remainder = core := by
    dsimp [slope, remainder, core]
    ring
  simpa only [hc, clearedSubstitution] using h

theorem core_dvd_of_clearedSubstitution_eq_zero (Q : Poly)
    (hQ : clearedSubstitution Q = 0) : core ∣ Q := by
  have h := core_dvd_cleared_difference Q
  rw [hQ, sub_zero] at h
  exact core_dvd_of_cleared_power_dvd Q (univariate Q).natDegree h

theorem univariate_eval₂ (Q : Poly) (x : Fin 18 → ℝ) (z : ℝ) :
    Polynomial.eval₂ (eval x) z (univariate Q) =
      eval (Function.update x 5 z) Q := by
  unfold univariate
  rw [← Polynomial.coe_eval₂RingHom, eval₂_comp_left]
  have hc : (Polynomial.eval₂RingHom (eval x) z).comp (Polynomial.C.comp C) =
      RingHom.id ℝ := by
    ext a
    simp
  rw [hc, eval₂_id]
  have hg : (Polynomial.eval₂RingHom (eval x) z) ∘
      (fun i : Fin 18 ↦ if i = 5 then Polynomial.X else Polynomial.C (X i)) =
      Function.update x 5 z := by
    funext i
    by_cases hi : i = 5 <;> simp [hi, Function.update]
  rw [hg]

theorem eval_clearedSubstitution (Q : Poly) (x : Fin 18 → ℝ)
    (hx : eval x slope ≠ 0) :
    eval x (clearedSubstitution Q) =
      (eval x slope) ^ (univariate Q).natDegree *
        eval (Function.update x 5 (-eval x remainder / eval x slope)) Q := by
  unfold clearedSubstitution
  rw [← Polynomial.eval₂_at_apply, map_neg]
  have he : -eval x remainder = eval x slope * (-eval x remainder / eval x slope) := by
    field_simp
  conv_lhs => rw [he]
  rw [Polynomial.scaleRoots_eval₂_mul, univariate_eval₂]

/-- Vanishing on an open box of the rational graph implies divisibility.
The box hypothesis is stated as an arbitrary product of infinite sets. -/
theorem core_dvd_of_rational_graph_vanishes (Q : Poly) (s : Fin 18 → Set ℝ)
    (hs : ∀ i, (s i).Infinite)
    (hden : ∀ x ∈ Set.pi Set.univ s, eval x slope ≠ 0)
    (hQ : ∀ x ∈ Set.pi Set.univ s,
      eval (Function.update x 5 (-eval x remainder / eval x slope)) Q = 0) :
    core ∣ Q := by
  apply core_dvd_of_clearedSubstitution_eq_zero
  apply zero_of_vanishes_on_box _ s hs
  intro x hx
  rw [eval_clearedSubstitution Q x (hden x hx), hQ x hx, mul_zero]

theorem eval_core_update (x : Fin 18 → ℝ) (z : ℝ) :
    eval (Function.update x 5 z) core =
      eval x core + eval x slope * (z - x 5) := by
  simp [core, slope, Function.update]
  ring

/-- Weak sign agreement on an open neighborhood forces vanishing at every
source zero where the distinguished-variable coefficient is nonzero. -/
theorem eval_eq_zero_of_weak_sign_on_open (Q : Poly)
    (Ω : Set (Fin 18 → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y core → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y core < 0 → eval y Q ≤ 0)
    (x : Fin 18 → ℝ) (hx : x ∈ Ω)
    (hzero : eval x core = 0) (hslope : eval x slope ≠ 0) : eval x Q = 0 := by
  let t : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  let path : ℝ → Fin 18 → ℝ := fun r ↦ Function.update x 5 (x 5 + r / eval x slope)
  have hp (r : ℝ) : eval (path r) core = r := by
    dsimp [path]
    rw [eval_core_update, hzero, zero_add]
    field_simp
    ring
  have hpathlim : Tendsto path (𝓝 0) (𝓝 x) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) (𝓝 0) (𝓝 x)).update 5
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x 5) (𝓝 0) (𝓝 (x 5))).add
        (tendsto_id.div_const (eval x slope)))
    simpa only [path, id_eq, zero_div, add_zero, Function.update_eq_self] using h
  have hplus := hpathlim.comp ht
  have htneg : Tendsto (fun m ↦ -t m) atTop (𝓝 0) := by simpa using ht.neg
  have hminus := hpathlim.comp htneg
  have hQplus := (Q.continuous_eval.continuousAt.tendsto).comp hplus
  have hQminus := (Q.continuous_eval.continuousAt.tendsto).comp hminus
  have hnonneg : 0 ≤ eval x Q := by
    apply ge_of_tendsto hQplus
    exact (hplus.eventually (hΩ.mem_nhds hx)).mono fun m hm ↦
      hpos _ hm (by simpa only [Function.comp_apply, hp] using htpos m)
  have hnonpos : eval x Q ≤ 0 := by
    apply le_of_tendsto hQminus
    exact (hminus.eventually (hΩ.mem_nhds hx)).mono fun m hm ↦
      hneg _ hm (by simpa only [Function.comp_apply, hp] using neg_neg_of_pos (htpos m))
  exact le_antisymm hnonpos hnonneg

noncomputable def zeroGraph (x : Fin 18 → ℝ) : Fin 18 → ℝ :=
  Function.update x 5 (-eval x remainder / eval x slope)

theorem eval_core_eq (x : Fin 18 → ℝ) :
    eval x core = eval x remainder + eval x slope * x 5 := by
  simp [core, remainder, slope]
  ring

theorem zeroGraph_eq_self (x : Fin 18 → ℝ)
    (hzero : eval x core = 0) (hslope : eval x slope ≠ 0) : zeroGraph x = x := by
  have he : -eval x remainder / eval x slope = x 5 := by
    apply (div_eq_iff hslope).mpr
    rw [eval_core_eq] at hzero
    nlinarith
  simp only [zeroGraph, he, Function.update_eq_self]

theorem eval_slope_zeroGraph (x : Fin 18 → ℝ) :
    eval (zeroGraph x) slope = eval x slope := by
  simp [zeroGraph, slope, Function.update]

theorem eval_core_zeroGraph (x : Fin 18 → ℝ) (hx : eval x slope ≠ 0) :
    eval (zeroGraph x) core = 0 := by
  rw [zeroGraph, eval_core_update, eval_core_eq]
  field_simp
  ring

theorem continuousAt_zeroGraph (x : Fin 18 → ℝ) (hx : eval x slope ≠ 0) :
    ContinuousAt zeroGraph x := by
  exact continuousAt_id.update 5
    ((remainder.continuous_eval.continuousAt.neg).div
      slope.continuous_eval.continuousAt hx)

/-- A weak sign representative on any open neighborhood of a regular source
zero is divisible by the source cubic. -/
theorem core_dvd_of_weak_sign_on_open (Q : Poly)
    (Ω : Set (Fin 18 → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y core → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y core < 0 → eval y Q ≤ 0)
    (x : Fin 18 → ℝ) (hx : x ∈ Ω)
    (hzero : eval x core = 0) (hslope : eval x slope ≠ 0) : core ∣ Q := by
  have hgraph : ∀ᶠ y in 𝓝 x, zeroGraph y ∈ Ω := by
    apply (continuousAt_zeroGraph x hslope).tendsto.eventually
    rw [zeroGraph_eq_self x hzero hslope]
    exact hΩ.mem_nhds hx
  have hden : ∀ᶠ y in 𝓝 x, eval y slope ≠ 0 :=
    slope.continuous_eval.continuousAt.eventually_ne hslope
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (hgraph.and hden)
  apply core_dvd_of_clearedSubstitution_eq_zero
  apply SignLimitProportionality.eq_zero_of_eval_zero_on_open _ U hUopen ⟨x, hxU⟩
  intro y hy
  obtain ⟨hyΩ, hyden⟩ := hUsub hy
  rw [eval_clearedSubstitution Q y hyden]
  have hQzero := eval_eq_zero_of_weak_sign_on_open Q Ω hΩ hpos hneg
    (zeroGraph y) hyΩ (eval_core_zeroGraph y hyden)
    (by simpa only [eval_slope_zeroGraph] using hyden)
  change _ * eval (zeroGraph y) Q = 0
  rw [hQzero, mul_zero]

end HeadComplexity.RoPECubic
