import HeadComplexity.Polynomial.RoPECubicLocalDivisibility

set_option linter.style.header false

/-!
# Local sign rigidity for an irreducible source linear in one coordinate

This dimension-independent version of the cubic graph argument separates the
general analytic/divisibility mechanism from the particular source polynomial.
-/

namespace HeadComplexity.LinearSourceDivisibility

open MvPolynomial
open scoped Topology
open Filter

abbrev Poly (σ : Type*) := MvPolynomial σ ℝ

variable {σ : Type*} [DecidableEq σ]

noncomputable def source (v : σ) (a b : Poly σ) : Poly σ := a * X v + b

noncomputable def univariate (v : σ) (Q : Poly σ) : Polynomial (Poly σ) :=
  eval₂ (Polynomial.C.comp C)
    (fun i ↦ if i = v then Polynomial.X else Polynomial.C (X i)) Q

theorem univariate_eval (v : σ) (Q : Poly σ) :
    (univariate v Q).eval (X v) = Q := by
  unfold univariate
  rw [← Polynomial.coe_evalRingHom, eval₂_comp_left]
  have hc : (Polynomial.evalRingHom (X v : Poly σ)).comp (Polynomial.C.comp C) = C := by
    ext x
    simp
  rw [hc]
  have hx : (Polynomial.evalRingHom (X v : Poly σ)) ∘
      (fun i : σ ↦ if i = v then Polynomial.X else Polynomial.C (X i)) = X := by
    funext i
    by_cases hi : i = v <;> simp [hi]
  rw [hx, eval₂_eta]

noncomputable def clearedSubstitution (v : σ) (a b Q : Poly σ) : Poly σ :=
  ((univariate v Q).scaleRoots a).eval (-b)

theorem source_dvd_cleared_difference (v : σ) (a b Q : Poly σ) :
    source v a b ∣ a ^ (univariate v Q).natDegree * Q - clearedSubstitution v a b Q := by
  have h := Polynomial.sub_dvd_eval_sub (a * X v) (-b)
    ((univariate v Q).scaleRoots a)
  rw [Polynomial.scaleRoots_eval_mul, univariate_eval] at h
  simpa only [sub_neg_eq_add, source, clearedSubstitution] using h

theorem source_dvd_of_clearedSubstitution_eq_zero (v : σ) (a b Q : Poly σ)
    (hp : Prime (source v a b)) (hno : ¬ source v a b ∣ a)
    (hQ : clearedSubstitution v a b Q = 0) : source v a b ∣ Q := by
  have h := source_dvd_cleared_difference v a b Q
  rw [hQ, sub_zero] at h
  exact (hp.dvd_mul.mp h).resolve_left (fun hk ↦ hno (hp.dvd_of_dvd_pow hk))

theorem univariate_eval₂ (v : σ) (Q : Poly σ) (x : σ → ℝ) (z : ℝ) :
    Polynomial.eval₂ (eval x) z (univariate v Q) = eval (Function.update x v z) Q := by
  unfold univariate
  rw [← Polynomial.coe_eval₂RingHom, eval₂_comp_left]
  have hc : (Polynomial.eval₂RingHom (eval x) z).comp (Polynomial.C.comp C) =
      RingHom.id ℝ := by
    ext t
    simp
  rw [hc, eval₂_id]
  have hg : (Polynomial.eval₂RingHom (eval x) z) ∘
      (fun i : σ ↦ if i = v then Polynomial.X else Polynomial.C (X i)) =
      Function.update x v z := by
    funext i
    by_cases hi : i = v <;> simp [hi, Function.update]
  rw [hg]

theorem eval_clearedSubstitution (v : σ) (a b Q : Poly σ) (x : σ → ℝ)
    (hx : eval x a ≠ 0) :
    eval x (clearedSubstitution v a b Q) =
      (eval x a) ^ (univariate v Q).natDegree *
        eval (Function.update x v (-eval x b / eval x a)) Q := by
  unfold clearedSubstitution
  rw [← Polynomial.eval₂_at_apply, map_neg]
  have he : -eval x b = eval x a * (-eval x b / eval x a) := by field_simp
  conv_lhs => rw [he]
  rw [Polynomial.scaleRoots_eval₂_mul, univariate_eval₂]

theorem eval_update_of_not_mem_vars (v : σ) (p : Poly σ) (hp : v ∉ p.vars)
    (x : σ → ℝ) (z : ℝ) : eval (Function.update x v z) p = eval x p := by
  apply eval₂Hom_congr' rfl _ rfl
  intro i hi _
  have hiv : i ≠ v := by intro he; subst i; exact hp hi
  exact Function.update_of_ne hiv z x

theorem eval_source_update (v : σ) (a b : Poly σ)
    (ha : v ∉ a.vars) (hb : v ∉ b.vars) (x : σ → ℝ) (z : ℝ) :
    eval (Function.update x v z) (source v a b) =
      eval x (source v a b) + eval x a * (z - x v) := by
  simp only [source, map_add, map_mul, eval_X, Function.update_self,
    eval_update_of_not_mem_vars v a ha, eval_update_of_not_mem_vars v b hb]
  ring

omit [DecidableEq σ] in
theorem eval_eq_zero_of_weak_sign_on_open (v : σ) (a b Q : Poly σ)
    (ha : v ∉ a.vars) (hb : v ∉ b.vars)
    (Ω : Set (σ → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y (source v a b) → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y (source v a b) < 0 → eval y Q ≤ 0)
    (x : σ → ℝ) (hx : x ∈ Ω)
    (hzero : eval x (source v a b) = 0) (hslope : eval x a ≠ 0) : eval x Q = 0 := by
  classical
  let t : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (m : ℕ) : 0 < t m := by dsimp [t]; positivity
  let path : ℝ → σ → ℝ := fun r ↦ Function.update x v (x v + r / eval x a)
  have hp (r : ℝ) : eval (path r) (source v a b) = r := by
    dsimp [path]
    rw [eval_source_update v a b ha hb, hzero, zero_add]
    field_simp
    ring
  have hpathlim : Tendsto path (𝓝 0) (𝓝 x) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) (𝓝 0) (𝓝 x)).update v
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x v) (𝓝 0) (𝓝 (x v))).add
        (tendsto_id.div_const (eval x a)))
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

noncomputable def zeroGraph (v : σ) (a b : Poly σ) (x : σ → ℝ) : σ → ℝ :=
  Function.update x v (-eval x b / eval x a)

theorem zeroGraph_eq_self (v : σ) (a b : Poly σ) (x : σ → ℝ)
    (hzero : eval x (source v a b) = 0) (hslope : eval x a ≠ 0) :
    zeroGraph v a b x = x := by
  have he : -eval x b / eval x a = x v := by
    apply (div_eq_iff hslope).mpr
    simp only [source, map_add, map_mul, eval_X] at hzero
    nlinarith
  simp only [zeroGraph, he, Function.update_eq_self]

theorem eval_source_zeroGraph (v : σ) (a b : Poly σ)
    (ha : v ∉ a.vars) (hb : v ∉ b.vars) (x : σ → ℝ) (hx : eval x a ≠ 0) :
    eval (zeroGraph v a b x) (source v a b) = 0 := by
  rw [zeroGraph, eval_source_update v a b ha hb]
  simp only [source, map_add, map_mul, eval_X]
  field_simp
  ring

theorem continuousAt_zeroGraph (v : σ) (a b : Poly σ) (x : σ → ℝ)
    (hx : eval x a ≠ 0) : ContinuousAt (zeroGraph v a b) x := by
  exact continuousAt_id.update v
    ((b.continuous_eval.continuousAt.neg).div a.continuous_eval.continuousAt hx)

omit [DecidableEq σ] in
/-- Weak signs on an open neighborhood of a regular source zero force exact
polynomial divisibility. No bound on the degree of the representative is needed. -/
theorem source_dvd_of_weak_sign_on_open [Finite σ] (v : σ) (a b Q : Poly σ)
    (ha : v ∉ a.vars) (hb : v ∉ b.vars)
    (hp : Prime (source v a b)) (hno : ¬ source v a b ∣ a)
    (Ω : Set (σ → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y (source v a b) → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y (source v a b) < 0 → eval y Q ≤ 0)
    (x : σ → ℝ) (hx : x ∈ Ω)
    (hzero : eval x (source v a b) = 0) (hslope : eval x a ≠ 0) :
    source v a b ∣ Q := by
  classical
  have hgraph : ∀ᶠ y in 𝓝 x, zeroGraph v a b y ∈ Ω := by
    apply (continuousAt_zeroGraph v a b x hslope).tendsto.eventually
    rw [zeroGraph_eq_self v a b x hzero hslope]
    exact hΩ.mem_nhds hx
  have hden : ∀ᶠ y in 𝓝 x, eval y a ≠ 0 :=
    a.continuous_eval.continuousAt.eventually_ne hslope
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (hgraph.and hden)
  apply source_dvd_of_clearedSubstitution_eq_zero v a b Q hp hno
  apply SignLimitProportionality.eq_zero_of_eval_zero_on_open _ U hUopen ⟨x, hxU⟩
  intro y hy
  obtain ⟨hyΩ, hyden⟩ := hUsub hy
  rw [eval_clearedSubstitution v a b Q y hyden]
  have hQzero := eval_eq_zero_of_weak_sign_on_open v a b Q ha hb Ω hΩ hpos hneg
    (zeroGraph v a b y) hyΩ (eval_source_zeroGraph v a b ha hb y hyden)
    (by simpa only [zeroGraph, eval_update_of_not_mem_vars v a ha] using hyden)
  change _ * eval (zeroGraph v a b y) Q = 0
  rw [hQzero, mul_zero]

end HeadComplexity.LinearSourceDivisibility
