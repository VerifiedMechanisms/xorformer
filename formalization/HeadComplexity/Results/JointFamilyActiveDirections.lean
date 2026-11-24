import HeadComplexity.Results.JointFamilyIncidenceObstruction

set_option linter.style.header false

/-! The rank obstruction persists when only some line directions are used.
`K` distinct nonvertical parallel classes span `K * (q - 1) + 1`
dimensions. This avoids assuming every Cauchy pole is active. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype A] [DecidableEq A]

private theorem sum_affine_argument (v : F → ℝ) {u : F} (hu : u ≠ 0) (b : F) :
    (∑ x : F, v (u * x + b)) = ∑ y : F, v y := by
  exact ((Equiv.mulLeft₀ u hu).trans (Equiv.addRight b)).sum_comp v

private theorem direction_pencil_sum
    (slope : A → F) (hslope : Function.Injective slope)
    (w : A → F → ℝ) (a : A) (b : F) :
    (∑ x : F, ∑ j : A, w j (slope a * x + b - slope j * x)) =
      (Fintype.card F : ℝ) * w a b +
        ∑ j : A, if j ≠ a then ∑ y : F, w j y else 0 := by
  rw [Finset.sum_comm]
  have he (j : A) :
      (∑ x : F, w j (slope a * x + b - slope j * x)) =
        (if j = a then (Fintype.card F : ℝ) * w a b else 0) +
        (if j ≠ a then ∑ y : F, w j y else 0) := by
    by_cases hj : j = a
    · subst j
      have harg (x : F) : slope a * x + b - slope a * x = b := by ring
      simp [harg]
    · have hne : slope a - slope j ≠ 0 := by
        exact sub_ne_zero.mpr (fun h ↦ hj (hslope h).symm)
      have harg (x : F) : slope a * x + b - slope j * x =
          (slope a - slope j) * x + b := by ring
      simp only [harg]
      rw [sum_affine_argument (w j) hne]
      simp [hj]
  simp_rw [he, Finset.sum_add_distrib]
  simp

/-- A linear relation among the constant and all but one line in each
selected parallel class is trivial. -/
theorem jointFamily_active_direction_relation
    (slope : A → F) (hslope : Function.Injective slope)
    (w : A → F → ℝ) (c : ℝ)
    (hzero : ∀ a, w a 0 = 0)
    (hrelation : ∀ x y : F, c + ∑ a : A, w a (y - slope a * x) = 0) :
    c = 0 ∧ ∀ a b, w a b = 0 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpencil (a : A) (b : F) :
      (Fintype.card F : ℝ) * c + (Fintype.card F : ℝ) * w a b +
        (∑ j : A, if j ≠ a then ∑ y : F, w j y else 0) = 0 := by
    have h := Finset.sum_eq_zero (s := (Finset.univ : Finset F))
      (fun x _ ↦ hrelation x (slope a * x + b))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, direction_pencil_sum slope hslope w a b] at h
    linarith
  have hw (a : A) (b : F) : w a b = 0 := by
    have h1 := hpencil a b
    have h2 := hpencil a 0
    rw [hzero a] at h2
    have he : (Fintype.card F : ℝ) * w a b = 0 := by linarith
    exact (mul_eq_zero.mp he).resolve_left hq
  refine ⟨?_, hw⟩
  simpa [hw] using hrelation 0 0

/-- One constant and `q - 1` line indicators for each of `K` distinct
directions are linearly independent over the reals. -/
theorem jointFamily_active_direction_independent
    (slope : A → F) (hslope : Function.Injective slope) :
    LinearIndependent ℝ
      (fun t : Option (A × {b : F // b ≠ 0}) ↦
        (match t with
          | none => fun _ ↦ (1 : ℝ)
          | some (a, b) => fun p ↦
              if p.2 = slope a * p.1 + b.val then 1 else 0 : (F × F) → ℝ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro z hz
  let w : A → F → ℝ := fun a b ↦ if hb : b ≠ 0 then z (some (a, ⟨b, hb⟩)) else 0
  have hzero (a : A) : w a 0 = 0 := by simp [w]
  have hsum (a : A) (x y : F) :
      (∑ b : {b : F // b ≠ 0},
        z (some (a, b)) * (if y = slope a * x + b.val then (1 : ℝ) else 0)) =
        w a (y - slope a * x) := by
    by_cases hb : y - slope a * x = 0
    · have harg : y = slope a * x := sub_eq_zero.mp hb
      have hfalse (b : {b : F // b ≠ 0}) : ¬ y = slope a * x + b.val := by
        intro he
        apply b.property
        linear_combination harg - he
      simp [w, hb, hfalse]
    · let b : {b : F // b ≠ 0} := ⟨y - slope a * x, hb⟩
      rw [Finset.sum_eq_single b]
      · have he : y = slope a * x + b.val := by dsimp [b]; ring
        rw [if_pos he, mul_one]
        simp only [w, dif_pos hb]
        rfl
      · intro b' _ hne
        have hfalse : ¬ y = slope a * x + b'.val := by
          intro he
          apply hne
          apply Subtype.ext
          dsimp [b]
          linear_combination -he
        simp [hfalse]
      · simp
  have hrelation (x y : F) : z none + ∑ a : A, w a (y - slope a * x) = 0 := by
    have he := congrFun hz (x, y)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, Fintype.sum_prod_type] at he
    change z none * 1 + (∑ a : A, ∑ b : {b : F // b ≠ 0},
      z (some (a, b)) * (if y = slope a * x + b.val then (1 : ℝ) else 0)) = 0 at he
    simpa only [mul_one, hsum] using he
  obtain ⟨hc, hw⟩ := jointFamily_active_direction_relation slope hslope w
    (z none) hzero hrelation
  intro t
  cases t with
  | none => exact hc
  | some t =>
    obtain ⟨a, b⟩ := t
    simpa [w, b.property] using hw a b.val

/-- `K` active directions already require `K * (q - 1) + 1`
shared features. No inactive direction is charged. -/
theorem jointFamily_active_direction_feature_dimension [Nonempty A] {d : ℕ}
    (slope : A → F) (hslope : Function.Injective slope)
    (feature : (F × F) → Fin d → ℝ)
    (coefficient : A → F → Fin d → ℝ)
    (hselector : ∀ p : F × F, ∀ a b,
      (if p.2 = slope a * p.1 + b then (1 : ℝ) else 0) =
        ∑ k, coefficient a b k * feature p k) :
    Fintype.card A * (Fintype.card F - 1) + 1 ≤ d := by
  classical
  let a₀ : A := Classical.choice inferInstance
  let T : (Fin d → ℝ) →ₗ[ℝ] ((F × F) → ℝ) :=
    { toFun := fun v p ↦ ∑ k, v k * feature p k
      map_add' := by intro v w; ext p; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c v; ext p; simp [Finset.mul_sum, mul_assoc] }
  let v : Option (A × {b : F // b ≠ 0}) → Fin d → ℝ := fun t ↦
    match t with
    | none => fun k ↦ ∑ b : F, coefficient a₀ b k
    | some (a, b) => coefficient a b.val
  have himage : LinearIndependent ℝ (T ∘ v) := by
    convert jointFamily_active_direction_independent slope hslope using 1
    funext t p
    cases t with
    | none =>
      change (∑ k, (∑ b : F, coefficient a₀ b k) * feature p k) = 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [← hselector]
      have he (b : F) : (p.2 = slope a₀ * p.1 + b) ↔
          b = p.2 - slope a₀ * p.1 := by
        constructor <;> intro h <;> linear_combination -h
      simp_rw [he]
      simp
    | some t =>
      obtain ⟨a, b⟩ := t
      exact (hselector p a b.val).symm
  have hind : LinearIndependent ℝ v := himage.of_comp T
  have hdim := hind.fintype_card_le_finrank
  have hc : Fintype.card {b : F // b ≠ 0} = Fintype.card F - 1 := by
    rw [Fintype.card_subtype_compl (fun b : F ↦ b = 0), Fintype.card_subtype_eq]
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Fintype.card_option, Fintype.card_prod, hc] using hdim

/-- The ambient affine dimension obstruction for an arbitrary active set
of `K` distinct directions is `K * (q - 1) <= n`. -/
theorem jointFamily_active_affine_selectors_dimension [Nonempty A] {n : ℕ}
    (slope : A → F) (hslope : Function.Injective slope)
    (address : (F × F) → Fin n → ℝ)
    (bias : A → F → ℝ) (weight : A → F → Fin n → ℝ)
    (hselector : ∀ p : F × F, ∀ a b,
      (if p.2 = slope a * p.1 + b then (1 : ℝ) else 0) =
        bias a b + ∑ k, weight a b k * address p k) :
    Fintype.card A * (Fintype.card F - 1) ≤ n := by
  let feature : (F × F) → Fin (n + 1) → ℝ :=
    fun p ↦ Fin.addCases (address p) (fun _ : Fin 1 ↦ 1)
  let coefficient : A → F → Fin (n + 1) → ℝ :=
    fun a b ↦ Fin.addCases (weight a b) (fun _ : Fin 1 ↦ bias a b)
  have hrepr (p : F × F) (a : A) (b : F) :
      (if p.2 = slope a * p.1 + b then (1 : ℝ) else 0) =
        ∑ k, coefficient a b k * feature p k := by
    simpa [feature, coefficient, Fin.sum_univ_add, add_comm] using hselector p a b
  have h := jointFamily_active_direction_feature_dimension slope hslope
    feature coefficient hrepr
  omega

/-- Nonzero, direction-dependent Cauchy weights do not change the active
direction obstruction, since each selector can be divided by its weight. -/
theorem jointFamily_active_weighted_affine_selectors_dimension [Nonempty A] {n : ℕ}
    (slope : A → F) (hslope : Function.Injective slope)
    (η : A → ℝ) (hη : ∀ a, η a ≠ 0)
    (address : (F × F) → Fin n → ℝ)
    (bias : A → F → ℝ) (weight : A → F → Fin n → ℝ)
    (hselector : ∀ p : F × F, ∀ a b,
      (if p.2 = slope a * p.1 + b then η a else 0) =
        bias a b + ∑ k, weight a b k * address p k) :
    Fintype.card A * (Fintype.card F - 1) ≤ n := by
  apply jointFamily_active_affine_selectors_dimension slope hslope address
    (fun a b ↦ bias a b / η a) (fun a b k ↦ weight a b k / η a)
  intro p a b
  have he := congrArg (fun z : ℝ ↦ z / η a) (hselector p a b)
  simpa only [ite_div, div_self (hη a), zero_div, add_div, Finset.sum_div,
    div_mul_eq_mul_div] using he

end HeadComplexity.AxisZeroGluing
