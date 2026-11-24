import HeadComplexity.Results.AffinePlaneIncidence

set_option linter.style.header false

/-!
# Ambient dimension obstruction for direct finite-plane sharing

The nonvertical line incidence map has a kernel of dimension `q - 1`:
its kernel consists exactly of weights constant on each vertical fiber,
whose fiber values sum to zero. Consequently, any realization of all line
selectors by `d` common real features requires `q^2 <= d + q - 1`.
In particular, affine selectors on an `n`-dimensional ambient input require
`q^2 <= n + q`. Binary addresses alone do not evade this restriction.

This is an obstruction only to a specified exact selector construction,
not a lower bound for head complexity or for general rational decoders.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The weighted sum on one nonvertical affine line. -/
noncomputable def jointFamilyLineSum (w : F × F → ℝ) (a b : F) : ℝ :=
  ∑ g : F × F, if g.2 = a * g.1 + b then w g else 0

/-- The kernel of all nonvertical line sums consists exactly of constants
on vertical fibers, with zero sum across the fibers. -/
theorem jointFamily_lineSum_kernel_iff (w : F × F → ℝ) :
    (∀ a b, jointFamilyLineSum w a b = 0) ↔
      ∃ u : F → ℝ, (∑ x, u x) = 0 ∧ ∀ x y, w (x, y) = u x := by
  constructor
  · intro h
    have hq : (Fintype.card F : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hpencil (p : F × F) :
        (Fintype.card F : ℝ) * w p +
          (∑ g : F × F, if g.1 ≠ p.1 then w g else 0) = 0 := by
      have he := affinePlane_weighted_pencil_identity p (fun _ ↦ 1)
        (fun _ g ↦ w g)
      have hz : (∑ a : F, 1 * ∑ g : F × F,
          if g.2 = a * g.1 + (p.2 - a * p.1) then w g else 0) = 0 := by
        change (∑ a : F, 1 * jointFamilyLineSum w a (p.2 - a * p.1)) = 0
        simp [h]
      rw [hz] at he
      simpa using he.symm
    have hfiber (x y : F) : w (x, y) = w (x, 0) := by
      have h1 := hpencil (x, y)
      have h2 := hpencil (x, 0)
      have he : (Fintype.card F : ℝ) * (w (x, y) - w (x, 0)) = 0 := by
        dsimp only at h1 h2
        linear_combination h1 - h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hq)
    refine ⟨fun x ↦ w (x, 0), ?_, hfiber⟩
    have hh := h 0 0
    simpa [jointFamilyLineSum, Fintype.sum_prod_type] using hh
  · rintro ⟨u, hu, hw⟩ a b
    simp only [jointFamilyLineSum, Fintype.sum_prod_type, hw]
    simpa using hu

/-- Augmenting arbitrary line-selector features by all but one vertical
fiber indicator makes the point-feature vectors linearly independent. -/
theorem jointFamily_augmented_features_independent {d : ℕ}
    (feature : (F × F) → Fin d → ℝ)
    (coefficient : (F × F) → Fin d → ℝ)
    (hselector : ∀ p L : F × F,
      (if p.2 = L.1 * p.1 + L.2 then (1 : ℝ) else 0) =
        ∑ k, coefficient L k * feature p k) :
    LinearIndependent ℝ
      (fun p : F × F ↦ (Sum.elim (feature p)
        (fun x : {x : F // x ≠ 0} ↦ if p.1 = x.val then (1 : ℝ) else 0) :
          (Fin d ⊕ {x : F // x ≠ 0}) → ℝ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hfeature (k : Fin d) : (∑ p, w p * feature p k) = 0 := by
    have he := congrFun hw (Sum.inl k)
    simpa using he
  have hvertical (x : F) (hx : x ≠ 0) :
      (∑ p : F × F, if p.1 = x then w p else 0) = 0 := by
    have he := congrFun hw (Sum.inr ⟨x, hx⟩)
    simpa [mul_ite] using he
  have hline (a b : F) : jointFamilyLineSum w a b = 0 := by
    have he (p : F × F) :
        (if p.2 = a * p.1 + b then w p else 0) =
          w p * (∑ k, coefficient (a, b) k * feature p k) := by
      rw [← hselector p (a, b)]
      simp
    simp only [jointFamilyLineSum, he, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, mul_comm (w _) (coefficient (a, b) _), mul_assoc,
      ← Finset.mul_sum, hfeature, mul_zero]
    simp
  obtain ⟨u, hu, hwu⟩ := (jointFamily_lineSum_kernel_iff w).mp hline
  have hnonzero (x : F) (hx : x ≠ 0) : u x = 0 := by
    have he := hvertical x hx
    simp [Fintype.sum_prod_type, hwu] at he
    exact he
  have hzero : u 0 = 0 := by
    have he : (∑ x : F, u x) = u 0 := by
      apply Finset.sum_eq_single 0
      · intro x _ hx
        exact hnonzero x hx
      · simp
    rwa [he] at hu
  intro p
  rw [show p = (p.1, p.2) from rfl, hwu]
  by_cases hx : p.1 = 0
  · simpa [hx] using hzero
  · exact hnonzero p.1 hx

/-- A common linear feature representation of every nonvertical line
selector needs at least `q^2 - q + 1` features. -/
theorem jointFamily_line_selectors_feature_dimension {d : ℕ}
    (feature : (F × F) → Fin d → ℝ)
    (coefficient : (F × F) → Fin d → ℝ)
    (hselector : ∀ p L : F × F,
      (if p.2 = L.1 * p.1 + L.2 then (1 : ℝ) else 0) =
        ∑ k, coefficient L k * feature p k) :
    Fintype.card F * Fintype.card F + 1 ≤ d + Fintype.card F := by
  have h := (jointFamily_augmented_features_independent feature coefficient
    hselector).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hc : Fintype.card {x : F // x ≠ 0} + 1 = Fintype.card F := by
    rw [Fintype.card_subtype_compl (fun x : F ↦ x = 0),
      Fintype.card_subtype_eq]
    have := Fintype.card_pos (α := F)
    omega
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- Binary (or arbitrary real) addresses do not make the exact affine
line-selector implementation cheaper: `q^2 <= n + q` is necessary. -/
theorem jointFamily_affine_line_selectors_dimension {n : ℕ}
    (address : (F × F) → Fin n → ℝ)
    (bias : (F × F) → ℝ) (slope : (F × F) → Fin n → ℝ)
    (hselector : ∀ p L : F × F,
      (if p.2 = L.1 * p.1 + L.2 then (1 : ℝ) else 0) =
        bias L + ∑ k, slope L k * address p k) :
    Fintype.card F * Fintype.card F ≤ n + Fintype.card F := by
  let feature : (F × F) → Fin (n + 1) → ℝ :=
    fun p ↦ Fin.addCases (address p) (fun _ : Fin 1 ↦ 1)
  let coefficient : (F × F) → Fin (n + 1) → ℝ :=
    fun L ↦ Fin.addCases (slope L) (fun _ : Fin 1 ↦ bias L)
  have hrepr (p L : F × F) :
      (if p.2 = L.1 * p.1 + L.2 then (1 : ℝ) else 0) =
        ∑ k, coefficient L k * feature p k := by
    simpa [feature, coefficient, Fin.sum_univ_add, add_comm] using hselector p L
  have h := jointFamily_line_selectors_feature_dimension feature coefficient hrepr
  omega

end HeadComplexity.AxisZeroGluing
