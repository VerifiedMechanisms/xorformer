import HeadComplexity.Results.ReverseMobius

set_option linter.style.header false

/-!
# Two reverse heads for five fixed queries

This finite universal construction does not assert a superconstant saving.
Its strict axis-zero consequence uses the checked general repair theorem.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators
open Filter Topology

namespace FiveQueries

def signQ (b : Bool) : ℚ := if b then 1 else -1

def Y (σ : Fin 5 → Bool) : Fin 3 → ℚ :=
  ![(if σ 0 then 8 else 1) * signQ (σ 2),
    (if σ 0 then 1 else 8) * signQ (σ 3), signQ (σ 4)]

def X (σ : Fin 5 → Bool) : ℚ := (Y σ 0 + Y σ 1) / 2

def V (σ : Fin 5 → Bool) : ℚ := (5 * Y σ 0 - 3 * Y σ 1 - 2 * Y σ 2) / 4

def P (σ : Fin 5 → Bool) : ℚ := 25 * (2 * Y σ 2 - 3 * Y σ 0 + Y σ 1)

def Q (σ : Fin 5 → Bool) : ℚ := X σ * V σ

def L (σ : Fin 5 → Bool) : ℚ := if σ 0 = σ 1 then 0 else -Q σ * 201 / 202

def pole (σ : Fin 5 → Bool) : Fin 2 → ℚ := ![P σ + V σ, P σ]

def denom : Fin 2 → Fin 5 → ℚ :=
  ![![1, 101/100, 99/100, 99/100, 98/100], ![1, 101/100, 1, 1, 1]]

def offset : Fin 2 → Fin 5 → ℚ :=
  ![![0, 0, 99/10000, -99/10000, 98/2500], ![0, 0, -1/100, 1/100, -1/25]]

def leading (σ : Fin 5 → Bool) : Fin 5 → ℚ :=
  ![L σ + Q σ, 101/100 * L σ + Q σ,
    Y σ 0 / 100, Y σ 1 / 100, Y σ 2 / 50]

/-- Exact finite certificate, checked by kernel reduction over rationals. -/
theorem leading_sign : ∀ (σ : Fin 5 → Bool) (j : Fin 5),
    0 < signQ (σ j) * leading σ j := by
  intro σ j
  fin_cases j <;>
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    cases h3 : σ 3 <;> cases h4 : σ 4 <;>
    norm_num [signQ, leading, L, Q, X, V, Y, h0, h1, h2, h3, h4]

/-- Uniform coefficient bounds used only for the full-cube extension. -/
theorem pole_bounds : ∀ (σ : Fin 5 → Bool) (h : Fin 2),
    (-800 : ℚ) ≤ pole σ h := by
  intro σ h
  fin_cases h <;>
    cases h0 : σ 0 <;> cases h2 : σ 2 <;> cases h3 : σ 3 <;> cases h4 : σ 4 <;>
    norm_num [pole, P, V, Y, signQ, h0, h2, h3, h4]

theorem denom_bounds : ∀ (h : Fin 2) (j : Fin 5),
    0 < denom h j ∧ denom h j ≤ 101/100 := by
  intro h j
  fin_cases h <;> fin_cases j <;> norm_num [denom]

noncomputable def numerator (δ : ℝ) (σ : Fin 5 → Bool) : Fin 2 → ℝ :=
  ![δ * (X σ : ℝ), -δ * (X σ : ℝ) + δ^2 * (L σ : ℝ)]

noncomputable def germ (δ : ℝ) (σ : Fin 5 → Bool) : Fin 5 → ℝ :=
  ![(leading σ 0 : ℝ) - δ * (L σ : ℝ) * (pole σ 0 : ℝ),
    (leading σ 1 : ℝ) - δ * (L σ : ℝ) * (pole σ 0 : ℝ),
    (leading σ 2 : ℝ) + δ * ((99/100 : ℝ) * (L σ : ℝ) + (Q σ : ℝ))
      - δ^2 * (L σ : ℝ) * (pole σ 0 : ℝ),
    (leading σ 3 : ℝ) + δ * ((99/100 : ℝ) * (L σ : ℝ) + (Q σ : ℝ))
      - δ^2 * (L σ : ℝ) * (pole σ 0 : ℝ),
    (leading σ 4 : ℝ) + δ * ((98/100 : ℝ) * (L σ : ℝ) + (Q σ : ℝ))
      - δ^2 * (L σ : ℝ) * (pole σ 0 : ℝ)]

lemma germ_zero (σ : Fin 5 → Bool) (j : Fin 5) :
    germ 0 σ j = (leading σ j : ℝ) := by
  fin_cases j <;> simp [germ]

lemma germ_continuous (σ : Fin 5 → Bool) (j : Fin 5) :
    Continuous (fun δ ↦ germ δ σ j) := by
  fin_cases j <;> dsimp [germ] <;> fun_prop

lemma cleared (δ : ℝ) (σ : Fin 5 → Bool) (j : Fin 5) :
    (numerator δ σ 0 + (offset 0 j : ℝ)) * ((denom 1 j : ℝ) - δ * (pole σ 1 : ℝ)) +
      ((denom 0 j : ℝ) - δ * (pole σ 0 : ℝ)) * (numerator δ σ 1 + (offset 1 j : ℝ)) =
      (if j.val < 2 then δ^2 else δ) * germ δ σ j := by
  fin_cases j <;>
    norm_num [numerator, offset, denom, germ, leading, pole, Q, X, V, P] <;>
    ring


/-- A common positive perturbation realizes every row pattern and the
full-cube budgets for this finite table. -/
theorem exists_perturbation {r : ℕ} (table : Fin r → Fin 5 → Bool) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ σ : Fin 5 → Bool, ∀ j,
        0 < outputSign (σ j) * germ δ σ j ∧
        ∀ h, 0 < (denom h j : ℝ) - δ * (pole σ h : ℝ)) ∧
      ∀ h : Fin 2, 0 < separatedReverseSlack
        (fun i ↦ δ * (pole (table i) h : ℝ))
        (fun j ↦ (denom h j : ℝ)) (-800 * δ) (101/100) := by
  have hgood : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ σ : Fin 5 → Bool, ∀ j,
      0 < outputSign (σ j) * germ δ σ j ∧
      ∀ h, 0 < (denom h j : ℝ) - δ * (pole σ h : ℝ) := by
    apply Filter.eventually_all.mpr
    intro σ
    apply Filter.eventually_all.mpr
    intro j
    have hs : 0 < outputSign (σ j) * germ 0 σ j := by
      rw [germ_zero]
      have hcast : outputSign (σ j) = (signQ (σ j) : ℝ) := by
        cases σ j <;> norm_num [outputSign, signQ]
      rw [hcast]
      exact_mod_cast leading_sign σ j
    have hg := continuousAt_const.eventually_lt
      (continuousAt_const.mul (germ_continuous σ j).continuousAt) hs
    refine hg.and (Filter.eventually_all.mpr ?_)
    intro h
    apply continuousAt_const.eventually_lt
      (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
    simpa using (show (0 : ℝ) < (denom h j : ℝ) by exact_mod_cast (denom_bounds h j).1)
  have hslack : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ h : Fin 2,
      0 < separatedReverseSlack (fun i ↦ δ * (pole (table i) h : ℝ))
        (fun j ↦ (denom h j : ℝ)) (-800 * δ) (101/100) := by
    apply Filter.eventually_all.mpr
    intro h
    have hc : Continuous (fun δ : ℝ ↦ separatedReverseSlack
        (fun i ↦ δ * (pole (table i) h : ℝ))
        (fun j ↦ (denom h j : ℝ)) (-800 * δ) (101/100)) := by
      unfold separatedReverseSlack
      fun_prop
    apply continuousAt_const.eventually_lt hc.continuousAt
    fin_cases h <;> norm_num [separatedReverseSlack, denom, Fin.sum_univ_succ]
  have hall := hgood.and hslack
  rcases Metric.mem_nhds_iff.mp hall with ⟨radius, hradius, hball⟩
  have hδ : 0 < radius / 2 := by positivity
  refine ⟨radius / 2, hδ, ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ]
  linarith

end FiveQueries

/-- Every table with five columns has a universal two-head reverse grid
compiler. No axis assertion is used in this theorem. -/
theorem hasWeakReverseGridCompiler_five (r : ℕ) : HasWeakReverseGridCompiler r 5 2 := by
  classical
  intro table
  obtain ⟨δ, hδ, hgood, hslack⟩ := FiveQueries.exists_perturbation table
  choose R hR using fun h : Fin 2 ↦ exists_weak_reverse_separated
    (fun i ↦ δ * (FiveQueries.pole (table i) h : ℝ))
    (fun i ↦ FiveQueries.numerator δ (table i) h)
    (fun j ↦ (FiveQueries.denom h j : ℝ))
    (fun j ↦ (FiveQueries.offset h j : ℝ)) (-800 * δ) (101/100)
    (fun i ↦ by
      have hp : (-800 : ℝ) ≤ (FiveQueries.pole (table i) h : ℝ) := by
        exact_mod_cast FiveQueries.pole_bounds (table i) h
      nlinarith)
    (fun j ↦ by
      have hh : (FiveQueries.denom h j : ℝ) ≤ ((101/100 : ℚ) : ℝ) := by
        exact_mod_cast (FiveQueries.denom_bounds h j).2
      norm_num at hh
      exact hh)
    (hslack h)
  let G : WeakReverseGridData r 5 2 := ⟨0, R⟩
  refine ⟨2, le_rfl, G, ?_⟩
  intro i j
  change 0 < outputSign (table i j) *
    (0 + ∑ h, (R h).value (localGrid i j))
  simp only [zero_add, hR, Fin.sum_univ_two]
  have h0 := (hgood (table i) j).2 0
  have h1 := (hgood (table i) j).2 1
  rw [div_add_div _ _ (ne_of_gt h0) (ne_of_gt h1), ← mul_div_assoc,
    FiveQueries.cleared]
  apply div_pos
  · have hg := (hgood (table i) j).1
    have hf : 0 < (if j.val < 2 then δ^2 else δ) := by split <;> positivity
    nlinarith
  · exact mul_pos h0 h1

/-- Strict slopes, full-cube positivity, and both exact axis conditions
hold for every five-column sign table, with nine heads. -/
theorem hasReverseAxisCompiler_five (r : ℕ) : HasReverseAxisCompiler r 5 9 := by
  simpa using hasReverseAxisCompiler_of_weakReverseGridCompiler
    (hasWeakReverseGridCompiler_five r)

end HeadComplexity.AxisZeroGluing
