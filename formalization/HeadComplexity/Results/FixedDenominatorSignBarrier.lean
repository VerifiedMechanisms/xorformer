import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The fixed-denominator sign barrier

A fixed linear score space meets every strict orthant precisely when it is
the entire table space. Thus changing from exact interpolation to strict
sign representation does not save dimensions if the denominators stay fixed.
This result does not constrain denominators selected separately for each target.
-/

namespace HeadComplexity

open scoped BigOperators

/-- Every assignment of strict coordinate signs occurs in this subspace. -/
def MeetsEveryStrictOrthant {ι : Type*} (U : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ s : ι → Bool, ∃ z ∈ U, ∀ i, if s i then 0 < z i else z i < 0

/-- A proper real linear subspace misses a strict orthant. -/
theorem eq_top_of_meetsEveryStrictOrthant {ι : Type*} [Fintype ι]
    (U : Submodule ℝ (ι → ℝ)) (hU : MeetsEveryStrictOrthant U) : U = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ, hker⟩ := U.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  let a : ι → ℝ := fun i ↦ φ (Pi.single i 1)
  have hexpand (z : ι → ℝ) : φ z = ∑ i, a i * z i := by
    conv_lhs => rw [← LinearMap.sum_single_apply (fun _ : ι ↦ ℝ) z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : Pi.single i (z i) = z i • (Pi.single i 1 : ι → ℝ) := by
      ext j
      by_cases hij : j = i <;> simp [hij]
    rw [hs, map_smul]
    simp [a, mul_comm]
  have ha : ∃ i, a i ≠ 0 := by
    by_contra! hn
    apply hφ
    ext z
    simp [hexpand, hn]
  obtain ⟨z, hzU, hz⟩ := hU (fun i ↦ decide (0 < a i))
  have hnonneg (i : ι) : 0 ≤ a i * z i := by
    specialize hz i
    by_cases hi : 0 < a i
    · simp [hi] at hz
      exact le_of_lt (mul_pos hi hz)
    · simp [hi] at hz
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hi) (le_of_lt hz)
  obtain ⟨j, hj⟩ := ha
  have hpos : 0 < a j * z j := by
    specialize hz j
    rcases lt_or_gt_of_ne hj with hj | hj
    · simp [not_lt_of_gt hj] at hz
      exact mul_pos_of_neg_of_neg hj hz
    · simp [hj] at hz
      exact mul_pos hj hz
  have hsum : 0 < ∑ i, a i * z i :=
    Finset.sum_pos' (fun i _ ↦ hnonneg i) ⟨j, Finset.mem_univ j, hpos⟩
  have hz0 : φ z = 0 := hker hzU
  rw [← hexpand, hz0] at hsum
  exact (lt_irrefl 0) hsum

/-- Strict orthant universality and linear surjectivity coincide. -/
theorem meetsEveryStrictOrthant_iff_eq_top {ι : Type*} [Fintype ι]
    (U : Submodule ℝ (ι → ℝ)) : MeetsEveryStrictOrthant U ↔ U = ⊤ := by
  classical
  refine ⟨eq_top_of_meetsEveryStrictOrthant U, ?_⟩
  rintro rfl s
  refine ⟨fun i ↦ if s i then 1 else -1, Submodule.mem_top, ?_⟩
  intro i
  cases h : s i <;> simp [h]

/-- Any fixed linear parameterization representing all strict signs needs at
least as many parameter dimensions as table coordinates. -/
theorem card_le_finrank_of_range_meetsEveryStrictOrthant
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] (ι → ℝ))
    (hL : MeetsEveryStrictOrthant L.range) : Fintype.card ι ≤ Module.finrank ℝ V := by
  have hsurj : Function.Surjective L :=
    LinearMap.range_eq_top.mp (eq_top_of_meetsEveryStrictOrthant L.range hL)
  simpa using LinearMap.finrank_le_finrank_of_surjective hsurj

/-- Coefficients of the normalized fixed-denominator chart: the common
constant and one coefficient for each head and input coordinate. -/
abbrev FixedFractionParameter (n H : ℕ) := Unit ⊕ (Fin H × Fin n)

/-- The normalized features for one specified list of denominators. -/
noncomputable def fixedFractionFeature {n H : ℕ}
    (B : Fin H → (Fin n → Bool) → ℝ) :
    FixedFractionParameter n H → ((Fin n → Bool) → ℝ)
  | Sum.inl _ => fun _ ↦ 1
  | Sum.inr (h, i) => fun x ↦ (if x i then 1 else 0) / B h x

/-- A fixed denominator list that represents every strict sign table in the
normalized chart must satisfy the full interpolation dimension bound. No
positivity hypothesis is needed for this linear-space obstruction. -/
theorem two_pow_le_one_add_heads_mul_dimension_of_fixed_denominators
    {n H : ℕ} (B : Fin H → (Fin n → Bool) → ℝ)
    (huniv : ∀ s : (Fin n → Bool) → Bool,
      ∃ θ : FixedFractionParameter n H → ℝ, ∀ x,
        if s x then
          0 < Fintype.linearCombination ℝ (fixedFractionFeature B) θ x
        else Fintype.linearCombination ℝ (fixedFractionFeature B) θ x < 0) :
    2 ^ n ≤ 1 + H * n := by
  have hr : MeetsEveryStrictOrthant
      (Fintype.linearCombination ℝ (fixedFractionFeature B)).range := by
    intro s
    obtain ⟨θ, hθ⟩ := huniv s
    exact ⟨_, ⟨θ, rfl⟩, hθ⟩
  simpa [FixedFractionParameter] using
    card_le_finrank_of_range_meetsEveryStrictOrthant
      (Fintype.linearCombination ℝ (fixedFractionFeature B)) hr

end HeadComplexity
