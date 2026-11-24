import HeadComplexity.Atoms.AtomicMargin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
Finite coordinate fibers can be centered and scaled to have a full absolute
unit gap. This operation does not preserve an active linear basis: a full
injective basis on which every value is one forces the constant function.
-/

noncomputable section
namespace HeadComplexity.FiniteFiberUnitGap
open Finset
open scoped BigOperators

variable {J X : Type*} [Fintype J] [Fintype X]

/-- A common finite scale, allowing arbitrary zero coordinates. -/
def gapScale (D : J → X → ℝ) : ℝ :=
  1 + ∑ j, ∑ x, 2 / |D j x|

theorem gapScale_pos (D : J → X → ℝ) : 0 < gapScale D := by
  unfold gapScale
  have : 0 ≤ ∑ j, ∑ x, 2 / |D j x| :=
    sum_nonneg fun j _ ↦ sum_nonneg fun x _ ↦ div_nonneg (by norm_num) (abs_nonneg _)
  linarith

theorem gapScale_mul_abs_ge (D : J → X → ℝ) (j : J) (x : X)
    (h : D j x ≠ 0) : 2 ≤ gapScale D * |D j x| := by
  classical
  have hp : 0 < |D j x| := abs_pos.mpr h
  have hx : 2 / |D j x| ≤ ∑ y, 2 / |D j y| :=
    single_le_sum (f := fun y ↦ 2 / |D j y|)
      (fun y _ ↦ div_nonneg (by norm_num) (abs_nonneg _)) (mem_univ x)
  have hj : (∑ y, 2 / |D j y|) ≤ ∑ k, ∑ y, 2 / |D k y| :=
    single_le_sum (f := fun k ↦ ∑ y : X, 2 / |D k y|)
      (fun k _ ↦ sum_nonneg fun y _ ↦
      div_nonneg (by norm_num) (abs_nonneg _)) (mem_univ j)
  have hm : 2 / |D j x| ≤ gapScale D := by unfold gapScale; linarith
  exact (div_le_iff₀ hp).mp hm

/-- All finite differences can be turned into scores with an absolute unit gap;
zero differences receive the positive label. -/
theorem centered_unit_gap (D : J → X → ℝ) (j : J) (x : X) :
    1 ≤ |1 + gapScale D * D j x| ∧
      (0 < 1 + gapScale D * D j x ↔ 0 ≤ D j x) := by
  by_cases hz : D j x = 0
  · simp [hz]
  have hm := gapScale_mul_abs_ge D j x hz
  rcases lt_or_gt_of_ne hz with hn | hp
  · rw [abs_of_neg hn] at hm
    have hs : 1 + gapScale D * D j x ≤ -1 := by nlinarith
    rw [abs_of_neg (by linarith)]
    constructor
    · linarith
    · constructor <;> intro hh <;> linarith
  · rw [abs_of_pos hp] at hm
    have hs : 0 < 1 + gapScale D * D j x := by linarith
    rw [abs_of_pos hs]
    exact ⟨by linarith, iff_of_true hs hp.le⟩

/-- Common coordinate observations become exact positive unit contacts. -/
theorem common_fiber_unit_contacts (S : J → X → ℝ) (G : X → ℝ)
    (I : Set X) (hI : ∀ j x, x ∈ I → S j x = G x) :
    ∀ j x, x ∈ I → 1 + gapScale (fun j x ↦ S j x - G x) *
      (S j x - G x) = 1 := by
  intro j x hx
  simp [hI j x hx]

variable {n H K : ℕ}

/-- The centering construction uses exactly the disjoint union of the original
heads and a fixed interpolating score's heads. Every scaled head is genuine. -/
theorem atom_centering_identity
    (φ : J → Fin H → FracAtom n) (ψ : Fin K → FracAtom n)
    (b : J → ℝ) (c M : ℝ) (j : J) (x : Fin n → Bool) :
    (1 + M * (b j - c)) +
      (∑ h : Fin H ⊕ Fin K,
        (Sum.elim (fun h ↦ (φ j h).scale M)
          (fun k ↦ (ψ k).scale (-M)) h).eval x) =
      1 + M * ((b j + ∑ h, (φ j h).eval x) -
        (c + ∑ k, (ψ k).eval x)) := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    FracAtom.scale_eval, ← Finset.mul_sum]
  ring

/-- An injective actual-row restriction excludes nonconstant interpolants with
all-positive unit data. Thus the preceding fiber transfer alone cannot give a
full active-basis branching counterexample. -/
theorem all_positive_contacts_force_constant
    {L : Type*} [Fintype L] (F : X → L → ℝ)
    (I : Set X) (a a₀ : L → ℝ)
    (hconst : ∀ x, ∑ l, F x l * a₀ l = 1)
    (hinj : Function.Injective (fun u : L → ℝ ↦
      fun x : I ↦ ∑ l, F x.val l * u l))
    (hcontact : ∀ x ∈ I, ∑ l, F x l * a l = 1) :
    ∀ x, ∑ l, F x l * a l = 1 := by
  have heq : a = a₀ := hinj (by
    funext x
    change (∑ l, F x.val l * a l) = ∑ l, F x.val l * a₀ l
    rw [hcontact x.val x.property, hconst x.val])
  simpa [heq] using hconst

end HeadComplexity.FiniteFiberUnitGap
