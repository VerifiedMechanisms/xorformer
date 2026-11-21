import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
Exact linear feasibility for completing a fixed residual by one fraction.
The residual is fixed throughout. This does not assert feasibility or a
global progress theorem for several adaptive denominators.
-/

namespace HeadComplexity

open scoped BigOperators

private theorem positive_uniform_slack {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ v i := by
  classical
  have h : ∀ s : Finset ι, ∃ ρ : ℝ, 0 < ρ ∧ ∀ i ∈ s, ρ ≤ v i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ρ, hρ, hr⟩ := ih
      refine ⟨min (v a) ρ, lt_min (hv a) hρ, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hr i hi)
  obtain ⟨ρ, hρ, hr⟩ := h Finset.univ
  exact ⟨ρ, hρ, fun i => hr i (Finset.mem_univ _)⟩

def completionPairing {X J : Type*} [Fintype J]
    (z : X → J → ℝ) (a : J → ℝ) (x : X) : ℝ :=
  ∑ j, a j * z x j

private theorem completionPairing_pos {X J : Type*} [Fintype J]
    (z : X → J → ℝ) (j₀ : J) (hz : ∀ x j, 0 ≤ z x j)
    (hz₀ : ∀ x, z x j₀ = 1) (b : J → ℝ) (hb : ∀ j, 0 < b j)
    (x : X) : 0 < completionPairing z b x := by
  classical
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (hb j).le (hz x j)
  · refine ⟨j₀, Finset.mem_univ _, ?_⟩
    simpa only [hz₀ x, mul_one] using hb j₀

private theorem completionPairing_div {X J : Type*} [Fintype J]
    (z : X → J → ℝ) (a : J → ℝ) (s : ℝ) (x : X) :
    completionPairing z (fun j => a j / s) x =
      completionPairing z a x / s := by
  simp only [completionPairing, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Strict sign completion with positive denominator coefficients. -/
def StrictFractionCompletion {X J : Type*} [Fintype J]
    (z : X → J → ℝ) (label residual : X → ℝ) : Prop :=
  ∃ a b : J → ℝ, (∀ j, 0 < b j) ∧
    ∀ x, 0 < label x * (residual x +
      completionPairing z a x / completionPairing z b x)

/-- A common positive slack in the normalized linear inequalities. -/
def PositiveSlackFractionCompletion {X J : Type*} [Fintype J]
    (z : X → J → ℝ) (label residual : X → ℝ) : Prop :=
  ∃ a b : J → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ (∑ j, b j) = 1 ∧
    (∀ j, ρ ≤ b j) ∧
    ∀ x, ρ ≤ label x * (residual x * completionPairing z b x +
      completionPairing z a x)

/-- Completing a fixed residual by one admissible fraction is equivalent
to strict feasibility of a linear system. No feasibility is assumed. -/
theorem strictFractionCompletion_iff_positiveSlack
    {X J : Type*} [Fintype X] [Fintype J]
    (z : X → J → ℝ) (j₀ : J) (hz : ∀ x j, 0 ≤ z x j)
    (hz₀ : ∀ x, z x j₀ = 1) (label residual : X → ℝ) :
    StrictFractionCompletion z label residual ↔
      PositiveSlackFractionCompletion z label residual := by
  classical
  constructor
  · rintro ⟨a, b, hb, hm⟩
    let s : ℝ := ∑ j, b j
    have hs : 0 < s := by
      apply Finset.sum_pos'
      · intro j hj
        exact (hb j).le
      · exact ⟨j₀, Finset.mem_univ _, hb j₀⟩
    let a' := fun j => a j / s
    let b' := fun j => b j / s
    have hb' : ∀ j, 0 < b' j := fun j => div_pos (hb j) hs
    have hB' : ∀ x, 0 < completionPairing z b' x :=
      completionPairing_pos z j₀ hz hz₀ b' hb'
    have hratio : ∀ x,
        completionPairing z a' x / completionPairing z b' x =
        completionPairing z a x / completionPairing z b x := by
      intro x
      dsimp [a', b']
      rw [completionPairing_div, completionPairing_div]
      field_simp [hs.ne']
    let cleared := fun x => label x *
      (residual x * completionPairing z b' x + completionPairing z a' x)
    have hc : ∀ x, 0 < cleared x := by
      intro x
      have he : cleared x = completionPairing z b' x *
          (label x * (residual x +
            completionPairing z a' x / completionPairing z b' x)) := by
        dsimp [cleared]
        field_simp [(hB' x).ne']
      rw [he, hratio x]
      exact mul_pos (hB' x) (hm x)
    obtain ⟨ρ, hρ, hr⟩ := positive_uniform_slack
      (Sum.elim b' cleared) (by intro i; cases i <;> simp_all)
    refine ⟨a', b', ρ, hρ, ?_, ?_, ?_⟩
    · dsimp [b']
      rw [← Finset.sum_div]
      exact div_self hs.ne'
    · intro j
      exact hr (Sum.inl j)
    · intro x
      exact hr (Sum.inr x)
  · rintro ⟨a, b, ρ, hρ, hsum, hb, hc⟩
    have hb' : ∀ j, 0 < b j := fun j => hρ.trans_le (hb j)
    refine ⟨a, b, hb', ?_⟩
    intro x
    have hB := completionPairing_pos z j₀ hz hz₀ b hb' x
    have he : label x * (residual x +
        completionPairing z a x / completionPairing z b x) =
        (label x * (residual x * completionPairing z b x +
          completionPairing z a x)) / completionPairing z b x := by
      field_simp [hB.ne']
    rw [he]
    exact div_pos (hρ.trans_le (hc x)) hB

/-- A nonnegative signed moment witness obstructs completion of this fixed
residual. It is not a certificate against changing the other heads. -/
theorem not_strictFractionCompletion_of_moment_witness
    {X J : Type*} [Fintype X] [Fintype J]
    (z : X → J → ℝ) (j₀ : J) (hz : ∀ x j, 0 ≤ z x j)
    (hz₀ : ∀ x, z x j₀ = 1) (label residual weight : X → ℝ)
    (hw : ∀ x, 0 ≤ weight x) (hwpos : ∃ x, 0 < weight x)
    (hzero : ∀ j, ∑ x, weight x * label x * z x j = 0)
    (hnonpos : ∀ j, ∑ x, weight x * label x * residual x * z x j ≤ 0) :
    ¬ StrictFractionCompletion z label residual := by
  classical
  rintro ⟨a, b, hb, hm⟩
  have hB := completionPairing_pos z j₀ hz hz₀ b hb
  have hc : ∀ x, 0 < label x *
      (residual x * completionPairing z b x + completionPairing z a x) := by
    intro x
    have he : label x *
        (residual x * completionPairing z b x + completionPairing z a x) =
        completionPairing z b x * (label x * (residual x +
          completionPairing z a x / completionPairing z b x)) := by
      field_simp [(hB x).ne']
    rw [he]
    exact mul_pos (hB x) (hm x)
  have hsumpos : 0 < ∑ x, weight x * (label x *
      (residual x * completionPairing z b x + completionPairing z a x)) := by
    apply Finset.sum_pos'
    · intro x hx
      exact mul_nonneg (hw x) (hc x).le
    · obtain ⟨x, hx⟩ := hwpos
      exact ⟨x, Finset.mem_univ _, mul_pos hx (hc x)⟩
  have hid : (∑ x, weight x * (label x *
      (residual x * completionPairing z b x + completionPairing z a x))) =
      ∑ j, (b j * (∑ x, weight x * label x * residual x * z x j) +
        a j * (∑ x, weight x * label x * z x j)) := by
    simp only [completionPairing, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x j =>
      weight x * (label x * (a j * z x j)))]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
      apply Finset.sum_congr rfl <;> intro x hx <;> ring
  have hsumneg : (∑ j, (b j *
      (∑ x, weight x * label x * residual x * z x j) +
        a j * (∑ x, weight x * label x * z x j))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    rw [hzero j, mul_zero, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hb j).le (hnonpos j)
  rw [hid] at hsumpos
  exact (not_lt_of_ge hsumneg) hsumpos

end HeadComplexity
