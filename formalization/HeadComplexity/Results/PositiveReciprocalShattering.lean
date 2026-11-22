import HeadComplexity.Atoms.PositiveReciprocalCompletion
import HeadComplexity.Results.ReciprocalMatchingShattering

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-! Unbounded free-query sign shattering with strictly positive poles,
residues and parameter witnesses. These queries are not asserted to be a
full Boolean-cube evaluation table for a small attention-head model. -/

namespace HeadComplexity.PositiveReciprocalShattering

open Finset PositiveReciprocalCompletion

theorem completion {I J : Type*} [Fintype I]
    (poles residues : J → I → ℝ) (hp : ∀ j i, 0 < poles j i)
    (hshatter : ∀ label : J → Bool, ∃ θ : I → ℝ,
      (∀ i, 0 < θ i) ∧ ∀ j,
        (if label j then (1 : ℝ) else -1) *
          (∑ i, residues j i / (θ i + poles j i)) > 1 / 2) :
    ∃ P A : J → I × Bool → ℝ, ∃ c : J → ℝ,
      (∀ j i, 0 < P j i ∧ 0 < A j i) ∧
      ∀ label : J → Bool, ∃ z : I × Bool → ℝ,
        (∀ i, 0 < z i) ∧ ∀ j,
          (if label j then (1 : ℝ) else -1) *
            ((∑ i, A j i / (z i + P j i)) - c j) > 1 / 4 := by
  classical
  let δ : ℝ := 1 / (8 * (Fintype.card I : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let P : J → I × Bool → ℝ := fun j i ↦ pole (residues j i.1) (poles j i.1) i.2
  let A : J → I × Bool → ℝ := fun j i ↦ residue δ (residues j i.1) (poles j i.1) i.2
  let c : J → ℝ := fun j ↦ ∑ i, constant (residues j i) (poles j i)
  refine ⟨P, A, c, ?_, ?_⟩
  · intro j i
    exact ⟨pole_positive (hp j i.1) i.2, residue_positive hδ (hp j i.1) i.2⟩
  · intro label
    obtain ⟨θ, hθ, hsign⟩ := hshatter label
    let z : I × Bool → ℝ := fun i ↦ parameter (θ i.1) i.2
    refine ⟨z, fun i ↦ parameter_positive (hθ i.1) i.2, ?_⟩
    intro j
    let old : ℝ := ∑ i, residues j i / (θ i + poles j i)
    let new : ℝ := (∑ i, A j i / (z i + P j i)) - c j
    let err : I → ℝ := fun i ↦ pairValue δ (residues j i) (poles j i) (θ i) -
      constant (residues j i) (poles j i) - residues j i / (θ i + poles j i)
    have he : new - old = ∑ i, err i := by
      dsimp [new, old, err, A, P, z, c, pairValue]
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_sub_distrib]
      simp
    have hb (i : I) : 0 ≤ err i ∧ err i ≤ 2 * δ :=
      pair_error hδ (hp j i) (hθ i)
    have hlo : 0 ≤ new - old := by
      rw [he]
      exact Finset.sum_nonneg fun i _ ↦ (hb i).1
    have hhi : new - old ≤ (Fintype.card I : ℝ) * (2 * δ) := by
      rw [he]
      calc
        _ ≤ ∑ _i : I, 2 * δ := Finset.sum_le_sum fun i _ ↦ (hb i).2
        _ = _ := by simp
    have hsmall : (Fintype.card I : ℝ) * (2 * δ) < 1 / 4 := by
      have hd : (0 : ℝ) < 8 * (Fintype.card I : ℝ) + 1 := by positivity
      have hh : (8 * (Fintype.card I : ℝ)) / (8 * (Fintype.card I : ℝ) + 1) < 1 := by
        apply (div_lt_iff₀ hd).mpr
        linarith
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      dsimp [δ]
      convert hh using 1
      ring
    have hold := hsign j
    change (if label j then (1 : ℝ) else -1) * old > 1 / 2 at hold
    change (if label j then (1 : ℝ) else -1) * new > 1 / 4
    cases hlabel : label j <;> simp only [hlabel, Bool.false_eq_true, ite_false,
      ite_true, neg_mul, one_mul] at hold ⊢ <;> linarith

theorem completion_fin {p m : ℕ}
    (poles residues : Fin m → Fin p → ℝ) (hp : ∀ j i, 0 < poles j i)
    (hshatter : ∀ label : Fin m → Bool, ∃ θ : Fin p → ℝ,
      (∀ i, 0 < θ i) ∧ ∀ j,
        (if label j then (1 : ℝ) else -1) *
          (∑ i, residues j i / (θ i + poles j i)) > 1 / 2) :
    ∃ P A : Fin m → Fin (2 * p) → ℝ, ∃ c : Fin m → ℝ,
      (∀ j i, 0 < P j i ∧ 0 < A j i) ∧
      ∀ label : Fin m → Bool, ∃ z : Fin (2 * p) → ℝ,
        (∀ i, 0 < z i) ∧ ∀ j,
          (if label j then (1 : ℝ) else -1) *
            ((∑ i, A j i / (z i + P j i)) - c j) > 1 / 4 := by
  classical
  obtain ⟨P, A, c, hpos, hsign⟩ := completion poles residues hp hshatter
  have hc : Fintype.card (Fin p × Bool) = 2 * p := by simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨fun j i ↦ P j (e.symm i), fun j i ↦ A j (e.symm i), c,
    fun j i ↦ hpos j (e.symm i), ?_⟩
  intro label
  obtain ⟨z, hz, hs⟩ := hsign label
  refine ⟨z ∘ e.symm, fun i ↦ hz _, ?_⟩
  intro j
  have he : (∑ i, A j (e.symm i) / (z (e.symm i) + P j (e.symm i))) =
      ∑ i, A j i / (z i + P j i) :=
    e.symm.sum_comp (fun i ↦ A j i / (z i + P j i))
  simp only [Function.comp_apply]
  rw [he]
  exact hs j

/-- Even strictly decreasing, strictly convex separable reciprocal queries
can realize unboundedly many independent signs per positive parameter. The
derivative interpretation is a written consequence of the positive residues. -/
theorem unbounded_positive_tests_per_parameter (C : ℕ) :
    ∃ p m : ℕ, 0 < p ∧ C * p < m ∧
      ∃ poles residues : Fin m → Fin p → ℝ, ∃ thresholds : Fin m → ℝ,
        (∀ j i, 0 < poles j i ∧ 0 < residues j i) ∧
        ∀ label : Fin m → Bool, ∃ θ : Fin p → ℝ,
          (∀ i, 0 < θ i) ∧ ∀ j,
            (if label j then (1 : ℝ) else -1) *
              ((∑ i, residues j i / (θ i + poles j i)) - thresholds j) > 1 / 4 := by
  obtain ⟨p, m, hp, hm, poles, residues, hpos, hsign⟩ :=
    ReciprocalMatchingShattering.unbounded_tests_per_positive_parameter (2 * C)
  refine ⟨2 * p, m, by omega, ?_, completion_fin poles residues hpos hsign⟩
  convert hm using 1
  ring

#print axioms completion
#print axioms unbounded_positive_tests_per_parameter

end HeadComplexity.PositiveReciprocalShattering
