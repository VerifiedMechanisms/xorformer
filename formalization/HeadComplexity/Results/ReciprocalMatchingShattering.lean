import HeadComplexity.Atoms.ReciprocalLevelSelector
import HeadComplexity.Results.FiniteFieldLines

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-! Hall matchings and paired reciprocal level selectors yield an unbounded
number of independent free-query sign tests per positive parameter.
This does not prove any worst-case attention-head lower bound. -/

namespace HeadComplexity.ReciprocalMatchingShattering

open Finset ReciprocalLevelSelector

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

noncomputable def index (k : K) : ℕ := (Fintype.equivFin K k).val + 1

omit [DecidableEq K] in
theorem index_positive (k : K) : 0 < index k := by
  unfold index
  omega

omit [DecidableEq K] in
theorem index_injective : Function.Injective (index : K → ℕ) := by
  intro k l h
  apply (Fintype.equivFin K).injective
  apply Fin.ext
  unfold index at h
  omega

noncomputable def assignment (f : K → I) (i : I) : ℕ :=
  if h : ∃ k, f k = i then index (Classical.choose h) else 0

omit [Fintype I] [DecidableEq K] in
theorem assignment_self (f : K → I) (hf : Function.Injective f) (k : K) :
    assignment f (f k) = index k := by
  unfold assignment
  split_ifs with h
  · have he : Classical.choose h = k := hf (Classical.choose_spec h)
    rw [he]
  · exact False.elim (h ⟨k, rfl⟩)

omit [Fintype I] [DecidableEq K] in
theorem assignment_eq_iff (f : K → I) (hf : Function.Injective f) (k : K) (i : I) :
    assignment f i = index k ↔ i = f k := by
  constructor
  · intro he
    unfold assignment at he
    split_ifs at he with h
    · have hk : Classical.choose h = k := index_injective he
      simpa only [hk] using (Classical.choose_spec h).symm
    · have hp := index_positive k
      omega
  · intro he
    subst i
    exact assignment_self f hf k

omit [DecidableEq K] in
theorem selected_sum (f : K → I) (hf : Function.Injective f) (k : K) (w : I → ℝ) :
    (∑ i, w i * if assignment f i = index k then 1 else 0) = w (f k) := by
  simp only [assignment_eq_iff f hf k]
  simp

omit [DecidableEq K] in
theorem selected_error (f : K → I) (hf : Function.Injective f) (k : K)
    (w : I → ℝ) (hw : ∀ i, |w i| = 1) :
    |(∑ i, w i * bump (4 * (Fintype.card I : ℝ) + 1) (index k) (assignment f i)) -
      w (f k)| < 1 / 2 := by
  let R : ℝ := 4 * (Fintype.card I : ℝ) + 1
  have hL : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hRp : 0 < R + 1 := by linarith
  have hsum := selected_sum f hf k w
  have heq : (∑ i, w i * bump R (index k) (assignment f i)) - w (f k) =
      ∑ i, w i * (bump R (index k) (assignment f i) -
        if assignment f i = index k then 1 else 0) := by
    rw [← hsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change |(∑ i, w i * bump R (index k) (assignment f i)) - w (f k)| < 1 / 2
  rw [heq]
  calc
    _ ≤ ∑ i, |w i * (bump R (index k) (assignment f i) -
        if assignment f i = index k then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, 2 / (R + 1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, hw, one_mul]
      exact bump_error hR _ _
    _ = (Fintype.card I : ℝ) * (2 / (R + 1)) := by simp
    _ < 1 / 2 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hh : (4 * (Fintype.card I : ℝ)) / (R + 1) < 1 := by
        apply (div_lt_iff₀ hRp).mpr
        dsimp [R]
        linarith
      convert hh using 1
      ring

omit [DecidableEq I] [DecidableEq K] in
theorem of_independent_choices (b : ℕ) (color : K → I → (Fin b → Bool))
    (hselect : ∀ target : K → (Fin b → Bool), ∃ f : K → I,
      Function.Injective f ∧ ∀ k, color k (f k) = target k) :
    ∃ poles residues : (K × Fin b) → (I × Bool) → ℝ,
      (∀ j i, 0 < poles j i) ∧
      ∀ label : K × Fin b → Bool, ∃ θ : I × Bool → ℝ,
        (∀ i, 0 < θ i) ∧ ∀ j,
          (if label j then (1 : ℝ) else -1) *
            (∑ i, residues j i / (θ i + poles j i)) > 1 / 2 := by
  classical
  let R : ℝ := 4 * (Fintype.card I : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let w : (K × Fin b) → I → ℝ := fun j i ↦ if color j.1 i j.2 then 1 else -1
  let poles : (K × Fin b) → (I × Bool) → ℝ := fun j i ↦
    if i.2 then R ^ (2 * index j.1 + 2) else R ^ (2 * index j.1)
  let residues : (K × Fin b) → (I × Bool) → ℝ := fun j i ↦
    if i.2 then w j i.1 * poles j i else -(w j i.1 * poles j i)
  refine ⟨poles, residues, ?_, ?_⟩
  · intro j i
    dsimp [poles]
    split <;> positivity
  · intro label
    obtain ⟨f, hf, hfc⟩ := hselect (fun k bit ↦ label (k, bit))
    let θ : I × Bool → ℝ := fun i ↦ R ^ (2 * assignment f i.1 + 1)
    refine ⟨θ, fun i ↦ pow_pos hR _, ?_⟩
    intro j
    have heval : (∑ i, residues j i / (θ i + poles j i)) =
        ∑ i, w j i * bump R (index j.1) (assignment f i) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      dsimp [residues, poles, θ, bump]
      ring
    have hw (i : I) : |w j i| = 1 := by
      dsimp [w]
      split <;> norm_num
    have hselected : w j (f j.1) = if label j then 1 else -1 := by
      dsimp [w]
      rw [hfc]
    have herr := selected_error f hf j.1 (w j) hw
    change |(∑ i, w j i * bump R (index j.1) (assignment f i)) - w j (f j.1)| <
      1 / 2 at herr
    rw [hselected] at herr
    rw [heval]
    obtain ⟨hupper, hlower⟩ := abs_sub_lt_iff.mp herr
    cases hlabel : label j <;> simp only [hlabel, Bool.false_eq_true, ite_false,
      ite_true, neg_mul, one_mul] at hupper hlower ⊢ <;> linarith

#print axioms of_independent_choices

theorem finite_field_queries (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (r b : ℕ) (hr : 2 * r ≤ Fintype.card F) (encode : F ≃ (Fin b → Bool)) :
    ∃ poles residues : ((FiniteFieldLines.Direction F × Fin r) × Fin b) →
        (FiniteFieldLines.Point F × Bool) → ℝ,
      (∀ j i, 0 < poles j i) ∧
      ∀ label : (FiniteFieldLines.Direction F × Fin r) × Fin b → Bool,
        ∃ θ : FiniteFieldLines.Point F × Bool → ℝ,
          (∀ i, 0 < θ i) ∧ ∀ j,
            (if label j then (1 : ℝ) else -1) *
              (∑ i, residues j i / (θ i + poles j i)) > 1 / 2 := by
  classical
  apply of_independent_choices b
    (fun k i ↦ encode (FiniteFieldLines.color F r k i))
  intro target
  obtain ⟨f, hf, hfc⟩ := FiniteFieldLines.exists_representatives F r hr
    (fun k ↦ encode.symm (target k))
  refine ⟨f, hf, ?_⟩
  intro k
  rw [hfc, Equiv.apply_symm_apply]

theorem finite_field_queries_fin (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (r b : ℕ) (hr : 2 * r ≤ Fintype.card F) (encode : F ≃ (Fin b → Bool)) :
    ∃ poles residues : Fin ((Fintype.card F + 1) * r * b) →
        Fin (2 * Fintype.card F ^ 2) → ℝ,
      (∀ j i, 0 < poles j i) ∧
      ∀ label : Fin ((Fintype.card F + 1) * r * b) → Bool,
        ∃ θ : Fin (2 * Fintype.card F ^ 2) → ℝ,
          (∀ i, 0 < θ i) ∧ ∀ j,
            (if label j then (1 : ℝ) else -1) *
              (∑ i, residues j i / (θ i + poles j i)) > 1 / 2 := by
  classical
  obtain ⟨poles, residues, hp, hshatter⟩ := finite_field_queries F r b hr encode
  have hI : Fintype.card (FiniteFieldLines.Point F × Bool) =
      2 * Fintype.card F ^ 2 := by
    rw [Fintype.card_prod, FiniteFieldLines.card_point]
    simp [mul_comm]
  have hJ : Fintype.card ((FiniteFieldLines.Direction F × Fin r) × Fin b) =
      (Fintype.card F + 1) * r * b := by
    simp only [Fintype.card_prod, FiniteFieldLines.card_direction, Fintype.card_fin]
  let eI := Fintype.equivFinOfCardEq hI
  let eJ := Fintype.equivFinOfCardEq hJ
  refine ⟨fun j i ↦ poles (eJ.symm j) (eI.symm i),
    fun j i ↦ residues (eJ.symm j) (eI.symm i), fun j i ↦ hp _ _, ?_⟩
  intro label
  obtain ⟨θ, hθ, hsign⟩ := hshatter (label ∘ eJ)
  refine ⟨θ ∘ eI.symm, fun i ↦ hθ _, ?_⟩
  intro j
  have he : (∑ i, residues (eJ.symm j) (eI.symm i) /
      (θ (eI.symm i) + poles (eJ.symm j) (eI.symm i))) =
      ∑ i, residues (eJ.symm j) i / (θ i + poles (eJ.symm j) i) :=
    eI.symm.sum_comp (fun i ↦ residues (eJ.symm j) i / (θ i + poles (eJ.symm j) i))
  simp only [Function.comp_apply]
  rw [he]
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hsign (eJ.symm j)

/-- Arbitrarily many free reciprocal sign tests per positive parameter.
The poles are positive and the witnesses have uniform strict signed margin.
No full Boolean-cube head-complexity lower bound is asserted. -/
theorem unbounded_tests_per_positive_parameter (C : ℕ) :
    ∃ p m : ℕ, 0 < p ∧ C * p < m ∧
      ∃ poles residues : Fin m → Fin p → ℝ,
        (∀ j i, 0 < poles j i) ∧
        ∀ label : Fin m → Bool, ∃ θ : Fin p → ℝ,
          (∀ i, 0 < θ i) ∧ ∀ j,
            (if label j then (1 : ℝ) else -1) *
              (∑ i, residues j i / (θ i + poles j i)) > 1 / 2 := by
  classical
  let b := 4 * C + 4
  let r := 2 ^ (4 * C + 3)
  let q := 2 ^ b
  let F := GaloisField 2 b
  let : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 b (by dsimp [b]; omega)
  have hqr : q = 2 * r := by
    dsimp [q, b, r]
    rw [show 4 * C + 4 = (4 * C + 3) + 1 by omega, pow_succ]
    ring
  have hrpos : 0 < r := by dsimp [r]; positivity
  let encode : F ≃ (Fin b → Bool) := Fintype.equivOfCardEq (by simp [hq, q])
  have h := finite_field_queries_fin F r b (by omega) encode
  refine ⟨2 * q ^ 2, (q + 1) * r * b, ?_, ?_, ?_⟩
  · rw [hqr]
    positivity
  · dsimp [b]
    rw [hqr]
    nlinarith [sq_pos_of_pos hrpos]
  · rw [hq] at h
    exact h

#print axioms finite_field_queries_fin
#print axioms unbounded_tests_per_positive_parameter

end HeadComplexity.ReciprocalMatchingShattering
