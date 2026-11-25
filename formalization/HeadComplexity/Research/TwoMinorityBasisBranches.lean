import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

/-!
Two open sets of admissible one-head denominator parameters have the same
actual full-rank unit-value sample basis and different full Boolean tables.
The strict residual inequalities explicitly witness full-dimensional feasibility.
-/

noncomputable section
namespace HeadComplexity.TwoMinorityBasisBranches
open scoped BigOperators

def matrix : Fin 8 → Fin 8 → ℝ := ![![-1, -2, -2, 0, 0, -2, 0, -2], ![-4, -3, -2, -2, -2, -2, 0, -4], ![6, 6, 5, 2, 2, 4, 0, 6], ![2, 2, 2, 1, 0, 2, 0, 2], ![2, 2, 2, 0, 1, 2, 0, 2], ![-2, -2, -2, 0, 0, -1, 0, -2], ![4, 4, 2, 2, 2, 2, 1, 4], ![0, 0, 0, 0, 0, 0, 0, 1]]

def transform (b : Fin 8 → ℝ) (i : Fin 8) : ℝ := ∑ j, matrix i j * b j

def affine (c : Fin 8 → ℝ) (x : Fin 7 → Bool) : ℝ :=
  affineValue (c 0) (fun i => c i.succ) x

def baseDenominator : Fin 2 → Fin 8 → ℝ := ![![2, 2, 9, 6, 6, 2, 2, 2], ![2, 2, 11, 2, 2, 2, 2, 2]]

def baseNumerator : Fin 2 → Fin 8 → ℝ := ![![-32, -68, 113, 40, 40, -32, 72, 2], ![-36, -56, 107, 40, 40, -36, 60, 2]]

def basisPoint : Fin 8 → Fin 7 → Bool := ![![true, false, true, false, false, true, true], ![false, false, true, true, true, false, true], ![true, true, false, false, true, false, true], ![true, false, true, true, false, false, true], ![false, false, false, true, false, false, true], ![true, true, false, true, true, false, true], ![true, true, true, false, true, false, false], ![true, true, false, false, false, false, true]]

def basisValue : Fin 8 → ℝ := ![1, 1, -1, -1, 1, 1, 1, 1]

def structuralPoint : Fin 20 → Fin 7 → Bool := ![![false, false, false, true, false, false, false], ![false, false, false, true, false, false, true], ![false, false, true, false, false, false, false], ![false, false, true, false, false, false, true], ![false, false, true, true, true, false, false], ![false, false, true, true, true, false, true], ![true, false, false, true, false, true, false], ![true, false, false, true, false, true, true], ![true, false, true, false, false, true, false], ![true, false, true, false, false, true, true], ![true, false, true, true, false, false, true], ![true, false, true, true, true, true, false], ![true, false, true, true, true, true, true], ![true, true, false, false, false, false, false], ![true, true, false, false, false, false, true], ![true, true, false, false, true, false, true], ![true, true, false, true, true, false, false], ![true, true, false, true, true, false, true], ![true, true, true, false, true, false, false], ![true, true, true, false, true, false, true]]

def IsStructural (x : Fin 7 → Bool) : Prop := ∃ j, structuralPoint j = x

instance (x : Fin 7 → Bool) : Decidable (IsStructural x) := inferInstanceAs (Decidable (∃ j, structuralPoint j = x))

def label (k : Fin 2) (x : Fin 7 → Bool) : ℝ :=
  if 0 < affine (baseNumerator k) x then 1 else -1

def residual (k : Fin 2) (x : Fin 7 → Bool) (b : Fin 8 → ℝ) : ℝ :=
  label k x * affine (transform b) x - affine b x

def neighborhood (k : Fin 2) : Set (Fin 8 → ℝ) :=
  {b | (∀ i, 0 < b i) ∧ ∀ x, ¬ IsStructural x → 0 < residual k x b}

theorem transform_base (k : Fin 2) : transform (baseDenominator k) = baseNumerator k := by
  funext i
  fin_cases k <;> fin_cases i <;>
    norm_num [transform, matrix, baseDenominator, baseNumerator, Fin.sum_univ_succ]

theorem baseDenominator_pos (k : Fin 2) (i : Fin 8) : 0 < baseDenominator k i := by
  fin_cases k <;> fin_cases i <;> norm_num [baseDenominator]

theorem basis_identity (b : Fin 8 → ℝ) (j : Fin 8) :
    affine (transform b) (basisPoint j) = basisValue j * affine b (basisPoint j) := by
  fin_cases j <;>
    norm_num [affine, affineValue, transform, matrix, basisPoint, basisValue,
      Fin.sum_univ_succ, boolToReal] <;> ring

set_option maxHeartbeats 2000000 in
-- Expanding twenty structural Boolean rows is a finite exact arithmetic proof.
theorem structural_identity (k : Fin 2) (x : Fin 7 → Bool)
    (hx : IsStructural x) (b : Fin 8 → ℝ) : residual k x b = 0 := by
  obtain ⟨j, rfl⟩ := hx
  fin_cases k <;> fin_cases j <;>
    norm_num [residual, label, structuralPoint, affine, affineValue, transform,
      matrix, baseNumerator, Fin.sum_univ_succ, boolToReal] <;> ring

set_option maxHeartbeats 8000000 in
-- Exhaust the 128 Boolean rows for each of the two exact parameter points.
theorem base_strict_residual (k : Fin 2) (x : Fin 7 → Bool)
    (hx : ¬ IsStructural x) : 0 < residual k x (baseDenominator k) := by
  unfold residual
  rw [transform_base]
  have hvec : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec] at hx ⊢
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4,
    x 5 = b5, x 6 = b6 at hx ⊢
  fin_cases k <;> cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;>
    norm_num [label, baseNumerator, baseDenominator, affine, affineValue,
      Fin.sum_univ_succ, boolToReal, IsStructural, structuralPoint, Fin.exists_fin_succ] at hx <;>
    norm_num [label, baseNumerator, baseDenominator, affine, affineValue,
      Fin.sum_univ_succ, boolToReal]

theorem continuous_residual (k : Fin 2) (x : Fin 7 → Bool) :
    Continuous (residual k x) := by
  unfold residual affine affineValue transform
  fun_prop

theorem neighborhood_isOpen (k : Fin 2) : IsOpen (neighborhood k) := by
  have hp : IsOpen {b : Fin 8 → ℝ | ∀ i, 0 < b i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hr : IsOpen {b : Fin 8 → ℝ | ∀ x, ¬ IsStructural x → 0 < residual k x b} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun x => ?_
    by_cases hx : IsStructural x
    · simp [hx]
    · simpa [hx] using isOpen_lt continuous_const (continuous_residual k x)
  exact hp.inter hr

theorem base_mem_neighborhood (k : Fin 2) : baseDenominator k ∈ neighborhood k :=
  ⟨baseDenominator_pos k, fun x hx => base_strict_residual k x hx⟩

theorem neighborhood_signed_gap (k : Fin 2) (b : Fin 8 → ℝ)
    (hb : b ∈ neighborhood k) (x : Fin 7 → Bool) :
    1 ≤ label k x * (affine (transform b) x / affine b x) := by
  have hd : 0 < affine b x := affineValue_pos (b 0) (fun i => b i.succ)
    (hb.1 0) (fun i => hb.1 i.succ) x
  have hr : 0 ≤ residual k x b := by
    by_cases hx : IsStructural x
    · rw [structural_identity k x hx b]
    · exact (hb.2 x hx).le
  unfold residual at hr
  rw [← mul_div_assoc, le_div_iff₀ hd]
  simpa using sub_nonneg.mp hr

def atom (b : Fin 8 → ℝ) (hb : ∀ i, 0 < b i) : FracAtom 7 :=
  FracAtom.ofPositiveAffineRatio (transform b 0) (fun i => transform b i.succ)
    (b 0) (fun i => b i.succ) (hb 0) (fun i => hb i.succ)

theorem atom_eval (b : Fin 8 → ℝ) (hb : ∀ i, 0 < b i) (x : Fin 7 → Bool) :
    (atom b hb).eval x = affine (transform b) x / affine b x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x

theorem neighborhood_basis_values (k : Fin 2) (b : Fin 8 → ℝ)
    (hb : b ∈ neighborhood k) (j : Fin 8) :
    (atom b hb.1).eval (basisPoint j) = basisValue j := by
  rw [atom_eval, basis_identity]
  have hd : affine b (basisPoint j) ≠ 0 :=
    (affineValue_pos (b 0) (fun i => b i.succ) (hb.1 0)
      (fun i => hb.1 i.succ) (basisPoint j)).ne'
  exact mul_div_cancel_right₀ _ hd

/-- The selected actual cube rows are a full affine basis. -/
theorem basis_affine_injective (c d : Fin 8 → ℝ)
    (h : ∀ j, affine c (basisPoint j) = affine d (basisPoint j)) : c = d := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  norm_num [affine, affineValue, basisPoint, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7
  ext i
  fin_cases i <;> norm_num only [Fin.mk_zero, Fin.reduceFinMk]
  · linear_combination (-1) * h1 + (1) * h2 + (2) * h4 + (-1) * h5 + (1) * h6 + (-1) * h7
  · linear_combination (-1) * h1 + (1) * h2 + (1) * h3 + (-1) * h7
  · linear_combination (1) * h1 + (-2) * h2 + (-1) * h3 + (-1) * h4 + (1) * h5 + (2) * h7
  · linear_combination (1) * h1 + (-1) * h2 + (-1) * h4 + (1) * h7
  · linear_combination (-1) * h2 + (1) * h5
  · linear_combination (1) * h2 + (-1) * h7
  · linear_combination (1) * h0 + (-1) * h2 + (-1) * h3 + (1) * h5
  · linear_combination (1) * h1 + (-1) * h4 + (-1) * h6 + (1) * h7

/-- Dividing every actual sample row by its positive denominator preserves rank. -/
theorem basis_ratio_injective (b : Fin 8 → ℝ) (hb : ∀ i, 0 < b i)
    (c d : Fin 8 → ℝ)
    (h : ∀ j, affine c (basisPoint j) / affine b (basisPoint j) =
      affine d (basisPoint j) / affine b (basisPoint j)) : c = d := by
  apply basis_affine_injective
  intro j
  have hd := (affineValue_pos (b 0) (fun i => b i.succ)
    (hb 0) (fun i => hb i.succ) (basisPoint j)).ne'
  exact (div_left_inj' hd).mp (h j)

theorem label_disagreement :
    label 0 ![false,false,false,false,true,true,false] = 1 ∧
    label 1 ![false,false,false,false,true,true,false] = -1 := by
  norm_num [label, affine, affineValue, baseNumerator, Fin.sum_univ_succ, boolToReal]

/-- The two feasible branches are disjoint, nonempty open subsets of the full
eight-dimensional positive denominator parameter space. -/
theorem two_open_feasible_branches :
    IsOpen (neighborhood 0) ∧ IsOpen (neighborhood 1) ∧
    (neighborhood 0).Nonempty ∧ (neighborhood 1).Nonempty ∧
    Disjoint (neighborhood 0) (neighborhood 1) := by
  refine ⟨neighborhood_isOpen 0, neighborhood_isOpen 1,
    ⟨_, base_mem_neighborhood 0⟩, ⟨_, base_mem_neighborhood 1⟩, ?_⟩
  rw [Set.disjoint_left]
  intro b h0 h1
  have q0 := neighborhood_signed_gap 0 b h0 ![false,false,false,false,true,true,false]
  have q1 := neighborhood_signed_gap 1 b h1 ![false,false,false,false,true,true,false]
  rw [label_disagreement.1] at q0
  rw [label_disagreement.2] at q1
  linarith

theorem exactly_two_negative_contacts (j : Fin 8) :
    basisValue j = -1 ↔ j = 2 ∨ j = 3 := by
  fin_cases j <;> norm_num [basisValue]

theorem same_difference_coefficient_signs (i : Fin 8) :
    ((0 < baseDenominator 0 i - baseNumerator 0 i) ↔
      (0 < baseDenominator 1 i - baseNumerator 1 i)) ∧
    ((baseDenominator 0 i - baseNumerator 0 i = 0) ↔
      (baseDenominator 1 i - baseNumerator 1 i = 0)) := by
  fin_cases i <;> norm_num [baseDenominator, baseNumerator]

/-- At a negative unit contact, an equal positive comparison level cannot occur
at a point with a strictly larger denominator. -/
theorem negative_contact_difference_strict (Aq Bq Ax Bx : ℝ)
    (_hBq : 0 < Bq) (hinc : Bq < Bx) (hq : Aq = -Bq)
    (hgap : Bx ≤ |Ax|) (hcomparison : 0 < Bx - Ax) :
    Bq - Aq < Bx - Ax := by
  have hAx : Ax < 0 := by
    by_contra h
    have hn : 0 ≤ Ax := le_of_not_gt h
    rw [abs_of_nonneg hn] at hgap
    linarith
  rw [abs_of_neg hAx] at hgap
  linarith

theorem equal_difference_impossible (Aq Bq Ax Bx : ℝ)
    (hBq : 0 < Bq) (hinc : Bq < Bx) (hq : Aq = -Bq)
    (hgap : Bx ≤ |Ax|) (heq : Bx - Ax = Bq - Aq) : False := by
  have hc : 0 < Bx - Ax := by rw [heq, hq]; linarith
  have hs := negative_contact_difference_strict Aq Bq Ax Bx hBq hinc hq hgap hc
  linarith

end HeadComplexity.TwoMinorityBasisBranches
