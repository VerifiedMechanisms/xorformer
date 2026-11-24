import HeadComplexity.Research.OriginalMarginCapacity
import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

/-! A full-cube parity annihilator bounds every replacement of one head and
the free bias, even when the replacement denominator is completely different. -/

noncomputable section
namespace HeadComplexity.FrozenHeadParityMargin
open scoped BigOperators

def vertex : Fin 8 → Fin 3 → Bool :=
  ![![false,false,false], ![false,false,true], ![false,true,false], ![false,true,true],
    ![true,false,false], ![true,false,true], ![true,true,false], ![true,true,true]]

def parity : Fin 3 → Bool → ℝ := fun _ b => if b then -1 else 1

def label (x : Fin 3 → Bool) : ℝ := -(parity 0 (x 0) * parity 1 (x 1) * parity 2 (x 2))

def affine (a : Fin 4 → ℝ) (x : Fin 3 → Bool) : ℝ :=
  affineValue (a 0) (fun i => a i.succ) x

/-- Three-bit parity annihilates every product of two affine forms. -/
theorem parity_affine_product_sum_zero (a b : Fin 4 → ℝ) :
    ∑ j : Fin 8, label (vertex j) * affine a (vertex j) * affine b (vertex j) = 0 := by
  norm_num [label, parity, vertex, affine, affineValue, Fin.sum_univ_succ, boolToReal]
  ring

/-- The two cleared rational scores have the same parity-weighted average.
The replacement bias is arbitrary. -/
theorem weighted_score_sum_eq (a b a' b' : Fin 4 → ℝ) (c : ℝ)
    (R : (Fin 3 → Bool) → ℝ)
    (hb : ∀ x, 0 < affine b x) (hb' : ∀ x, 0 < affine b' x) :
    (∑ j : Fin 8, (affine b (vertex j) * affine b' (vertex j)) *
      (label (vertex j) * (c + affine a' (vertex j) / affine b' (vertex j) + R (vertex j)))) =
    (∑ j : Fin 8, (affine b (vertex j) * affine b' (vertex j)) *
      (label (vertex j) * (affine a (vertex j) / affine b (vertex j) + R (vertex j)))) := by
  have hp (j : Fin 8) :
      (affine b (vertex j) * affine b' (vertex j)) *
        (label (vertex j) * (c + affine a' (vertex j) / affine b' (vertex j) + R (vertex j))) =
      (affine b (vertex j) * affine b' (vertex j)) *
        (label (vertex j) * (affine a (vertex j) / affine b (vertex j) + R (vertex j))) +
      c * (label (vertex j) * affine b (vertex j) * affine b' (vertex j)) +
      (label (vertex j) * affine a' (vertex j) * affine b (vertex j)) -
      (label (vertex j) * affine a (vertex j) * affine b' (vertex j)) := by
    field_simp [(hb (vertex j)).ne', (hb' (vertex j)).ne']
    ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, parity_affine_product_sum_zero, parity_affine_product_sum_zero,
    parity_affine_product_sum_zero]
  ring

/-- No feasible replacement of one entire affine ratio and the bias can have
minimum parity gap larger than the old score's maximum parity gap. -/
theorem gap_le_of_frozen_residual (a b a' b' : Fin 4 → ℝ) (c γ ε : ℝ)
    (R : (Fin 3 → Bool) → ℝ)
    (hb : ∀ x, 0 < affine b x) (hb' : ∀ x, 0 < affine b' x)
    (hupper : ∀ x, label x * (affine a x / affine b x + R x) ≤ ε)
    (hlower : ∀ x, γ ≤ label x * (c + affine a' x / affine b' x + R x)) :
    γ ≤ ε := by
  let w (j : Fin 8) := affine b (vertex j) * affine b' (vertex j)
  have hw : ∀ j, 0 < w j := fun j => mul_pos (hb _) (hb' _)
  have hsum : 0 < ∑ j, w j := Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty
  have hlow : (∑ j, w j) * γ ≤
      ∑ j, w j * (label (vertex j) * (c + affine a' (vertex j) / affine b' (vertex j) + R (vertex j))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hlower _) (hw j).le)
  have hupp : (∑ j, w j * (label (vertex j) *
      (affine a (vertex j) / affine b (vertex j) + R (vertex j)))) ≤ (∑ j, w j) * ε := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hupper _) (hw j).le)
  have heq := weighted_score_sum_eq a b a' b' c R hb hb'
  change (∑ j, w j * _) = (∑ j, w j * _) at heq
  rw [heq] at hlow
  have hle := hlow.trans hupp
  nlinarith

/-- Every genuine original head has the affine-ratio presentation used above;
this includes either denominator orientation and constant denominators. -/
theorem original_head_presentation (phi : FracAtom 3) :
    ∃ a b : Fin 4 → ℝ, (∀ x, 0 < affine b x) ∧
      ∀ x, phi.eval x = affine a x / affine b x := by
  let aa := OriginalMarginCapacity.numeratorCoefficients phi
  let bb := OriginalMarginCapacity.denominatorCoefficients phi
  let a : Fin 4 → ℝ := ![aa none, aa (some 0), aa (some 1), aa (some 2)]
  let b : Fin 4 → ℝ := ![bb none, bb (some 0), bb (some 1), bb (some 2)]
  have ha (x) : affine a x = CoefficientOrderChart.affineValue aa x := by
    simp [affine, affineValue, CoefficientOrderChart.affineValue, a, Fin.sum_univ_succ, mul_comm]
  have hb (x) : affine b x = CoefficientOrderChart.affineValue bb x := by
    simp [affine, affineValue, CoefficientOrderChart.affineValue, b, Fin.sum_univ_succ, mul_comm]
  refine ⟨a, b, ?_, ?_⟩
  · intro x
    rw [hb, show bb = OriginalMarginCapacity.denominatorCoefficients phi from rfl,
      OriginalMarginCapacity.affineValue_denominatorCoefficients]
    exact phi.denom_pos x
  · intro x
    rw [ha, hb]
    exact (OriginalMarginCapacity.affineRatio_eq_eval phi x).symm

/-- Original-model version. The replacement is an arbitrary admissible head. -/
theorem original_gap_le_of_frozen_residual (phi psi : FracAtom 3) (c γ ε : ℝ)
    (R : (Fin 3 → Bool) → ℝ)
    (hupper : ∀ x, label x * (phi.eval x + R x) ≤ ε)
    (hlower : ∀ x, γ ≤ label x * (c + psi.eval x + R x)) : γ ≤ ε := by
  obtain ⟨a, b, hb, hphi⟩ := original_head_presentation phi
  obtain ⟨a', b', hb', hpsi⟩ := original_head_presentation psi
  apply gap_le_of_frozen_residual a b a' b' c γ ε R hb hb'
  · intro x
    simpa [← hphi x] using hupper x
  · intro x
    simpa [← hpsi x] using hlower x

def parityFunction (x : Fin 3 → Bool) : Bool := Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

theorem signedLabel_parityFunction (x : Fin 3 → Bool) :
    signedLabel parityFunction x = label x := by
  unfold signedLabel parityFunction label parity
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> norm_num

/-- The same obstruction holds for the requested relative margin, using norms
on the entire Boolean cube. No restriction is placed on the replacement head. -/
theorem relativeMargin_le_of_frozen_heads {H : ℕ} (phi psi : FracAtom 3)
    (rest : Fin H → FracAtom 3) (c ε : ℝ)
    (hupper : ∀ x, label x * (phi.eval x + ∑ h, (rest h).eval x) ≤ ε)
    (hnorm : 1 ≤ ∑ h, RelativeMarginQuantifiers.atomSup (rest h))
    (hstrict : RelativeMarginQuantifiers.StrictlyRepresents parityFunction
      (Fin.cases psi rest) c) :
    RelativeMarginQuantifiers.relativeMargin parityFunction (Fin.cases psi rest) c ≤ ε := by
  let heads : Fin (H + 1) → FracAtom 3 := Fin.cases psi rest
  let γ := RelativeMarginQuantifiers.relativeMargin parityFunction heads c
  have hγ : 0 < γ := RelativeMarginQuantifiers.relativeMargin_pos hstrict
  have hgap := (RelativeMarginQuantifiers.le_relativeMargin_iff hstrict).mp
    (show γ ≤ RelativeMarginQuantifiers.relativeMargin parityFunction heads c from le_rfl)
  have hbound : γ * RelativeMarginQuantifiers.amplitude heads c ≤ ε := by
    apply original_gap_le_of_frozen_residual phi psi c
      (γ * RelativeMarginQuantifiers.amplitude heads c) ε
      (fun x => ∑ h, (rest h).eval x) hupper
    intro x
    simpa [RelativeMarginQuantifiers.score, heads, Fin.sum_univ_succ,
      signedLabel_parityFunction, add_assoc] using hgap x
  have hamp : 1 ≤ RelativeMarginQuantifiers.amplitude heads c := by
    simp only [RelativeMarginQuantifiers.amplitude, heads, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ]
    linarith [abs_nonneg c, RelativeMarginQuantifiers.atomSup_nonneg psi]
  change γ ≤ ε
  exact (le_mul_of_one_le_right hγ.le hamp).trans hbound

end HeadComplexity.FrozenHeadParityMargin
