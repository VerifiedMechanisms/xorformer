import HeadComplexity.Atoms.AtomicMargin
import HeadComplexity.Atoms.ClearedNormalForm

set_option linter.style.header false

/-! A bounded score is a rational approximant of the same degree as its number
of heads. The approximation-hardness premise below is explicit. In particular,
this file does not formalize or assume an unconditional head lower bound. -/
namespace HeadComplexity.BoundedAmplitude
open scoped BigOperators
open MvPolynomial

theorem interval_rescaling {y s M : ℝ} (hy : y = 1 ∨ y = -1)
    (hl : 1 ≤ y*s) (hu : y*s ≤ M) :
    |y - 2*s/(M+1)| ≤ (M-1)/(M+1) := by
  have hM : 1 ≤ M := hl.trans hu
  have hd : 0 < M+1 := by linarith
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_left₀ hd).mp
    rcases hy with rfl | rfl <;> simp only [one_mul, neg_one_mul] at hl hu ⊢ <;>
      field_simp <;> nlinarith
  · apply (mul_le_mul_iff_left₀ hd).mp
    rcases hy with rfl | rfl <;> simp only [one_mul, neg_one_mul] at hl hu ⊢ <;>
      field_simp <;> nlinarith

/-- A uniform approximation certificate; both degrees are bounded separately. -/
theorem bounded_margin_rational_certificate {n H : ℕ}
    (phi : Fin H → FracAtom n) (c M : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hl : ∀ x, 1 ≤ signedLabel f x * (c + ∑ h, (phi h).eval x))
    (hu : ∀ x, signedLabel f x * (c + ∑ h, (phi h).eval x) ≤ M) :
    ∃ P Q : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ H ∧ Q.totalDegree ≤ H ∧
      (∀ x, 0 < eval (cubePoint x) Q) ∧
      (∀ x, |signedLabel f x - eval (cubePoint x) P / eval (cubePoint x) Q|
        ≤ (M-1)/(M+1)) := by
  let P := C (2/(M+1)) * clearedAtomPoly phi c
  let Q := atomDenProduct phi
  refine ⟨P, Q, ?_, atomDenProduct_totalDegree_le phi,
    atomDenProduct_eval_pos phi, ?_⟩
  · exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, Nat.zero_add] using
        clearedAtomPoly_totalDegree_le phi c)
  · intro x
    have hQ : eval (cubePoint x) Q ≠ 0 := (atomDenProduct_eval_pos phi x).ne'
    have he : eval (cubePoint x) P / eval (cubePoint x) Q =
        2*(c + ∑ h, (phi h).eval x)/(M+1) := by
      dsimp [P, Q]
      rw [map_mul, eval_C, clearedAtomPoly_eval]
      dsimp [Q] at hQ
      field_simp
    rw [he]
    apply interval_rescaling ?_ (hl x) (hu x)
    unfold signedLabel
    split <;> simp

/-- Explicit hardness premise, without a claim that it holds for every label. -/
def RationalApproximationHard {n : ℕ} (f : (Fin n → Bool) → Bool)
    (d : ℕ) (e : ℝ) : Prop :=
  ∀ P Q : MvPolynomial (Fin n) ℝ,
    P.totalDegree ≤ d → Q.totalDegree ≤ d →
    (∀ x, 0 < eval (cubePoint x) Q) →
    ∃ x, e < |signedLabel f x - eval (cubePoint x) P / eval (cubePoint x) Q|

/-- Rational approximation hardness forces a large output-to-margin ratio.
External hardness results can instantiate `hhard`; it is not proved here. -/
theorem amplitude_ratio_obstruction {n H : ℕ}
    (phi : Fin H → FracAtom n) (c M delta : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hhard : RationalApproximationHard f H (1-delta))
    (hl : ∀ x, 1 ≤ signedLabel f x * (c + ∑ h, (phi h).eval x))
    (hu : ∀ x, signedLabel f x * (c + ∑ h, (phi h).eval x) ≤ M) :
    2 < delta*(M+1) := by
  obtain ⟨P, Q, hp, hq, hpos, herr⟩ :=
    bounded_margin_rational_certificate phi c M f hl hu
  obtain ⟨x, hx⟩ := hhard P Q hp hq hpos
  have hlt := hx.trans_le (herr x)
  have hM : 1 ≤ M := (hl (fun _ ↦ false)).trans (hu (fun _ ↦ false))
  have hd : 0 < M+1 := by linarith
  have hm := (lt_div_iff₀ hd).mp hlt
  nlinarith

#print axioms interval_rescaling
#print axioms bounded_margin_rational_certificate
#print axioms amplitude_ratio_obstruction
end HeadComplexity.BoundedAmplitude
