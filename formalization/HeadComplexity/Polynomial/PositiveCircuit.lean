import HeadComplexity.Atoms.ClearedFeatureMatrix
import HeadComplexity.Results.AffineFreeSparsity

set_option linter.style.header false

/-!
# Integral positive-circuit obstructions

A nonzero nonnegative weight vector which annihilates every signed squarefree
monomial through degree `d` is an exact obstruction to threshold degree at
most `d`.  The certificate equations are integral, while the contradiction is
proved for arbitrary real sign polynomials.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n d : ℕ} {f : (Fin n → Bool) → Bool}

/-- The integral sign attached to a Boolean label. -/
def integralLabelSign (label : Bool) : ℤ :=
  if label then 1 else -1

/-- Integral evaluation of a squarefree monomial on the Boolean cube. -/
def integralSquarefreeMonomial (S : Finset (Fin n))
    (bits : Fin n → Bool) : ℤ :=
  ∏ i ∈ S, semiringBitValue (R := ℤ) (bits i)

/-- An exact nonnegative circuit annihilating every signed monomial through a
specified degree. -/
structure IntegralPositiveCircuit
    (f : (Fin n → Bool) → Bool) (d : ℕ) where
  weight : (Fin n → Bool) → ℕ
  nonzero : ∃ bits, 0 < weight bits
  moment : ∀ S : Finset (Fin n), S.card ≤ d →
    ∑ bits, (weight bits : ℤ) * integralLabelSign (f bits) *
      integralSquarefreeMonomial S bits = 0

namespace IntegralPositiveCircuit

private def realLabelSign (label : Bool) : ℝ :=
  if label then 1 else -1

private theorem cast_integralSquarefreeMonomial
    (S : Finset (Fin n)) (bits : Fin n → Bool) :
    (integralSquarefreeMonomial S bits : ℝ) =
      squarefreeMonomial S bits := by
  simp only [integralSquarefreeMonomial, squarefreeMonomial, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases bits i <;> norm_num [semiringBitValue, boolToReal]

private theorem cast_integralLabelSign (label : Bool) :
    (integralLabelSign label : ℝ) = realLabelSign label := by
  cases label <;> norm_num [integralLabelSign, realLabelSign]

/-- The checked integer identities imply the corresponding real moment
identities used by polynomial evaluation. -/
theorem real_moment (C : IntegralPositiveCircuit f d)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    ∑ bits, (C.weight bits : ℝ) * realLabelSign (f bits) *
      squarefreeMonomial S bits = 0 := by
  have hcast := congrArg (fun z : ℤ ↦ (z : ℝ)) (C.moment S hS)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    cast_integralLabelSign, cast_integralSquarefreeMonomial, Int.cast_zero]
    using hcast

private theorem weighted_eval_eq_zero
    (C : IntegralPositiveCircuit f d) (P : SquarefreePolynomial n)
    (hPdeg : P.DegreeLE d) :
    ∑ bits, (C.weight bits : ℝ) * realLabelSign (f bits) * P.eval bits = 0 := by
  classical
  simp_rw [← P.fullSum_eq_eval]
  simp_rw [mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hcoeff : P.coeff S = 0
  · simp [hcoeff]
  · calc
      (∑ bits,
          (C.weight bits : ℝ) * realLabelSign (f bits) *
            (P.coeff S * squarefreeMonomial S bits)) =
          P.coeff S *
            ∑ bits, (C.weight bits : ℝ) * realLabelSign (f bits) *
              squarefreeMonomial S bits := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro bits _
                ring
      _ = 0 := by rw [C.real_moment S (hPdeg S hcoeff), mul_zero]

private theorem signed_eval_pos
    (P : SquarefreePolynomial n) (hP : P.StrictSignRepresents f)
    (bits : Fin n → Bool) :
    0 < realLabelSign (f bits) * P.eval bits := by
  cases hlabel : f bits with
  | false =>
      have hnpos : ¬ 0 < P.eval bits := by
        intro hpos
        have htrue := (hP bits).1.mp hpos
        rw [hlabel] at htrue
        exact Bool.false_ne_true htrue
      have hneg : P.eval bits < 0 :=
        lt_of_le_of_ne (not_lt.mp hnpos) (hP bits).2
      simp [realLabelSign]
      linarith
  | true =>
      have hpos : 0 < P.eval bits := (hP bits).1.mpr hlabel
      simpa [realLabelSign] using hpos

/-- **Positive-circuit alternative.** No degree-at-most-`d` real polynomial
can strictly sign-represent a function carrying such a circuit. -/
theorem not_thresholdDegLE (C : IntegralPositiveCircuit f d) :
    ¬ ThresholdDegLE f d := by
  intro hdeg
  obtain ⟨P, hPdeg, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE hdeg
  obtain ⟨chosen, hchosen⟩ := C.nonzero
  have hall : ∀ bits,
      0 ≤ (C.weight bits : ℝ) * realLabelSign (f bits) * P.eval bits := by
    intro bits
    rw [mul_assoc]
    exact mul_nonneg (Nat.cast_nonneg _) (signed_eval_pos P hP bits).le
  have hone :
      0 < (C.weight chosen : ℝ) * realLabelSign (f chosen) * P.eval chosen := by
    rw [mul_assoc]
    exact mul_pos (by exact_mod_cast hchosen) (signed_eval_pos P hP chosen)
  have hsumpos :
      0 < ∑ bits, (C.weight bits : ℝ) * realLabelSign (f bits) * P.eval bits := by
    apply Finset.sum_pos' (fun bits _ ↦ hall bits)
    exact ⟨chosen, Finset.mem_univ chosen, hone⟩
  exact (ne_of_gt hsumpos) (C.weighted_eval_eq_zero P hPdeg)

/-- The circuit gives a strict lower bound on the minimum threshold degree. -/
theorem lt_thresholdDeg (C : IntegralPositiveCircuit f d) :
    d < thresholdDeg f := by
  by_contra hnot
  push Not at hnot
  obtain ⟨P, hPdeg, hP⟩ := thresholdDeg_spec f
  exact C.not_thresholdDegLE ⟨P, hPdeg.trans hnot, hP⟩

end IntegralPositiveCircuit

end HeadComplexity
