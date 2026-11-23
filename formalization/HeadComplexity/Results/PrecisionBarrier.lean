import HeadComplexity.Results.CountingLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.header false

/-!
# Finite precision is a necessary resource for head compression

These are finite counting obstructions, not bounds on unrestricted real heads.
The alphabet must be fixed independently of the target truth table. In
particular, the results do not assign a bit length to an arbitrary real number.
The eventual asymptotic propositions at the end are definitions only.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

/-- Any finite set of deterministic strict-sign decoders that realizes all
Boolean tables needs at least one code per table. No regularity assumption on
the decoder is needed. -/
theorem two_pow_card_le_card_of_strict_universal
    {I E : Type*} [Fintype I] [Fintype E]
    (score : E → I → ℝ)
    (huniversal : ∀ f : I → Bool, ∃ e : E, ∀ i,
      if f i then 0 < score e i else score e i < 0) :
    2 ^ Fintype.card I ≤ Fintype.card E := by
  classical
  choose encode hencode using huniversal
  have hinjective : Function.Injective encode := by
    intro f g hfg
    funext i
    have hf := hencode f i
    have hg := hencode g i
    rw [← hfg] at hg
    cases hfi : f i <;> cases hgi : g i <;> simp_all
    all_goals linarith
  simpa [Fintype.card_bool] using Fintype.card_le_of_injective encode hinjective

/-- With a fixed finite alphabet, `p` scalar coefficients supply at most
`alphabet.card ^ p` distinct parameter vectors. -/
theorem two_pow_card_le_alphabet_pow_of_strict_universal
    {I K : Type*} [Fintype I] [Fintype K]
    (alphabet : Finset ℝ) (score : (K → ℝ) → I → ℝ)
    (huniversal : ∀ f : I → Bool, ∃ θ : K → ℝ,
      (∀ k, θ k ∈ alphabet) ∧
        ∀ i, if f i then 0 < score θ i else score θ i < 0) :
    2 ^ Fintype.card I ≤ alphabet.card ^ Fintype.card K := by
  classical
  have h := two_pow_card_le_card_of_strict_universal
    (fun θ : K → alphabet ↦ score (fun k ↦ θ k)) ?_
  · simpa using h
  · intro f
    obtain ⟨θ, hθ, hsign⟩ := huniversal f
    exact ⟨fun k ↦ ⟨θ k, hθ k⟩, hsign⟩

/-- The exact information bound: if every scalar has at most `2^b` possible
values, universality on `N` inputs requires `N ≤ b * p`. -/
theorem card_le_bits_mul_parameters_of_strict_universal
    {I K : Type*} [Fintype I] [Fintype K]
    (alphabet : Finset ℝ) (score : (K → ℝ) → I → ℝ)
    (b : ℕ) (halphabet : alphabet.card ≤ 2 ^ b)
    (huniversal : ∀ f : I → Bool, ∃ θ : K → ℝ,
      (∀ k, θ k ∈ alphabet) ∧
        ∀ i, if f i then 0 < score θ i else score θ i < 0) :
    Fintype.card I ≤ b * Fintype.card K := by
  have h := two_pow_card_le_alphabet_pow_of_strict_universal
    alphabet score huniversal
  have hpow : 2 ^ Fintype.card I ≤ 2 ^ (b * Fintype.card K) := by
    calc
      2 ^ Fintype.card I ≤ alphabet.card ^ Fintype.card K := h
      _ ≤ (2 ^ b) ^ Fintype.card K := Nat.pow_le_pow_left halphabet _
      _ = 2 ^ (b * Fintype.card K) := (pow_mul _ _ _).symm
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hpow

/-- A strict representation in the original atom model whose bias and
effective affine numerator/denominator coefficients belong to a fixed
alphabet. Admissibility is inherited from `FracAtom`, on the whole cube. -/
def FiniteAlphabetStrictFracComputable (n H : ℕ)
    (alphabet : Finset ℝ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (φ : Fin H → FracAtom n) (c : ℝ),
    (∀ k, countingParameterPoint (FracAtom.affineFamily φ) c k ∈ alphabet) ∧
      ∀ x, if f x then 0 < c + ∑ h, (φ h).eval x
        else c + ∑ h, (φ h).eval x < 0

/-- This auxiliary restriction changes neither the original computability
definition nor its admissibility requirements. -/
theorem computableWithHeadsN_of_finiteAlphabetStrictFracComputable
    {n H : ℕ} {alphabet : Finset ℝ} {f : (Fin n → Bool) → Bool}
    (hf : FiniteAlphabetStrictFracComputable n H alphabet f) :
    computableWithHeadsN n H f := by
  obtain ⟨φ, c, _, hsign⟩ := hf
  apply computable_of_fracComputable
  refine ⟨φ, c, fun x ↦ ?_⟩
  have h := hsign x
  cases hfx : f x with
  | false =>
      have hn : c + ∑ h, (φ h).eval x < 0 := by simpa [hfx] using h
      simpa using hn.le
  | true =>
      have hp : 0 < c + ∑ h, (φ h).eval x := by simpa [hfx] using h
      simpa using hp

/-- Universal finite-alphabet representations in the actual atom model obey
the unconditional finite information bound. Numerator coefficients, denominator
coefficients, and the bias are all counted. -/
theorem two_pow_le_bits_mul_affine_parameters_of_finiteAlphabet_universal
    {n H b : ℕ} (alphabet : Finset ℝ)
    (halphabet : alphabet.card ≤ 2 ^ b)
    (huniversal : ∀ f : (Fin n → Bool) → Bool,
      FiniteAlphabetStrictFracComputable n H alphabet f) :
    2 ^ n ≤ b * (1 + 2 * H * (n + 1)) := by
  have h := card_le_bits_mul_parameters_of_strict_universal alphabet
    (fun (θ : CountingParameter n H → ℝ) (x : Fin n → Bool) ↦
      eval θ (countingClearedPoly (H := H) x)) b halphabet ?_
  · rw [card_countingParameter] at h
    simpa [Fintype.card_bool] using h
  · intro f
    obtain ⟨φ, c, halphabet', hsign⟩ := huniversal f
    refine ⟨countingParameterPoint (FracAtom.affineFamily φ) c,
      halphabet', fun x ↦ ?_⟩
    rw [eval_countingClearedPoly]
    change if f x then 0 < eval (cubePoint x) (clearedAtomPoly φ c)
      else eval (cubePoint x) (clearedAtomPoly φ c) < 0
    rw [clearedAtomPoly_eval]
    have hs := hsign x
    cases hfx : f x with
    | false =>
        rw [hfx] at hs
        exact mul_neg_of_pos_of_neg (atomDenProduct_eval_pos φ x) hs
    | true =>
        rw [hfx] at hs
        exact mul_pos (atomDenProduct_eval_pos φ x) hs

/-- Intrinsic raw atom parameters: the bias and, per head, `η`, `δ`, `γ`,
`α`, the `n` entries of `ρ`, and the `n` entries of `m`. This is not the
possibly redundant attention-matrix parameterization. -/
abbrev RawFracParameter (n H : ℕ) :=
  Unit ⊕ (Fin H × (Fin 4 ⊕ (Bool × Fin n)))

theorem card_rawFracParameter (n H : ℕ) :
    Fintype.card (RawFracParameter n H) = 1 + H * (4 + 2 * n) := by
  simp [RawFracParameter]

/-- The raw scalar chart of an actual admissible atom family. -/
noncomputable def rawFracParameterPoint {n H : ℕ}
    (φ : Fin H → FracAtom n) (c : ℝ) : RawFracParameter n H → ℝ
  | Sum.inl _ => c
  | Sum.inr (h, Sum.inl j) =>
      if j = 0 then (φ h).η else if j = 1 then (φ h).δ
      else if j = 2 then (φ h).γ else (φ h).α
  | Sum.inr (h, Sum.inr (false, i)) => (φ h).ρ i
  | Sum.inr (h, Sum.inr (true, i)) => (φ h).m i

/-- A deterministic decoder on every raw parameter vector. Positivity is
not needed to define this decoder; actual certificates below still use
`FracAtom` and retain all of its positivity requirements. -/
noncomputable def rawFracParameterScore {n H : ℕ}
    (θ : RawFracParameter n H → ℝ) (x : Fin n → Bool) : ℝ :=
  θ (Sum.inl ()) + ∑ h,
    (θ (Sum.inr (h, Sum.inl 0)) +
      ∑ i, θ (Sum.inr (h, Sum.inr (false, i))) *
        (if x i then θ (Sum.inr (h, Sum.inl 3)) else 1) *
        (θ (Sum.inr (h, Sum.inr (true, i))) +
          (if x i then θ (Sum.inr (h, Sum.inl 1)) else 0))) /
    (θ (Sum.inr (h, Sum.inl 2)) +
      ∑ i, θ (Sum.inr (h, Sum.inr (false, i))) *
        (if x i then θ (Sum.inr (h, Sum.inl 3)) else 1))

theorem rawFracParameterScore_point {n H : ℕ}
    (φ : Fin H → FracAtom n) (c : ℝ) (x : Fin n → Bool) :
    rawFracParameterScore (rawFracParameterPoint φ c) x =
      c + ∑ h, (φ h).eval x := by
  simp [rawFracParameterScore, rawFracParameterPoint, FracAtom.eval, FracAtom.wt]

/-- Finite alphabets on the actual raw atom scalars, with every strict sign
and every whole-cube admissibility condition retained. -/
def FiniteAlphabetRawStrictFracComputable (n H : ℕ)
    (alphabet : Finset ℝ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (φ : Fin H → FracAtom n) (c : ℝ),
    (∀ k, rawFracParameterPoint φ c k ∈ alphabet) ∧
      ∀ x, if f x then 0 < c + ∑ h, (φ h).eval x
        else c + ∑ h, (φ h).eval x < 0

/-- Raw atom alphabets obey the same information law with their exact
parameter count. No preservation of finite precision through affine
normalization or exponentiation is assumed. -/
theorem two_pow_le_bits_mul_raw_parameters_of_finiteAlphabet_universal
    {n H b : ℕ} (alphabet : Finset ℝ)
    (halphabet : alphabet.card ≤ 2 ^ b)
    (huniversal : ∀ f : (Fin n → Bool) → Bool,
      FiniteAlphabetRawStrictFracComputable n H alphabet f) :
    2 ^ n ≤ b * (1 + H * (4 + 2 * n)) := by
  have h := card_le_bits_mul_parameters_of_strict_universal alphabet
    (@rawFracParameterScore n H) b halphabet ?_
  · rw [card_rawFracParameter] at h
    simpa [Fintype.card_bool] using h
  · intro f
    obtain ⟨φ, c, halphabet', hsign⟩ := huniversal f
    refine ⟨rawFracParameterPoint φ c, halphabet', fun x ↦ ?_⟩
    simpa only [rawFracParameterScore_point] using hsign x

/-- The requested eventual bound, stated against the original worst-case
complexity. This proposition is deliberately not asserted as a theorem. -/
def WorstCaseExponentImprovement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (worstCaseHeadComplexity n : ℝ) ≤
      C * (2 : ℝ) ^ n / (n : ℝ) ^ (1 + δ)

/-- The revised task's exact eventual target, with natural logarithms.
This is an unproved proposition definition, not an upper-bound theorem. -/
def WorstCaseLogLogSaving : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (worstCaseHeadComplexity n : ℝ) ≤
      C * (2 : ℝ) ^ n / ((n : ℝ) * Real.log (Real.log (n : ℝ)))

end HeadComplexity
