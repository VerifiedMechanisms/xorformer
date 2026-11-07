module

public import HeadComplexity.BooleanFunction.SignRepresentation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# One-layer attention on Boolean inputs

`Attention.Model` has shared token and positional embeddings and separate query, key, value,
and output maps for each head. The model reads the residual at the fixed query position.
`HasHeadScore` and `ComputableWithHeads` record score realization and Boolean computation at
a fixed head budget.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace HeadComplexity
namespace Attention

/-- A shared-embedding attention layer with `n` input bits, `H` heads, model width `d`,
and head width `m`. The distinguished token and position are both indexed by `none`. -/
structure Model (n H d m : ℕ) where
  tokenEmbed : Option Bool → EuclideanSpace ℝ (Fin d)
  posEmbed : Option (Fin n) → EuclideanSpace ℝ (Fin d)
  query : Fin H → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)
  key : Fin H → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)
  value : Fin H → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)
  out : Fin H → EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)

namespace Model

variable {n H d m : ℕ} (M : Model n H d m)

/-- The sum of the token and positional embeddings at a position. -/
def embed (x : Fin n → Bool) (p : Option (Fin n)) : EuclideanSpace ℝ (Fin d) :=
  M.tokenEmbed (p.map x) + M.posEmbed p

/-- The query embedding is the sum of the query token and position embeddings, independently of
the input. -/
@[simp] theorem embed_none (x : Fin n → Bool) :
    M.embed x none = M.tokenEmbed none + M.posEmbed none := rfl

/-- At an input position, the embedding adds the embedding of its bit to its positional
embedding. -/
@[simp] theorem embed_some (x : Fin n → Bool) (i : Fin n) :
    M.embed x (some i) = M.tokenEmbed (some (x i)) + M.posEmbed (some i) := rfl

/-- The logit at a position, with the query taken at `none`. -/
def logit (h : Fin H) (x : Fin n → Bool) (p : Option (Fin n)) : ℝ :=
  ⟪M.query h (M.embed x none), M.key h (M.embed x p)⟫_ℝ

/-- The unnormalized attention weight at a position. -/
def weight (h : Fin H) (x : Fin n → Bool) (p : Option (Fin n)) : ℝ :=
  Real.exp (M.logit h x p)

/-- Every unnormalized softmax weight is strictly positive. -/
theorem weight_pos (h : Fin H) (x : Fin n → Bool) (p : Option (Fin n)) :
    0 < M.weight h x p := Real.exp_pos _

/-- The softmax denominator, including the query position. -/
def denominator (h : Fin H) (x : Fin n → Bool) : ℝ :=
  ∑ p, M.weight h x p

/-- The sum of the softmax weights is strictly positive because it includes the query position. -/
theorem denominator_pos (h : Fin H) (x : Fin n → Bool) : 0 < M.denominator h x :=
  Finset.sum_pos (fun p _ ↦ M.weight_pos h x p) ⟨none, Finset.mem_univ _⟩

/-- The weighted sum of values before softmax normalization and output projection. -/
def numerator (h : Fin H) (x : Fin n → Bool) : EuclideanSpace ℝ (Fin m) :=
  ∑ p, M.weight h x p • M.value h (M.embed x p)

/-- The projected output of one head. -/
def headOutput (h : Fin H) (x : Fin n → Bool) : EuclideanSpace ℝ (Fin d) :=
  M.out h ((M.denominator h x)⁻¹ • M.numerator h x)

/-- The scalar readout at the query, with the classification threshold subtracted. -/
def score (w : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (x : Fin n → Bool) : ℝ :=
  ⟪w, M.embed x none + ∑ h, M.headOutput h x⟫_ℝ - τ

/-- The scalar score is a constant from the query and threshold plus one ratio per head, with
the scalar readout applied to the weighted values. -/
theorem score_eq_const_add_sum_div (w : EuclideanSpace ℝ (Fin d)) (τ : ℝ)
    (x : Fin n → Bool) :
    M.score w τ x = (⟪w, M.tokenEmbed none + M.posEmbed none⟫_ℝ - τ) +
      ∑ h, (∑ p, M.weight h x p * ⟪w, M.out h (M.value h (M.embed x p))⟫_ℝ) /
        M.denominator h x := by
  simp only [score, headOutput, numerator, embed_none, inner_add_right, inner_sum, map_smul,
    map_sum, real_inner_smul_right, div_eq_inv_mul, sub_eq_add_neg]
  exact add_right_comm _ _ _

/-- Append `k` heads with zero output maps. -/
def pad (k : ℕ) : Model n (H + k) d m where
  tokenEmbed := M.tokenEmbed
  posEmbed := M.posEmbed
  query := Fin.addCases M.query fun _ ↦ 0
  key := Fin.addCases M.key fun _ ↦ 0
  value := Fin.addCases M.value fun _ ↦ 0
  out := Fin.addCases M.out fun _ ↦ 0

/-- Appending zero-output heads leaves the input and query embeddings unchanged. -/
@[simp] theorem embed_pad (k : ℕ) (x : Fin n → Bool) (p : Option (Fin n)) :
    (M.pad k).embed x p = M.embed x p := rfl

/-- An original head has the same output after padding the model. -/
@[simp] theorem headOutput_pad_castAdd (k : ℕ) (h : Fin H) (x : Fin n → Bool) :
    (M.pad k).headOutput (Fin.castAdd k h) x = M.headOutput h x := by
  simp only [headOutput, numerator, denominator, weight, logit, embed, pad, Fin.addCases_left]

/-- Each appended head has zero output. -/
@[simp] theorem headOutput_pad_natAdd (k : ℕ) (h : Fin k) (x : Fin n → Bool) :
    (M.pad k).headOutput (Fin.natAdd H h) x = 0 := by
  simp [headOutput, pad]

/-- Padding by zero-output heads preserves the entire scalar score. -/
@[simp] theorem score_pad (k : ℕ) (w : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    (M.pad k).score w τ = M.score w τ := by
  funext x
  simp only [score, embed_pad, Fin.sum_univ_add, headOutput_pad_castAdd, headOutput_pad_natAdd,
    Finset.sum_const_zero, add_zero]

end Model
end Attention

variable {n H K : ℕ} {s : (Fin n → Bool) → ℝ} {f : (Fin n → Bool) → Bool}

/-- Exact realization of a scalar score with `H` heads and positive widths. -/
def HasHeadScore (s : (Fin n → Bool) → ℝ) (H : ℕ) : Prop :=
  ∃ d m, ∃ M : Attention.Model n H (d + 1) (m + 1), ∃ w τ, M.score w τ = s

/-- Boolean computation by thresholding a score realized with `H` heads. -/
def ComputableWithHeads (f : (Fin n → Bool) → Bool) (H : ℕ) : Prop :=
  ∃ s, HasHeadScore s H ∧ Function.SignRepresents s f

/-- An exactly realized score computes a Boolean function when its positive set is the true set. -/
theorem HasHeadScore.computableWithHeads (hs : HasHeadScore s H)
    (hf : Function.SignRepresents s f) : ComputableWithHeads f H :=
  ⟨s, hs, hf⟩

/-- An exact score can be realized with any larger head budget. -/
theorem HasHeadScore.mono (h : H ≤ K) (hs : HasHeadScore s H) : HasHeadScore s K := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨d, m, M, w, τ, hscore⟩ := hs
  exact ⟨d, m, M.pad k, w, τ, (M.score_pad k w τ).trans hscore⟩

/-- A Boolean function that is computable at one head budget is computable at any larger budget. -/
theorem ComputableWithHeads.mono (h : H ≤ K) (hf : ComputableWithHeads f H) :
    ComputableWithHeads f K := by
  obtain ⟨s, hs, hsign⟩ := hf
  exact (hs.mono h).computableWithHeads hsign

/-- The scores that can be realized with zero heads are exactly the constant scores. -/
theorem hasHeadScore_zero_iff : HasHeadScore s 0 ↔ ∃ c, s = Function.const _ c := by
  constructor
  · rintro ⟨d, m, M, w, τ, rfl⟩
    exact ⟨⟪w, M.tokenEmbed none + M.posEmbed none⟫_ℝ - τ, by
      funext x
      simp [Attention.Model.score]⟩
  · rintro ⟨c, rfl⟩
    let M : Attention.Model n 0 1 1 :=
      { tokenEmbed := 0, posEmbed := 0, query := 0, key := 0, value := 0, out := 0 }
    refine ⟨0, 0, M, 0, -c, ?_⟩
    funext x
    simp [Attention.Model.score]

end HeadComplexity
