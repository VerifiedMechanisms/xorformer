import HeadComplexity.Research.ConditionedReciprocalApproximation
import HeadComplexity.Results.CountingLowerBound
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm

set_option linter.style.header false

/-!
Polynomial parameterization of the conditioned reciprocal approximation.

For a fixed selection chart, the score has `1 + 3 * (n + 1) * H`
parameters and parameter degree at most `2 * d + 2`. The last counting
statement explicitly assumes Warren's theorem. This file does not prove
a sparse margin repair or an unrestricted lower bound.
-/

noncomputable section

namespace HeadComplexity.MarginSensitiveCapacity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

/-- Bias, affine numerator, affine denominator, and reciprocal coefficients. -/
abbrev Parameter (n H : ℕ) := Unit ⊕ (Fin H × Fin 3 × Option (Fin n))

theorem card_parameter :
    Fintype.card (Parameter n H) = 1 + 3 * (n + 1) * H := by
  simp [Parameter]
  ring

/-- A fixed chart chooses the head's coordinates and one present coefficient
at each input. No polynomial dependence on these choices is asserted. -/
structure Chart (n H : ℕ) where
  coordinates : Fin H → (Fin n → Bool) → (Fin n → Bool)
  selected : Fin H → (Fin n → Bool) → Option (Fin n)

/-- The universal affine coefficient block at a fixed Boolean point. -/
def affinePoly (kind : Fin 3) (h : Fin H) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H) ℝ :=
  X (Sum.inr (h, kind, none)) +
    ∑ i, C (boolToReal (x i)) * X (Sum.inr (h, kind, some i))

theorem affinePoly_totalDegree_le (kind : Fin 3) (h : Fin H)
    (x : Fin n → Bool) : (affinePoly kind h x).totalDegree ≤ 1 := by
  unfold affinePoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · refine totalDegree_finsetSum_le fun i _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

/-- Formal reciprocal of the selected denominator coefficient. -/
def reciprocalPoly (chart : Chart n H) (h : Fin H) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H) ℝ :=
  X (Sum.inr (h, 2, chart.selected h x))

@[simp] theorem reciprocalPoly_totalDegree (chart : Chart n H)
    (h : Fin H) (x : Fin n → Bool) :
    (reciprocalPoly chart h x).totalDegree = 1 := totalDegree_X _

/-- Polynomial obtained by substituting the formal reciprocal into the finite
geometric approximation. The scalar `m` is fixed, not a parameter. -/
def headPoly (chart : Chart n H) (m : ℝ) (d : ℕ)
    (h : Fin H) (x : Fin n → Bool) : MvPolynomial (Parameter n H) ℝ :=
  affinePoly 0 h (chart.coordinates h x) * (reciprocalPoly chart h x * C m⁻¹) *
    ∑ k ∈ range (d + 1),
      (1 - affinePoly 1 h (chart.coordinates h x) *
        (reciprocalPoly chart h x * C m⁻¹)) ^ k

theorem headPoly_totalDegree_le (chart : Chart n H) (m : ℝ) (d : ℕ)
    (h : Fin H) (x : Fin n → Bool) :
    (headPoly chart m d h x).totalDegree ≤ 2 * d + 2 := by
  have hz : (reciprocalPoly chart h x * C m⁻¹).totalDegree ≤ 1 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [reciprocalPoly_totalDegree, totalDegree_C]
  have hmul (kind : Fin 3) :
      (affinePoly kind h (chart.coordinates h x) *
        (reciprocalPoly chart h x * C m⁻¹)).totalDegree ≤ 2 := by
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (affinePoly_totalDegree_le _ _ _) hz)
  have hbase :
      (1 - affinePoly 1 h (chart.coordinates h x) *
        (reciprocalPoly chart h x * C m⁻¹)).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ (hmul 1))
    simp
  have hsum :
      (∑ k ∈ range (d + 1),
        (1 - affinePoly 1 h (chart.coordinates h x) *
          (reciprocalPoly chart h x * C m⁻¹)) ^ k).totalDegree ≤ 2 * d := by
    refine totalDegree_finsetSum_le fun k hk => ?_
    have hk' : k ≤ d := Nat.le_of_lt_succ (mem_range.mp hk)
    calc
      _ ≤ k * (1 - affinePoly 1 h (chart.coordinates h x) *
          (reciprocalPoly chart h x * C m⁻¹)).totalDegree := totalDegree_pow _ _
      _ ≤ k * 2 := Nat.mul_le_mul_left _ hbase
      _ ≤ d * 2 := Nat.mul_le_mul_right _ hk'
      _ = 2 * d := Nat.mul_comm _ _
  unfold headPoly
  exact (totalDegree_mul _ _).trans
    ((Nat.add_le_add (hmul 0) hsum).trans_eq (by omega))

/-- The universal score for a fixed coefficient-selection chart. -/
def scorePoly (chart : Chart n H) (m : ℝ) (d : ℕ)
    (x : Fin n → Bool) : MvPolynomial (Parameter n H) ℝ :=
  X (Sum.inl ()) + ∑ h, headPoly chart m d h x

theorem scorePoly_totalDegree_le (chart : Chart n H) (m : ℝ) (d : ℕ)
    (x : Fin n → Bool) :
    (scorePoly chart m d x).totalDegree ≤ 2 * d + 2 := by
  unfold scorePoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
    omega
  · exact totalDegree_finsetSum_le fun h _ => headPoly_totalDegree_le chart m d h x

/-- The polynomial evaluation is exactly the scalar geometric approximation
when the selected formal reciprocal has its actual value. -/
theorem eval_headPoly (chart : Chart n H) (m : ℝ) (d : ℕ)
    (h : Fin H) (x : Fin n → Bool) (θ : Parameter n H → ℝ) (q : ℝ)
    (hz : θ (Sum.inr (h, 2, chart.selected h x)) = q⁻¹) :
    eval θ (headPoly chart m d h x) =
      ConditionedReciprocalApproximation.headApprox
        (eval θ (affinePoly 0 h (chart.coordinates h x)))
        (eval θ (affinePoly 1 h (chart.coordinates h x))) q m d := by
  simp only [headPoly, map_mul, map_sum, map_pow, map_sub, map_one,
    eval_C, reciprocalPoly, eval_X, hz,
    ConditionedReciprocalApproximation.headApprox, div_eq_mul_inv, mul_inv_rev]

/-- A positive relative margin supplies a strict polynomial sign pattern
once the chart is conditioned and the degree gives sufficiently small error. -/
theorem strictPattern_of_margin
    (chart : Chart n H) (m gamma : ℝ) (d : ℕ)
    (f : (Fin n → Bool) → Bool) (θ : Parameter n H → ℝ)
    (q : Fin H → (Fin n → Bool) → ℝ) (M : Fin H → ℝ)
    (hgamma : 0 < gamma) (hm : 1 ≤ m)
    (hz : ∀ h x, θ (Sum.inr (h, 2, chart.selected h x)) = (q h x)⁻¹)
    (hq : ∀ h x, 0 < q h x)
    (hlo : ∀ h x, q h x ≤ eval θ (affinePoly 1 h (chart.coordinates h x)))
    (hhi : ∀ h x, eval θ (affinePoly 1 h (chart.coordinates h x)) ≤ m * q h x)
    (hamp : ∀ h x,
      |eval θ (affinePoly 0 h (chart.coordinates h x)) /
        eval θ (affinePoly 1 h (chart.coordinates h x))| ≤ M h)
    (hM : 0 < |θ (Sum.inl ())| + ∑ h, M h)
    (hmargin : ∀ x,
      gamma * (|θ (Sum.inl ())| + ∑ h, M h) ≤
        (if f x then (1 : ℝ) else -1) *
          (θ (Sum.inl ()) + ∑ h,
            eval θ (affinePoly 0 h (chart.coordinates h x)) /
              eval θ (affinePoly 1 h (chart.coordinates h x))))
    (hdegree : Real.exp (-((d + 1 : ℕ) : ℝ) / m) ≤ gamma / 2) :
    StrictPolynomialSignPattern (scorePoly chart m d) f := by
  refine ⟨θ, fun x => ?_⟩
  have hsign := ConditionedReciprocalApproximation.conditioned_score_preserves_sign
    (fun h => eval θ (affinePoly 0 h (chart.coordinates h x)))
    (fun h => eval θ (affinePoly 1 h (chart.coordinates h x)))
    (fun h => q h x) M (θ (Sum.inl ())) (if f x then 1 else -1) gamma m d
    (by cases f x <;> norm_num) hgamma hm
    (fun h => hq h x) (fun h => hlo h x) (fun h => hhi h x)
    (fun h => hamp h x) hM (hmargin x) hdegree
  have heval : eval θ (scorePoly chart m d x) = θ (Sum.inl ()) +
      ∑ h, ConditionedReciprocalApproximation.headApprox
        (eval θ (affinePoly 0 h (chart.coordinates h x)))
        (eval θ (affinePoly 1 h (chart.coordinates h x))) (q h x) m d := by
    simp only [scorePoly, map_add, eval_X, map_sum]
    congr 1
    exact sum_congr rfl (fun h _ => eval_headPoly chart m d h x θ (q h x) (hz h x))
  rw [heval]
  cases hfx : f x
  · simp only [hfx, Bool.false_eq_true, ↓reduceIte, neg_one_mul] at hsign ⊢
    linarith
  · simpa [hfx] using hsign

/-- Exact fixed-chart count. Warren remains an explicit proposition hypothesis. -/
theorem card_strictPatterns_le_warren (hWarren : WarrenStrictSignPatternBound)
    (chart : Chart n H) (m : ℝ) (d : ℕ)
    (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((strictPolynomialSignPatterns (scorePoly chart m d)).ncard : ℝ) ≤
      (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
        (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) := by
  have h := hWarren (2 ^ n) (2 * d + 2) (1 + 3 * (n + 1) * H)
    (by omega) (by omega) hparameters
    (Fin n → Bool) (Parameter n H) (scorePoly chart m d)
    (by simp [Fintype.card_bool]) card_parameter
    (scorePoly_totalDegree_le chart m d)
  exact_mod_cast h

/-- Union of the sign families over a finite list of charts. -/
def chartPatterns {ι : Type*} (charts : ι → Chart n H) (m : ℝ) (d : ℕ) :
    Set ((Fin n → Bool) → Bool) :=
  ⋃ i, strictPolynomialSignPatterns (scorePoly (charts i) m d)

/-- The finite union costs exactly the number of charts. -/
theorem card_chartPatterns_le_warren {ι : Type*} [Fintype ι]
    (hWarren : WarrenStrictSignPatternBound)
    (charts : ι → Chart n H) (m : ℝ) (d : ℕ)
    (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((chartPatterns charts m d).ncard : ℝ) ≤
      (Fintype.card ι : ℝ) *
        (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) := by
  classical
  calc
    _ ≤ ∑ i : ι,
        ((strictPolynomialSignPatterns (scorePoly (charts i) m d)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_iUnion_le_of_fintype
        (fun i => strictPolynomialSignPatterns (scorePoly (charts i) m d))
    _ ≤ ∑ _i : ι,
        (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) :=
      sum_le_sum (fun i _ => card_strictPatterns_le_warren hWarren (charts i) m d hparameters)
    _ = _ := by simp

#print axioms card_parameter
#print axioms headPoly_totalDegree_le
#print axioms scorePoly_totalDegree_le
#print axioms eval_headPoly
#print axioms strictPattern_of_margin
#print axioms card_strictPatterns_le_warren
#print axioms card_chartPatterns_le_warren

end HeadComplexity.MarginSensitiveCapacity
