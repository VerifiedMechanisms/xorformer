import HeadComplexity.Research.CoefficientOrderChart
import HeadComplexity.Research.RelativeMarginQuantifiers
import HeadComplexity.Atoms.FracAtomSymmetry
import HeadComplexity.Results.WarrenBound

set_option linter.style.header false

/-!
Original-model bridge for the finite margin-sensitive capacity theorem.
All atoms remain genuine `FracAtom`s. Numerators and denominators vary with
the target, coefficients are unrestricted real numbers, and no cancellation
hypothesis is imposed. The count retains a positive relative-margin hypothesis.
-/

noncomputable section

namespace HeadComplexity.OriginalMarginCapacity

open Finset MvPolynomial
open scoped BigOperators
open CoefficientOrderChart MarginSensitiveCapacity RelativeMarginQuantifiers

variable {n H : ℕ}

/-- Affine coefficients of an atom's numerator. -/
def numeratorCoefficients (phi : FracAtom n) : Option (Fin n) → ℝ
  | none => phi.η + ∑ i, phi.ρ i * phi.m i
  | some i => phi.ρ i * (phi.α * (phi.m i + phi.δ) - phi.m i)

/-- Affine coefficients of an atom's denominator. -/
def denominatorCoefficients (phi : FracAtom n) : Option (Fin n) → ℝ
  | none => phi.γ + ∑ i, phi.ρ i
  | some i => phi.ρ i * (phi.α - 1)

theorem affineValue_numeratorCoefficients (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue (numeratorCoefficients phi) x =
      phi.η + ∑ i, phi.wt x i * (phi.m i + if x i then phi.δ else 0) := by
  unfold affineValue numeratorCoefficients
  rw [add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  cases h : x i <;> simp [FracAtom.wt, h, boolToReal]
  ring

theorem affineValue_denominatorCoefficients (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue (denominatorCoefficients phi) x = phi.γ + ∑ i, phi.wt x i := by
  unfold affineValue denominatorCoefficients
  rw [add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  cases h : x i <;> simp [FracAtom.wt, h, boolToReal]
  ring

theorem affineRatio_eq_eval (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue (numeratorCoefficients phi) x /
      affineValue (denominatorCoefficients phi) x = phi.eval x := by
  rw [affineValue_numeratorCoefficients, affineValue_denominatorCoefficients]
  rfl

theorem denominatorCoefficients_constant_pos (phi : FracAtom n) :
    0 < denominatorCoefficients phi none :=
  add_pos_of_pos_of_nonneg phi.hγ (sum_nonneg fun i _ => (phi.hρ i).le)

theorem denominatorCoefficients_nonneg (phi : FracAtom n) (ha : 1 ≤ phi.α) :
    ∀ i, 0 ≤ denominatorCoefficients phi i := by
  intro i
  cases i with
  | none => exact (denominatorCoefficients_constant_pos phi).le
  | some i => exact mul_nonneg (phi.hρ i).le (sub_nonneg.mpr ha)

/-- Whether the input coordinates inside this one head must be reflected. -/
def orientation (phi : FracAtom n) : Bool := if 1 ≤ phi.α then false else true

/-- An admissible atom with nonnegative denominator slopes. -/
def orientedAtom (phi : FracAtom n) : FracAtom n := if 1 ≤ phi.α then phi else phi.flip

theorem orientedAtom_alpha (phi : FracAtom n) : 1 ≤ (orientedAtom phi).α := by
  by_cases h : 1 ≤ phi.α
  · simp [orientedAtom, h]
  · simp only [orientedAtom, ite_eq_right h, FracAtom.flip]
    exact (one_le_inv₀ phi.hα).mpr (le_of_not_ge h)

theorem orientedAtom_eval (phi : FracAtom n) (x : Fin n → Bool) :
    (orientedAtom phi).eval (CoefficientOrderChart.coordinates (orientation phi) x) =
      phi.eval x := by
  by_cases h : 1 ≤ phi.α
  · simp only [orientedAtom, orientation, ite_eq_left h]
    rfl
  · simp only [orientedAtom, orientation, ite_eq_right h, FracAtom.flip_eval]
    congr 1
    funext i
    simp [flipBits, CoefficientOrderChart.coordinates]

/-- Actual polynomial parameter values: all reciprocal entries are present,
including unused zero-denominator coefficients, whose inverse is harmless. -/
def parameterPoint (phi : Fin H → FracAtom n) (c : ℝ) : Parameter n H → ℝ
  | Sum.inl _ => c
  | Sum.inr (h, kind, i) =>
      if kind = 0 then numeratorCoefficients (orientedAtom (phi h)) i
      else if kind = 1 then denominatorCoefficients (orientedAtom (phi h)) i
      else (denominatorCoefficients (orientedAtom (phi h)) i)⁻¹

@[simp] theorem parameterPoint_bias (phi : Fin H → FracAtom n) (c : ℝ) :
    parameterPoint phi c (Sum.inl ()) = c := rfl

@[simp] theorem eval_parameterPoint_numerator (phi : Fin H → FracAtom n)
    (c : ℝ) (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint phi c) (affinePoly 0 h x) =
      affineValue (numeratorCoefficients (orientedAtom (phi h))) x := by
  simp [affinePoly, parameterPoint, affineValue]

@[simp] theorem eval_parameterPoint_denominator (phi : Fin H → FracAtom n)
    (c : ℝ) (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint phi c) (affinePoly 1 h x) =
      affineValue (denominatorCoefficients (orientedAtom (phi h))) x := by
  simp [affinePoly, parameterPoint, affineValue]

@[simp] theorem parameterPoint_reciprocal (phi : Fin H → FracAtom n)
    (c : ℝ) (h : Fin H) (i : Option (Fin n)) :
    parameterPoint phi c (Sum.inr (h, 2, i)) =
      (denominatorCoefficients (orientedAtom (phi h)) i)⁻¹ := by
  simp [parameterPoint]

/-- Every high-margin original representation occurs in the finite chart
union. The global atom suprema are precisely those in the requested margin. -/
theorem highMarginFunctions_subset_orderedPatterns {gamma : ℝ}
    (hgamma : 0 < gamma) (d : ℕ)
    (hdegree : Real.exp (-((d + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ gamma / 2) :
    highMarginFunctions n H gamma ⊆
      chartPatterns (toChart (n := n) (H := H)) ((n + 1 : ℕ) : ℝ) d := by
  classical
  intro f hf
  obtain ⟨phi, c, hs, hg⟩ := hf
  have hex (h : Fin H) := exists_conditioning_order
    (denominatorCoefficients (orientedAtom (phi h)))
    (denominatorCoefficients_nonneg _ (orientedAtom_alpha _))
    (denominatorCoefficients_constant_pos _)
  choose order horder using hex
  let idx : CoefficientOrderChart.Index n H := fun h => (orientation (phi h), order h)
  let q : Fin H → (Fin n → Bool) → ℝ := fun h x =>
    denominatorCoefficients (orientedAtom (phi h))
      (selected (order h) (CoefficientOrderChart.coordinates (orientation (phi h)) x))
  have hratio (h : Fin H) (x : Fin n → Bool) :
      eval (parameterPoint phi c) (affinePoly 0 h ((toChart idx).coordinates h x)) /
        eval (parameterPoint phi c) (affinePoly 1 h ((toChart idx).coordinates h x)) =
          (phi h).eval x := by
    rw [eval_parameterPoint_numerator, eval_parameterPoint_denominator, affineRatio_eq_eval]
    exact orientedAtom_eval (phi h) x
  have hpattern := strictPattern_of_margin (toChart idx) ((n + 1 : ℕ) : ℝ) gamma d
    f (parameterPoint phi c) q (fun h => atomSup (phi h)) hgamma (by norm_cast; omega)
    (fun h x => by simp [toChart, idx, q])
    (fun h x => (horder h (CoefficientOrderChart.coordinates (orientation (phi h)) x)).1)
    (fun h x => by
      simpa [toChart, idx, q] using
        (horder h (CoefficientOrderChart.coordinates (orientation (phi h)) x)).2.1)
    (fun h x => by
      simpa [toChart, idx, q] using
        (horder h (CoefficientOrderChart.coordinates (orientation (phi h)) x)).2.2)
    (fun h x => by rw [hratio]; exact abs_eval_le_atomSup (phi h) x)
    (by simpa [amplitude] using amplitude_pos_of_strict hs)
    (fun x => by
      have hmin : gamma * amplitude phi c ≤ minimumSignedScore f phi c :=
        (le_div_iff₀ (amplitude_pos_of_strict hs)).mp hg
      have hinf : minimumSignedScore f phi c ≤ signedLabel f x * score phi c x :=
        Finset.inf'_le _ (Finset.mem_univ x)
      simpa only [parameterPoint_bias, hratio, amplitude, score, signedLabel] using
        hmin.trans hinf)
    hdegree
  exact Set.mem_iUnion.mpr ⟨idx, hpattern⟩

/-- Finite margin-sensitive count for genuine original heads, with the
analytic strict sign theorem retained as an explicit argument. -/
theorem card_highMarginFunctions_le_warren (hWarren : WarrenStrictSignPatternBound)
    {gamma : ℝ} (hgamma : 0 < gamma) (d : ℕ)
    (hdegree : Real.exp (-((d + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ gamma / 2)
    (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((highMarginFunctions n H gamma).ncard : ℝ) ≤
      ((2 * (n + 1).factorial : ℕ) : ℝ) ^ H *
        (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) := by
  have hsub := highMarginFunctions_subset_orderedPatterns (H := H) hgamma d hdegree
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  calc
    _ ≤ ((chartPatterns (toChart (n := n) (H := H)) ((n + 1 : ℕ) : ℝ) d).ncard : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := card_orderedPatterns_le_warren hWarren ((n + 1 : ℕ) : ℝ) d hparameters

/-- The elementary geometric degree used in the written finite formula. -/
def approximationDegree (n : ℕ) (gamma : ℝ) : ℕ :=
  ⌈((n + 1 : ℕ) : ℝ) * Real.log (2 / gamma)⌉₊

theorem approximationDegree_error {gamma : ℝ} (hgamma : 0 < gamma) :
    Real.exp (-((approximationDegree n gamma + 1 : ℕ) : ℝ) /
      ((n + 1 : ℕ) : ℝ)) ≤ gamma / 2 := by
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hceil : ((n + 1 : ℕ) : ℝ) * Real.log (2 / gamma) ≤
      (approximationDegree n gamma : ℝ) := Nat.le_ceil _
  have harg : -((approximationDegree n gamma + 1 : ℕ) : ℝ) /
      ((n + 1 : ℕ) : ℝ) ≤ -Real.log (2 / gamma) := by
    apply (div_le_iff₀ hm).mpr
    push_cast at hceil ⊢
    nlinarith
  calc
    _ ≤ Real.exp (-Real.log (2 / gamma)) := Real.exp_le_exp.mpr harg
    _ = gamma / 2 := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hgamma), inv_div]

/-- The exact finite formula with the ceiling degree and only the genuine
relative-margin hypothesis, apart from the explicit Warren theorem argument. -/
theorem card_highMarginFunctions_le_finite_formula
    (hWarren : WarrenStrictSignPatternBound) {gamma : ℝ} (hgamma : 0 < gamma)
    (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((highMarginFunctions n H gamma).ncard : ℝ) ≤
      ((2 * (n + 1).factorial : ℕ) : ℝ) ^ H *
        (4 * Real.exp 1 * (2 * (approximationDegree n gamma : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) :=
  card_highMarginFunctions_le_warren hWarren hgamma (approximationDegree n gamma)
    (approximationDegree_error hgamma) hparameters

/-- Unconditional finite margin-sensitive capacity theorem for the original
model. The imported and independently audited Warren proof discharges the
analytic argument; the relative-margin hypothesis is deliberately retained. -/
theorem card_highMarginFunctions_le {gamma : ℝ} (hgamma : 0 < gamma)
    (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((highMarginFunctions n H gamma).ncard : ℝ) ≤
      ((2 * (n + 1).factorial : ℕ) : ℝ) ^ H *
        (4 * Real.exp 1 * (2 * (approximationDegree n gamma : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) :=
  card_highMarginFunctions_le_finite_formula warrenStrictSignPatternBound hgamma hparameters

#print axioms orientedAtom_eval
#print axioms highMarginFunctions_subset_orderedPatterns
#print axioms card_highMarginFunctions_le_warren
#print axioms approximationDegree_error
#print axioms card_highMarginFunctions_le_finite_formula
#print axioms card_highMarginFunctions_le

end HeadComplexity.OriginalMarginCapacity
