import HeadComplexity.Polynomial.PureFourHeadGram
import HeadComplexity.Results.FourHeadLocalPattern

set_option linter.style.header false

namespace HeadComplexity.PureFourHeadLocalPattern

noncomputable section

open Finset PureRoPEThreeHead FourHeadSelectorQuadratic FourHeadLocalPattern
open scoped BigOperators

def fractions (p : Fin 4 → PureRoPEAtom 17) : Fin 4 → AffineFraction 17 :=
  fun h ↦ (p h).toAffineFraction

def mass (p : Fin 4 → PureRoPEAtom 17) (h : Fin 4) (i : Fin 16) : ℝ :=
  ((p h).a (i.castAdd 1) + (p h).b (i.castAdd 1)) / 2

def valueDifference (p : Fin 4 → PureRoPEAtom 17) (h : Fin 4) : ℝ :=
  ((p h).v₁ - (p h).v₀) / 2

def valueAverage (p : Fin 4 → PureRoPEAtom 17) (h : Fin 4) : ℝ :=
  ((p h).v₁ + (p h).v₀) / 2

theorem mass_pos (p : Fin 4 → PureRoPEAtom 17) (h : Fin 4) (i : Fin 16) :
    0 < mass p h i := by
  exact div_pos (add_pos ((p h).ha _) ((p h).hb _)) (by norm_num)

theorem numVector_pure (p : Fin 4 → PureRoPEAtom 17) (h : Fin 4) (i : Fin 16) :
    numVector (fractions p) h i = valueDifference p h * mass p h i +
      valueAverage p h * denVector (fractions p) h i := by
  simp only [numVector, denVector, fractions, PureRoPEAtom.toAffineFraction,
    valueDifference, valueAverage, mass]
  ring

def projectedConstant (p : Fin 4 → PureRoPEAtom 17) (c : ℝ) : ℝ :=
  extracted c (denCenter (fractions p)) (denSelector (fractions p))
    (numCenter (fractions p)) (numSelector (fractions p)) 0 0

def projectedFactors (p : Fin 4 → PureRoPEAtom 17) (c : ℝ) : Fin 4 → Fin 16 → ℝ :=
  PureFourHeadGram.factors c (denCenter (fractions p)) (denSelector (fractions p))
    (numCenter (fractions p)) (numSelector (fractions p))
    (valueDifference p) (valueAverage p) (mass p) (denVector (fractions p))

theorem projected_eq (p : Fin 4 → PureRoPEAtom 17) (c : ℝ) (x : Fin 16 → Bool) :
    extractedFunction (fractions p) c x =
      productScore (projectedConstant p c) (projectedFactors p c) (denVector (fractions p)) x := by
  rw [extractedFunction_eq, extracted_eq]
  unfold productScore
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [firstFactor_linear]
  congr 1
  unfold linear
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [projectedFactors, PureFourHeadGram.factors, PureFourHeadGram.factor]
  congr 1
  funext j
  exact numVector_pure p j i

theorem cleared_sign (p : Fin 4 → PureRoPEAtom 17) (c : ℝ)
    (f : (Fin 17 → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (p h).eval x ↔ f x = true) (x : Fin 17 → Bool) :
    0 < clearedFunction (fractions p) c x ↔ f x = true := by
  have hp (h : Fin 4) : 0 < ((fractions p) h).denominator x := (p h).denominator_pos x
  unfold clearedFunction
  rw [cleared_eq _ _ _ (fun h ↦ (hp h).ne')]
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2)) (hp 3))]
  simpa only [fractions, PureRoPEAtom.eval_eq, AffineFraction.eval] using hf x

theorem projected_positive (p : Fin 4 → PureRoPEAtom 17) (c : ℝ)
    (f : (Fin 17 → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (p h).eval x ↔ f x = true)
    (x : Fin 16 → Bool) (hx : OrbitLabel f x true) :
    0 < extractedFunction (fractions p) c x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hs := cleared_sign p c f hf
  have h1' := (hs _).mpr h1
  have h2' : clearedFunction (fractions p) c (join false x) ≤ 0 := by
    have := hs (join false x); rw [h2] at this; simpa using this
  have h3' := (hs _).mpr h3
  have h4' : clearedFunction (fractions p) c (join false (flip x)) ≤ 0 := by
    have := hs (join false (flip x)); rw [h4] at this; simpa using this
  unfold extractedFunction
  linarith

theorem projected_negative (p : Fin 4 → PureRoPEAtom 17) (c : ℝ)
    (f : (Fin 17 → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (p h).eval x ↔ f x = true)
    (x : Fin 16 → Bool) (hx : OrbitLabel f x false) :
    extractedFunction (fractions p) c x < 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hs := cleared_sign p c f hf
  have h1' : clearedFunction (fractions p) c (join true x) ≤ 0 := by
    have := hs (join true x); rw [h1] at this; simpa using this
  have h2' := (hs _).mpr h2
  have h3' : clearedFunction (fractions p) c (join true (flip x)) ≤ 0 := by
    have := hs (join true (flip x)); rw [h3] at this; simpa using this
  have h4' := (hs _).mpr h4
  unfold extractedFunction
  linarith

/-- Every completion of the 404 local labels needs at least five pure heads. -/
theorem not_pureRoPEComputable_four (f : (Fin 17 → Bool) → Bool)
    (hf : LocalPattern f) : ¬ pureRoPEComputable 17 4 f := by
  rintro ⟨p, c, hsign⟩
  obtain ⟨hz, hs, hc, hp⟩ := hf
  apply PureFourHeadGram.quadratic_obstruction (projectedConstant p c) c
    (denCenter (fractions p)) (denSelector (fractions p))
    (numCenter (fractions p)) (numSelector (fractions p))
    (valueDifference p) (valueAverage p) (mass p) (denVector (fractions p)) (mass_pos p)
  · change productScore (projectedConstant p c) (projectedFactors p c) _ zeroInput < 0
    rw [← projected_eq]
    exact projected_negative p c f hsign _ hz
  · intro i
    change 0 < productScore (projectedConstant p c) (projectedFactors p c) _ (singleInput i)
    rw [← projected_eq]
    exact projected_positive p c f hsign _ (hs i)
  · intro i j hij
    change productScore (projectedConstant p c) (projectedFactors p c) _
      (doubleInput (left i) (right j)) < 0
    rw [← projected_eq]
    exact projected_negative p c f hsign _ (hc i j hij)
  · intro i j hij
    change productScore (projectedConstant p c) (projectedFactors p c) _
      (doubleInput (right i) (right j)) < 0
    rw [← projected_eq]
    exact projected_negative p c f hsign _ (hp i j hij)

theorem pureRoPEHStar_ge_five (f : (Fin 17 → Bool) → Bool) (hf : LocalPattern f) :
    5 ≤ PureRoPEHStar 17 f := by
  by_contra h
  have hle : PureRoPEHStar 17 f ≤ 4 := by omega
  apply not_pureRoPEComputable_four f hf
  exact PureRoPEThreeHead.computable_mono hle (pureRoPEHStar_computable f)

end
end HeadComplexity.PureFourHeadLocalPattern
