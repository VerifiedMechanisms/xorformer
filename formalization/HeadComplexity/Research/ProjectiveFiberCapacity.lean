import HeadComplexity.Research.AffineFiberCapacity

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-! Margin-free capacity after positive rescaling on projective denominator fibers. -/

noncomputable section
namespace HeadComplexity.ProjectiveFiberCapacity
open Finset MvPolynomial
open scoped BigOperators

open AffineFiberCapacity
abbrev Coordinate (n : ℕ) := Option (Fin n)
abbrev WedgeCoordinate (n : ℕ) := Coordinate n × Coordinate n
abbrev Parameter (n : ℕ) := Option (WedgeCoordinate n × WedgeCoordinate n)

variable {n K H : ℕ}

def inputCoordinate (x : Cube n) : Coordinate n → ℝ
  | none => 1
  | some i => boolToReal (x i)

def wedgeFeature (xy : Cube n × Cube n) (ij : WedgeCoordinate n) : ℝ :=
  inputCoordinate xy.1 ij.1 * inputCoordinate xy.2 ij.2 -
    inputCoordinate xy.2 ij.1 * inputCoordinate xy.1 ij.2

def partitionPoly (xy : Cube n × Cube n) : MvPolynomial (Parameter n) ℝ :=
  X none - ∑ i, ∑ j, C (wedgeFeature xy i * wedgeFeature xy j) *
    X (some (i, j))

theorem partitionPoly_totalDegree_le (xy : Cube n × Cube n) :
    (partitionPoly xy).totalDegree ≤ 1 := by
  unfold partitionPoly
  apply (totalDegree_sub _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X, zero_add]; omega)

def partitionPatterns (n : ℕ) : Set (Relation n) :=
  strictPolynomialSignPatterns (partitionPoly (n := n))

def represented (n K : ℕ) (hK : 0 < K) : Set (Cube n → Bool) :=
  ⋃ E : partitionPatterns n,
    strictPolynomialSignPatterns (affinePoly (canonicalCode hK E.val))

theorem card_partitionPatterns_le (hparameters : 1 + (n + 1) ^ 4 ≤ (2 ^ n) ^ 2) :
    ((partitionPatterns n).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((2 : ℝ) ^ n) ^ 2 / (1 + ((n : ℝ) + 1) ^ 4)) ^ (1 + (n + 1) ^ 4) := by
  have hp : Fintype.card (Parameter n) = 1 + (n + 1) ^ 4 := by
    simp [Parameter, WedgeCoordinate, Coordinate]
    ring
  have hi : Fintype.card (Cube n × Cube n) = (2 ^ n) ^ 2 := by
    simp [Cube, Fintype.card_bool, pow_two]
  have h := warrenStrictSignPatternBound ((2 ^ n) ^ 2) 1 (1 + (n + 1) ^ 4)
    (by omega) (by omega) hparameters (Cube n × Cube n) (Parameter n)
    partitionPoly hi hp partitionPoly_totalDegree_le
  simpa [partitionPatterns] using h

/-- All joint observation partitions are charged independently of head count. -/
theorem card_represented_le (hK : 0 < K)
    (hpartition : 1 + (n + 1) ^ 4 ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    ((represented n K hK).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((2 : ℝ) ^ n) ^ 2 / (1 + ((n : ℝ) + 1) ^ 4)) ^ (1 + (n + 1) ^ 4) *
      (4 * Real.exp 1 * (2 : ℝ) ^ n / (((n : ℝ) + 1) * K)) ^ ((n + 1) * K) := by
  classical
  let := Fintype.ofFinite (partitionPatterns n)
  let B : ℝ := (4 * Real.exp 1 * (2 : ℝ) ^ n / (((n : ℝ) + 1) * K)) ^ ((n + 1) * K)
  have hB : 0 ≤ B := by positivity
  calc
    _ ≤ ∑ E : partitionPatterns n,
        ((strictPolynomialSignPatterns (affinePoly (canonicalCode hK E.val))).ncard : ℝ) := by
      exact_mod_cast Set.ncard_iUnion_le_of_fintype
        (fun E : partitionPatterns n ↦
          strictPolynomialSignPatterns (affinePoly (canonicalCode hK E.val)))
    _ ≤ ∑ _E : partitionPatterns n, B := by
      apply Finset.sum_le_sum
      intro E _
      exact card_affinePatterns_le _ hK haffine
    _ = ((partitionPatterns n).ncard : ℝ) * B := by
      simp [Set.fintypeCard_eq_ncard]
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_partitionPatterns_le hpartition) hB

/-- A finite Gram identity for arbitrary observation features. -/
theorem gram_identity {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (v : J → ℝ) :
    (∑ i, ∑ j, (∑ h, b h i * b h j) * (v i * v j)) =
      ∑ h, (∑ i, b h i * v i) ^ 2 := by
  simp_rw [Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def observationDistance {I : Type*} [Fintype I]
    (b : I → WedgeCoordinate n → ℝ) (xy : Cube n × Cube n) : ℝ :=
  ∑ h, (∑ i, b h i * wedgeFeature xy i) ^ 2

def observationRelation {I : Type*} [Fintype I]
    (b : I → WedgeCoordinate n → ℝ) : Relation n := by
  classical
  exact fun xy ↦ decide (observationDistance b xy = 0)

theorem observationRelation_eq_true {I : Type*} [Fintype I]
    (b : I → WedgeCoordinate n → ℝ) (x y : Cube n) :
    observationRelation b (x, y) = true ↔
      ∀ h, (∑ i, b h i * wedgeFeature (x, y) i) = 0 := by
  simp only [observationRelation, decide_eq_true_eq, observationDistance,
    Finset.sum_sq_eq_zero_iff, Finset.mem_univ, true_implies]

theorem observationRelation_mem {I : Type*} [Fintype I]
    (b : I → WedgeCoordinate n → ℝ) :
    observationRelation b ∈ partitionPatterns n := by
  classical
  let gap (xy : Cube n × Cube n) : ℝ :=
    if observationDistance b xy = 0 then 1 else observationDistance b xy
  have hgap (xy : Cube n × Cube n) : 0 < gap xy := by
    dsimp [gap]
    split
    · norm_num
    · exact lt_of_le_of_ne (Finset.sum_nonneg fun h _ ↦ sq_nonneg _) (Ne.symm ‹_›)
  obtain ⟨ε, hε, hεgap⟩ := PolynomialRootCount.exists_pos_lt_finite gap hgap
  let θ : Parameter n → ℝ :=
    fun v ↦ Option.elim v ε (fun ij ↦ ∑ h, b h ij.1 * b h ij.2)
  have heval (xy : Cube n × Cube n) :
      eval θ (partitionPoly xy) = ε - observationDistance b xy := by
    simp only [partitionPoly, map_sub, map_sum, map_mul, eval_C, eval_X, θ,
      Option.elim_none, Option.elim_some]
    dsimp [observationDistance]
    congr 1
    convert gram_identity b (wedgeFeature xy) using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨θ, fun xy ↦ ?_⟩
  rw [heval]
  by_cases hz : observationDistance b xy = 0
  · simpa [observationRelation, hz] using hε
  · simpa [observationRelation, gap, hz] using sub_neg.mpr (hεgap xy)

theorem mem_represented_of_fiber_affine (hK : 0 < K)
    (E : Relation n) (hE : E ∈ partitionPatterns n)
    (code : Cube n → Fin K) (hcode : IsCode E code)
    (a : Fin K → Option (Fin n) → ℝ) (f : Cube n → Bool)
    (hstrict : ∀ x, if f x then 0 < a (code x) none +
      ∑ i, boolToReal (x i) * a (code x) (some i)
      else a (code x) none + ∑ i, boolToReal (x i) * a (code x) (some i) < 0) :
    f ∈ represented n K hK := by
  classical
  let C := canonicalCode hK E
  have hC : IsCode E C := canonicalCode_isCode hK E ⟨code, hcode⟩
  let θ : AffineParameter n K → ℝ :=
    fun ki ↦ a (code (fiberRepresentative C ki.1)) ki.2
  have hsame (x : Cube n) : code (fiberRepresentative C (C x)) = code x := by
    exact (hcode _ _).mpr ((hC _ _).mp (fiberRepresentative_spec C x))
  have hsame' (x : Cube n) :
      code (fiberRepresentative C (canonicalCode hK E x)) = code x := hsame x
  refine Set.mem_iUnion.mpr ⟨⟨E, hE⟩, θ, fun x ↦ ?_⟩
  simpa only [affinePoly, map_add, map_sum, map_mul, eval_X, eval_C, θ, hsame']
    using hstrict x

open OriginalMarginCapacity CoefficientOrderChart RelativeMarginQuantifiers

def denominatorWedge (phi : Fin H → FracAtom n) :
    (Fin H × Fin H) → WedgeCoordinate n → ℝ :=
  fun hk ij ↦ denominatorCoefficients (phi hk.1) ij.1 *
    denominatorCoefficients (phi hk.2) ij.2

theorem affineValue_eq_sum (a : Coordinate n → ℝ) (x : Cube n) :
    affineValue a x = ∑ i, a i * inputCoordinate x i := by
  simp [affineValue, inputCoordinate, Fintype.sum_option, mul_comm]

theorem denominatorWedge_dot (phi : Fin H → FracAtom n)
    (h k : Fin H) (x y : Cube n) :
    (∑ i, denominatorWedge phi (h, k) i * wedgeFeature (x, y) i) =
      affineValue (denominatorCoefficients (phi h)) x *
        affineValue (denominatorCoefficients (phi k)) y -
      affineValue (denominatorCoefficients (phi h)) y *
        affineValue (denominatorCoefficients (phi k)) x := by
  simp only [denominatorWedge, wedgeFeature, Fintype.sum_prod_type,
    affineValue_eq_sum, Finset.sum_mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

def HasAtMostProjectiveFibers (phi : Fin H → FracAtom n) (K : ℕ) : Prop :=
  ∃ code : Cube n → Fin K, ∀ x y, code x = code y ↔ ∀ h k,
    affineValue (denominatorCoefficients (phi h)) x *
      affineValue (denominatorCoefficients (phi k)) y =
    affineValue (denominatorCoefficients (phi h)) y *
      affineValue (denominatorCoefficients (phi k)) x

theorem denominator_relation (phi : Fin H → FracAtom n) (x y : Cube n) :
    observationRelation (denominatorWedge phi) (x, y) = true ↔ ∀ h k,
      affineValue (denominatorCoefficients (phi h)) x *
        affineValue (denominatorCoefficients (phi k)) y =
      affineValue (denominatorCoefficients (phi h)) y *
        affineValue (denominatorCoefficients (phi k)) x := by
  rw [observationRelation_eq_true]
  simp only [Prod.forall, denominatorWedge_dot, sub_eq_zero]

theorem denominator_pos (phi : FracAtom n) (x : Cube n) :
    0 < affineValue (denominatorCoefficients phi) x := by
  rw [affineValue_denominatorCoefficients]
  exact add_pos_of_pos_of_nonneg phi.hγ (Finset.sum_nonneg fun i _ ↦ (phi.wt_pos x i).le)

/-- Multiplication by one positive denominator makes the score affine on each
projective observation fiber, including the original free bias. -/
theorem exists_projective_fiber_affine_score (phi : Fin H → FracAtom n)
    (h₀ : Fin H) (c : ℝ) (code : Cube n → Fin K)
    (hcode : ∀ x y, code x = code y → ∀ h k,
      affineValue (denominatorCoefficients (phi h)) x *
        affineValue (denominatorCoefficients (phi k)) y =
      affineValue (denominatorCoefficients (phi h)) y *
        affineValue (denominatorCoefficients (phi k)) x) :
    ∃ a : Fin K → Option (Fin n) → ℝ, ∀ x,
      affineValue (denominatorCoefficients (phi h₀)) x * score phi c x =
        a (code x) none + ∑ i, boolToReal (x i) * a (code x) (some i) := by
  let D (k : Fin K) (h : Fin H) : ℝ :=
    affineValue (denominatorCoefficients (phi h)) (fiberRepresentative code k)
  let a (k : Fin K) (i : Option (Fin n)) : ℝ :=
    c * denominatorCoefficients (phi h₀) i +
      ∑ h, numeratorCoefficients (phi h) i * (D k h₀ / D k h)
  refine ⟨a, fun x ↦ ?_⟩
  have hratio (h : Fin H) :
      affineValue (denominatorCoefficients (phi h₀)) x /
        affineValue (denominatorCoefficients (phi h)) x = D (code x) h₀ / D (code x) h := by
    apply (div_eq_div_iff (denominator_pos _ _).ne' (denominator_pos _ _).ne').mpr
    exact (hcode x _ (fiberRepresentative_spec code x).symm h₀ h)
  have hterm (h : Fin H) :
      affineValue (denominatorCoefficients (phi h₀)) x * (phi h).eval x =
      affineValue (numeratorCoefficients (phi h)) x * (D (code x) h₀ / D (code x) h) := by
    rw [← affineRatio_eq_eval]
    calc
      _ = affineValue (numeratorCoefficients (phi h)) x *
          (affineValue (denominatorCoefficients (phi h₀)) x /
            affineValue (denominatorCoefficients (phi h)) x) := by ring
      _ = _ := by rw [hratio]
  simp only [score, mul_add, Finset.mul_sum, hterm]
  simp only [a, affineValue, add_mul, Finset.sum_mul, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  ring_nf
  have hc (h : Fin H) : numeratorCoefficients (phi h) none * D (code x) h₀ *
      (D (code x) h)⁻¹ = D (code x) h₀ * numeratorCoefficients (phi h) none *
      (D (code x) h)⁻¹ := by ring
  simp_rw [hc]
  ring

/-- Exact bridge from genuine original heads, with arbitrary cancellation. -/
theorem mem_represented_of_original (hK : 0 < K)
    (phi : Fin H → FracAtom n) (h₀ : Fin H) (c : ℝ) (f : Cube n → Bool)
    (hfibers : HasAtMostProjectiveFibers phi K) (hstrict : StrictlyRepresents f phi c) :
    f ∈ represented n K hK := by
  obtain ⟨code, hcode⟩ := hfibers
  let E := observationRelation (denominatorWedge phi)
  have hE : E ∈ partitionPatterns n := observationRelation_mem _
  have hc : IsCode E code := by
    intro x y
    exact (hcode x y).trans (denominator_relation phi x y).symm
  obtain ⟨a, ha⟩ := exists_projective_fiber_affine_score phi h₀ c code
    (fun x y hxy ↦ (hcode x y).mp hxy)
  apply mem_represented_of_fiber_affine hK E hE code hc a f
  intro x
  have hs := hstrict x
  have hd := denominator_pos (phi h₀) x
  rw [← ha x]
  cases hf : f x <;> simp [signedLabel, hf] at hs ⊢ <;> nlinarith

def originalFunctions (n K : ℕ) : Set (Cube n → Bool) :=
  {f | ∃ (H : ℕ) (phi : Fin H → FracAtom n) (_h₀ : Fin H) (c : ℝ),
    HasAtMostProjectiveFibers phi K ∧ StrictlyRepresents f phi c}

theorem originalFunctions_subset (hK : 0 < K) :
    originalFunctions n K ⊆ represented n K hK := by
  rintro f ⟨H, phi, h₀, c, hf, hs⟩
  exact mem_represented_of_original hK phi h₀ c f hf hs

theorem card_originalFunctions_le (hK : 0 < K)
    (hpartition : 1 + (n + 1) ^ 4 ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    ((originalFunctions n K).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((2 : ℝ) ^ n) ^ 2 / (1 + ((n : ℝ) + 1) ^ 4)) ^
        (1 + (n + 1) ^ 4) *
      (4 * Real.exp 1 * (2 : ℝ) ^ n / (((n : ℝ) + 1) * K)) ^ ((n + 1) * K) := by
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard (originalFunctions_subset hK))).trans
    (card_represented_le hK hpartition haffine)

/-- A simple integral exponent, useful without logarithmic estimates. -/
theorem card_represented_le_pow (hK : 0 < K)
    (hpartition : 1 + (n + 1) ^ 4 ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    (represented n K hK).ncard ≤
      2 ^ ((2 * n + 4) * (1 + (n + 1) ^ 4) + (n + 4) * ((n + 1) * K)) := by
  classical
  let := Fintype.ofFinite (partitionPatterns n)
  have hpart : (partitionPatterns n).ncard ≤
      (12 * ((2 ^ n) ^ 2)) ^ (1 + (n + 1) ^ 4) := by
    have hp : Fintype.card (Parameter n) = 1 + (n + 1) ^ 4 := by
      simp [Parameter, WedgeCoordinate, Coordinate]; ring
    have hi : Fintype.card (Cube n × Cube n) = (2 ^ n) ^ 2 := by
      simp [Cube, Fintype.card_bool, pow_two]
    simpa [partitionPatterns] using coarseWarrenSignPatternBound ((2 ^ n) ^ 2) 1
      (1 + (n + 1) ^ 4) (by omega) (by omega) hpartition (Cube n × Cube n)
      (Parameter n) partitionPoly hi hp partitionPoly_totalDegree_le
  have haff (code : Cube n → Fin K) :
      (strictPolynomialSignPatterns (affinePoly code)).ncard ≤
        (12 * 2 ^ n) ^ ((n + 1) * K) := by
    have hp : Fintype.card (AffineParameter n K) = (n + 1) * K := by
      simp [AffineParameter]; ring
    have hi : Fintype.card (Cube n) = 2 ^ n := by simp [Cube, Fintype.card_bool]
    simpa using coarseWarrenSignPatternBound (2 ^ n) 1 ((n + 1) * K)
      (by omega) (Nat.mul_pos (by omega) hK) haffine (Cube n) (AffineParameter n K)
      (affinePoly code) hi hp (affinePoly_totalDegree_le code)
  have hunion : (represented n K hK).ncard ≤
      (partitionPatterns n).ncard * (12 * 2 ^ n) ^ ((n + 1) * K) := by
    calc
      _ ≤ ∑ E : partitionPatterns n,
          (strictPolynomialSignPatterns (affinePoly (canonicalCode hK E.val))).ncard :=
        Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _E : partitionPatterns n, (12 * 2 ^ n) ^ ((n + 1) * K) :=
        Finset.sum_le_sum fun E _ ↦ haff _
      _ = _ := by simp [Set.fintypeCard_eq_ncard]
  have hb1 : 12 * ((2 ^ n) ^ 2) ≤ 2 ^ (2 * n + 4) := by
    rw [pow_add, ← pow_mul]
    have he : n * 2 = 2 * n := by omega
    rw [he]
    norm_num
    omega
  have hb2 : 12 * 2 ^ n ≤ 2 ^ (n + 4) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _ ≤ (12 * ((2 ^ n) ^ 2)) ^ (1 + (n + 1) ^ 4) *
        (12 * 2 ^ n) ^ ((n + 1) * K) :=
      hunion.trans (Nat.mul_le_mul_right _ hpart)
    _ ≤ (2 ^ (2 * n + 4)) ^ (1 + (n + 1) ^ 4) *
        (2 ^ (n + 4)) ^ ((n + 1) * K) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb1 _) (Nat.pow_le_pow_left hb2 _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]

theorem card_originalFunctions_le_pow (hK : 0 < K)
    (hpartition : 1 + (n + 1) ^ 4 ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    (originalFunctions n K).ncard ≤
      2 ^ ((2 * n + 4) * (1 + (n + 1) ^ 4) + (n + 4) * ((n + 1) * K)) :=
  (Set.ncard_le_ncard (originalFunctions_subset hK)).trans
    (card_represented_le_pow hK hpartition haffine)

theorem card_originalFunctions_le_half_tables (hK : 0 < K)
    (hpartition : 1 + (n + 1) ^ 4 ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n)
    (hbudget : (2 * n + 4) * (1 + (n + 1) ^ 4) + (n + 4) * ((n + 1) * K) ≤ 2 ^ n / 2) :
    (originalFunctions n K).ncard ≤ 2 ^ (2 ^ n / 2) :=
  (card_originalFunctions_le_pow hK hpartition haffine).trans
    (Nat.pow_le_pow_right (by omega) hbudget)

end HeadComplexity.ProjectiveFiberCapacity
