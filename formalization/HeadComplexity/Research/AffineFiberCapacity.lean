import HeadComplexity.Research.OriginalMarginCapacity

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-! Margin-free capacity for scores affine on common affine-observation fibers. -/

noncomputable section
namespace HeadComplexity.AffineFiberCapacity
open Finset MvPolynomial
open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev Relation (n : ℕ) := Cube n × Cube n → Bool
abbrev PartitionParameter (n : ℕ) := Option (Fin n × Fin n)
abbrev AffineParameter (n K : ℕ) := Fin K × Option (Fin n)

variable {n K H : ℕ}

def bitDifference (x y : Cube n) (i : Fin n) : ℝ :=
  boolToReal (x i) - boolToReal (y i)

def partitionPoly (xy : Cube n × Cube n) : MvPolynomial (PartitionParameter n) ℝ :=
  X none - ∑ i, ∑ j, C (bitDifference xy.1 xy.2 i * bitDifference xy.1 xy.2 j) *
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

def IsCode (E : Relation n) (code : Cube n → Fin K) : Prop :=
  ∀ x y, code x = code y ↔ E (x, y) = true

def canonicalCode (hK : 0 < K) (E : Relation n) : Cube n → Fin K := by
  classical
  exact if h : ∃ code : Cube n → Fin K, IsCode E code then Classical.choose h
  else fun _ ↦ ⟨0, hK⟩

theorem canonicalCode_isCode (hK : 0 < K) (E : Relation n)
    (h : ∃ code : Cube n → Fin K, IsCode E code) :
    IsCode E (canonicalCode hK E) := by
  simp only [canonicalCode, dite_eq_left h]
  exact Classical.choose_spec h

def affinePoly (code : Cube n → Fin K) (x : Cube n) :
    MvPolynomial (AffineParameter n K) ℝ :=
  X (code x, none) + ∑ i, C (boolToReal (x i)) * X (code x, some i)

theorem affinePoly_totalDegree_le (code : Cube n → Fin K) (x : Cube n) :
    (affinePoly code x).totalDegree ≤ 1 := by
  unfold affinePoly
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

def represented (n K : ℕ) (hK : 0 < K) : Set (Cube n → Bool) :=
  ⋃ E : partitionPatterns n,
    strictPolynomialSignPatterns (affinePoly (canonicalCode hK E.val))

theorem card_partitionPatterns_le (hparameters : 1 + n * n ≤ (2 ^ n) ^ 2) :
    ((partitionPatterns n).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((2 : ℝ) ^ n) ^ 2 / (1 + (n : ℝ) * n)) ^ (1 + n * n) := by
  have hp : Fintype.card (PartitionParameter n) = 1 + n * n := by
    simp [PartitionParameter]
    omega
  have hi : Fintype.card (Cube n × Cube n) = (2 ^ n) ^ 2 := by
    simp [Cube, Fintype.card_bool, pow_two]
  have h := warrenStrictSignPatternBound ((2 ^ n) ^ 2) 1 (1 + n * n)
    (by omega) (by omega) hparameters (Cube n × Cube n) (PartitionParameter n)
    partitionPoly hi hp partitionPoly_totalDegree_le
  simpa [partitionPatterns] using h

theorem card_affinePatterns_le (code : Cube n → Fin K) (hK : 0 < K)
    (hparameters : (n + 1) * K ≤ 2 ^ n) :
    ((strictPolynomialSignPatterns (affinePoly code)).ncard : ℝ) ≤
      (4 * Real.exp 1 * (2 : ℝ) ^ n / (((n : ℝ) + 1) * K)) ^ ((n + 1) * K) := by
  have hp : Fintype.card (AffineParameter n K) = (n + 1) * K := by
    simp [AffineParameter]
    ring
  have hi : Fintype.card (Cube n) = 2 ^ n := by simp [Cube, Fintype.card_bool]
  have h := warrenStrictSignPatternBound (2 ^ n) 1 ((n + 1) * K)
    (by omega) (Nat.mul_pos (by omega) hK) hparameters (Cube n) (AffineParameter n K)
    (affinePoly code) hi hp (affinePoly_totalDegree_le code)
  simpa using h

/-- All joint observation partitions are charged independently of head count. -/
theorem card_represented_le (hK : 0 < K)
    (hpartition : 1 + n * n ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    ((represented n K hK).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((2 : ℝ) ^ n) ^ 2 / (1 + (n : ℝ) * n)) ^ (1 + n * n) *
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

/-- The Gram matrix encodes any number of affine observations. -/
theorem gram_identity (b : Fin H → Fin n → ℝ) (x y : Cube n) :
    (∑ i, ∑ j, (∑ h, b h i * b h j) *
      (bitDifference x y i * bitDifference x y j)) =
    ∑ h, (∑ i, b h i * bitDifference x y i) ^ 2 := by
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


def observationDistance (b : Fin H → Fin n → ℝ) (xy : Cube n × Cube n) : ℝ :=
  ∑ h, (∑ i, b h i * bitDifference xy.1 xy.2 i) ^ 2

def observationRelation (b : Fin H → Fin n → ℝ) : Relation n := by
  classical
  exact fun xy ↦ decide (observationDistance b xy = 0)

theorem observationRelation_eq_true (b : Fin H → Fin n → ℝ) (x y : Cube n) :
    observationRelation b (x, y) = true ↔
      ∀ h, (∑ i, b h i * boolToReal (x i)) = ∑ i, b h i * boolToReal (y i) := by
  simp only [observationRelation, decide_eq_true_eq, observationDistance,
    Finset.sum_sq_eq_zero_iff, Finset.mem_univ, true_implies]
  simp_rw [bitDifference, mul_sub, Finset.sum_sub_distrib, sub_eq_zero]

/-- Every joint affine-observation equality partition occurs in the polynomial
comparison family, without any coefficient-height hypothesis. -/
theorem observationRelation_mem (b : Fin H → Fin n → ℝ) :
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
  let θ : PartitionParameter n → ℝ :=
    fun v ↦ Option.elim v ε (fun ij ↦ ∑ h, b h ij.1 * b h ij.2)
  have heval (xy : Cube n × Cube n) :
      eval θ (partitionPoly xy) = ε - observationDistance b xy := by
    simp only [partitionPoly, map_sub, map_sum, map_mul, eval_C, eval_X, θ,
      Option.elim_none, Option.elim_some]
    dsimp [observationDistance]
    congr 1
    convert gram_identity b xy.1 xy.2 using 1
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

def fiberRepresentative (code : Cube n → Fin K) (k : Fin K) : Cube n := by
  classical
  exact if h : ∃ x, code x = k then Classical.choose h else fun _ ↦ false

theorem fiberRepresentative_spec (code : Cube n → Fin K) (x : Cube n) :
    code (fiberRepresentative code (code x)) = code x := by
  classical
  have h : ∃ y, code y = code x := ⟨x, rfl⟩
  simp only [fiberRepresentative, dite_eq_left h]
  exact Classical.choose_spec h

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

/-- This means that the complete denominator observation vector assumes at
most K values; no predetermined observation map or codebook is imposed. -/
def HasAtMostFibers (phi : Fin H → FracAtom n) (K : ℕ) : Prop :=
  ∃ code : Cube n → Fin K, ∀ x y,
    code x = code y ↔ ∀ h,
      affineValue (denominatorCoefficients (phi h)) x =
        affineValue (denominatorCoefficients (phi h)) y

theorem denominator_relation (phi : Fin H → FracAtom n) (x y : Cube n) :
    observationRelation (fun h i ↦ denominatorCoefficients (phi h) (some i)) (x, y) = true ↔
      ∀ h, affineValue (denominatorCoefficients (phi h)) x =
        affineValue (denominatorCoefficients (phi h)) y := by
  rw [observationRelation_eq_true]
  simp only [affineValue, add_right_inj]
  simp only [mul_comm]

/-- The original score is affine on each joint denominator fiber. -/
theorem exists_fiber_affine_score (phi : Fin H → FracAtom n) (c : ℝ)
    (code : Cube n → Fin K)
    (hcode : ∀ x y, code x = code y → ∀ h,
      affineValue (denominatorCoefficients (phi h)) x =
        affineValue (denominatorCoefficients (phi h)) y) :
    ∃ a : Fin K → Option (Fin n) → ℝ, ∀ x,
      score phi c x = a (code x) none + ∑ i, boolToReal (x i) * a (code x) (some i) := by
  let D (k : Fin K) (h : Fin H) : ℝ :=
    affineValue (denominatorCoefficients (phi h)) (fiberRepresentative code k)
  let a (k : Fin K) : Option (Fin n) → ℝ
    | none => c + ∑ h, numeratorCoefficients (phi h) none / D k h
    | some i => ∑ h, numeratorCoefficients (phi h) (some i) / D k h
  refine ⟨a, fun x ↦ ?_⟩
  have hD (h : Fin H) : D (code x) h =
      affineValue (denominatorCoefficients (phi h)) x :=
    hcode _ _ (fiberRepresentative_spec code x) h
  unfold score
  simp_rw [← affineRatio_eq_eval, affineValue, add_div, Finset.sum_div]
  simp only [a, hD]
  dsimp only [affineValue]
  rw [Finset.sum_add_distrib, add_assoc]
  congr 2
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc]

/-- Exact bridge from genuine original heads, with arbitrary real numerators,
signed cancellation, bias, and target-dependent denominator observations. -/
theorem mem_represented_of_original (hK : 0 < K)
    (phi : Fin H → FracAtom n) (c : ℝ) (f : Cube n → Bool)
    (hfibers : HasAtMostFibers phi K) (hstrict : StrictlyRepresents f phi c) :
    f ∈ represented n K hK := by
  obtain ⟨code, hcode⟩ := hfibers
  let E := observationRelation (fun h i ↦ denominatorCoefficients (phi h) (some i))
  have hE : E ∈ partitionPatterns n := observationRelation_mem _
  have hc : IsCode E code := by
    intro x y
    exact (hcode x y).trans (denominator_relation phi x y).symm
  obtain ⟨a, ha⟩ := exists_fiber_affine_score phi c code
    (fun x y hxy ↦ (hcode x y).mp hxy)
  apply mem_represented_of_fiber_affine hK E hE code hc a f
  intro x
  have hs := hstrict x
  rw [ha x] at hs
  cases hf : f x <;> simp [signedLabel, hf] at hs ⊢ <;> linarith

def originalFunctions (n K : ℕ) : Set (Cube n → Bool) :=
  {f | ∃ (H : ℕ) (phi : Fin H → FracAtom n) (c : ℝ),
    HasAtMostFibers phi K ∧ StrictlyRepresents f phi c}

theorem originalFunctions_subset (hK : 0 < K) :
    originalFunctions n K ⊆ represented n K hK := by
  rintro f ⟨H, phi, c, hf, hs⟩
  exact mem_represented_of_original hK phi c f hf hs

/-- The count is independent of the original number of heads. -/
theorem card_originalFunctions_le (hK : 0 < K)
    (hpartition : 1 + n * n ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    ((originalFunctions n K).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((2 : ℝ) ^ n) ^ 2 / (1 + (n : ℝ) * n)) ^ (1 + n * n) *
      (4 * Real.exp 1 * (2 : ℝ) ^ n / (((n : ℝ) + 1) * K)) ^ ((n + 1) * K) := by
  exact (Nat.cast_le.mpr (Set.ncard_le_ncard (originalFunctions_subset hK))).trans
    (card_represented_le hK hpartition haffine)


/-- A simple integral exponent, useful without logarithmic estimates. -/
theorem card_represented_le_pow (hK : 0 < K)
    (hpartition : 1 + n * n ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    (represented n K hK).ncard ≤
      2 ^ ((2 * n + 4) * (1 + n * n) + (n + 4) * ((n + 1) * K)) := by
  classical
  let := Fintype.ofFinite (partitionPatterns n)
  have hpart : (partitionPatterns n).ncard ≤
      (12 * ((2 ^ n) ^ 2)) ^ (1 + n * n) := by
    have hp : Fintype.card (PartitionParameter n) = 1 + n * n := by
      simp [PartitionParameter]; omega
    have hi : Fintype.card (Cube n × Cube n) = (2 ^ n) ^ 2 := by
      simp [Cube, Fintype.card_bool, pow_two]
    simpa [partitionPatterns] using coarseWarrenSignPatternBound ((2 ^ n) ^ 2) 1
      (1 + n * n) (by omega) (by omega) hpartition (Cube n × Cube n)
      (PartitionParameter n) partitionPoly hi hp partitionPoly_totalDegree_le
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
    _ ≤ (12 * ((2 ^ n) ^ 2)) ^ (1 + n * n) *
        (12 * 2 ^ n) ^ ((n + 1) * K) :=
      hunion.trans (Nat.mul_le_mul_right _ hpart)
    _ ≤ (2 ^ (2 * n + 4)) ^ (1 + n * n) *
        (2 ^ (n + 4)) ^ ((n + 1) * K) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb1 _) (Nat.pow_le_pow_left hb2 _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]

theorem card_originalFunctions_le_pow (hK : 0 < K)
    (hpartition : 1 + n * n ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n) :
    (originalFunctions n K).ncard ≤
      2 ^ ((2 * n + 4) * (1 + n * n) + (n + 4) * ((n + 1) * K)) :=
  (Set.ncard_le_ncard (originalFunctions_subset hK)).trans
    (card_represented_le_pow hK hpartition haffine)

theorem card_originalFunctions_le_half_tables (hK : 0 < K)
    (hpartition : 1 + n * n ≤ (2 ^ n) ^ 2)
    (haffine : (n + 1) * K ≤ 2 ^ n)
    (hbudget : (2 * n + 4) * (1 + n * n) + (n + 4) * ((n + 1) * K) ≤ 2 ^ n / 2) :
    (originalFunctions n K).ncard ≤ 2 ^ (2 ^ n / 2) :=
  (card_originalFunctions_le_pow hK hpartition haffine).trans
    (Nat.pow_le_pow_right (by omega) hbudget)

end HeadComplexity.AffineFiberCapacity
