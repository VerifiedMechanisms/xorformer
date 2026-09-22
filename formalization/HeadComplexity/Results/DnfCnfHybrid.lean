import HeadComplexity.Results.AffineCylinderThreshold
import HeadComplexity.Results.DummyVariables
import HeadComplexity.Results.PositiveWeightedSignDegree
import HeadComplexity.Results.StructuralInvariances
import HeadComplexity.Results.WeightedUpperBound

set_option linter.style.header false

/-!
# DNF and CNF hybrid upper bounds

This file formalizes theorem 73.  Formula terms and clauses are nonempty,
consistent cylinders on exactly the displayed used-variable cube.  Four
independent certificates are retained: sparse volume, oriented literal
expansion, universal junta interpolation, and width-degree sparsity.
-/

namespace HeadComplexity

open Finset Polynomial
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {n v s : ℕ} {f : (Fin n → Bool) → Bool}

/-! ## Sparse-support upper bound -/

/-- Inputs on which a Boolean function is true. -/
def trueSupport (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun bits ↦ f bits = true

/-- Inputs on which a Boolean function is false. -/
def falseSupport (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun bits ↦ f bits = false

/-- The injective binary statistic used by the sparse-support certificate. -/
noncomputable def binaryStatistic (bits : Fin n → Bool) : ℝ :=
  wT (fun i ↦ (2 : ℝ) ^ (i : ℕ)) bits

theorem binaryStatistic_injective :
    Function.Injective (binaryStatistic (n := n)) := by
  change Function.Injective (wT (fun i : Fin n ↦ (2 : ℝ) ^ (i : ℕ)))
  exact wT_two_pow_injective

/-- Product vanishing precisely on the true support. -/
noncomputable def sparseVanishingValue (f : (Fin n → Bool) → Bool)
    (bits : Fin n → Bool) : ℝ :=
  ∏ target ∈ trueSupport f,
    (binaryStatistic bits - binaryStatistic target) ^ 2

theorem sparseVanishingValue_pos_of_false
    (f : (Fin n → Bool) → Bool) {bits : Fin n → Bool}
    (hbits : f bits = false) : 0 < sparseVanishingValue f bits := by
  classical
  unfold sparseVanishingValue
  apply Finset.prod_pos
  intro target htarget
  have htarget' : f target = true := by
    simpa [trueSupport] using htarget
  have hne : bits ≠ target := by
    intro h
    subst target
    simp [hbits] at htarget'
  have hstat : binaryStatistic bits - binaryStatistic target ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h ↦ hne (binaryStatistic_injective h)
  positivity

/-- The least positive vanishing-product value on a nonempty false support. -/
noncomputable def sparseGap (f : (Fin n → Bool) → Bool)
    (hfalse : (falseSupport f).Nonempty) : ℝ :=
  (falseSupport f).inf' hfalse (sparseVanishingValue f)

theorem sparseGap_pos (f : (Fin n → Bool) → Bool)
    (hfalse : (falseSupport f).Nonempty) : 0 < sparseGap f hfalse := by
  rw [sparseGap, Finset.lt_inf'_iff]
  intro bits hbits
  exact sparseVanishingValue_pos_of_false f (Finset.mem_filter.mp hbits).2

theorem sparseGap_le (f : (Fin n → Bool) → Bool)
    (hfalse : (falseSupport f).Nonempty) {bits : Fin n → Bool}
    (hbits : f bits = false) :
    sparseGap f hfalse ≤ sparseVanishingValue f bits := by
  rw [sparseGap]
  exact Finset.inf'_le (sparseVanishingValue f)
    (by simp [falseSupport, hbits])

/-- A degree-`2 |f⁻¹(1)|` polynomial which is positive exactly on the true
support. -/
noncomputable def sparseSignPolynomial
    (f : (Fin n → Bool) → Bool) (hfalse : (falseSupport f).Nonempty) : ℝ[X] :=
  Polynomial.C (sparseGap f hfalse / 2) -
    ∏ target ∈ trueSupport f,
      (Polynomial.X - Polynomial.C (binaryStatistic target)) ^ 2

theorem sparseSignPolynomial_natDegree_le
    (f : (Fin n → Bool) → Bool) (hfalse : (falseSupport f).Nonempty) :
    (sparseSignPolynomial f hfalse).natDegree ≤ 2 * (trueSupport f).card := by
  classical
  unfold sparseSignPolynomial
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine (Polynomial.natDegree_prod_le
      (fun target ↦
        (Polynomial.X - Polynomial.C (binaryStatistic target)) ^ 2)
      (s := trueSupport f)).trans ?_
    calc
      (∑ target ∈ trueSupport f,
          ((Polynomial.X - Polynomial.C (binaryStatistic target)) ^ 2).natDegree) ≤
          ∑ _target ∈ trueSupport f, 2 := by
            apply Finset.sum_le_sum
            intro target _
            exact Polynomial.natDegree_pow_le.trans (by simp)
      _ = 2 * (trueSupport f).card := by simp [mul_comm]

theorem sparseSignPolynomial_eval
    (f : (Fin n → Bool) → Bool) (hfalse : (falseSupport f).Nonempty)
    (bits : Fin n → Bool) :
    (sparseSignPolynomial f hfalse).eval (binaryStatistic bits) =
      sparseGap f hfalse / 2 - sparseVanishingValue f bits := by
  simp only [sparseSignPolynomial, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_X]
  rfl

theorem sparseSignPolynomial_sign
    (f : (Fin n → Bool) → Bool) (hfalse : (falseSupport f).Nonempty)
    (bits : Fin n → Bool) :
    0 < (sparseSignPolynomial f hfalse).eval (binaryStatistic bits) ↔
      f bits = true := by
  rw [sparseSignPolynomial_eval]
  cases hbit : f bits with
  | false =>
      have hle := sparseGap_le f hfalse hbit
      have hpos := sparseGap_pos f hfalse
      simp only [Bool.false_eq_true, iff_false]
      linarith
  | true =>
      have hmem : bits ∈ trueSupport f := by simp [trueSupport, hbit]
      have hzero : sparseVanishingValue f bits = 0 := by
        unfold sparseVanishingValue
        apply Finset.prod_eq_zero hmem
        simp
      rw [hzero]
      simp only [iff_true]
      linarith [sparseGap_pos f hfalse]

/-- A nonconstant function has a positive weighted sign certificate costing
twice the size of its true support. -/
theorem positiveWeightedSignDegLE_two_mul_trueSupport
    (f : (Fin n → Bool) → Bool) (hfalse : (falseSupport f).Nonempty) :
    PositiveWeightedSignDegLE f (2 * (trueSupport f).card) := by
  refine ⟨(fun i ↦ (2 : ℝ) ^ (i : ℕ)), (fun _ ↦ by positivity), ?_⟩
  exact ⟨sparseSignPolynomial f hfalse,
    sparseSignPolynomial_natDegree_le f hfalse,
    sparseSignPolynomial_sign f hfalse⟩

/-- Sparse true support gives the theorem-37 upper bound. -/
theorem HStar_le_two_mul_trueSupport
    (f : (Fin n → Bool) → Bool) (hfalse : (falseSupport f).Nonempty) :
    HStar n f ≤ 2 * (trueSupport f).card :=
  HStar_le_of_computableWithHeadsN
    (positiveWeightedSignDegLE_two_mul_trueSupport f hfalse).computable

theorem trueSupport_nonempty_of_nonconstant
    (f : (Fin n → Bool) → Bool) (hnonconstant : ¬ ∀ x y, f x = f y) :
    (trueSupport f).Nonempty := by
  push Not at hnonconstant
  obtain ⟨x, y, hxy⟩ := hnonconstant
  cases hx : f x <;> cases hy : f y
  · exact (hxy (by rw [hx, hy])).elim
  · exact ⟨y, by simp [trueSupport, hy]⟩
  · exact ⟨x, by simp [trueSupport, hx]⟩
  · exact (hxy (by rw [hx, hy])).elim

theorem falseSupport_nonempty_of_nonconstant
    (f : (Fin n → Bool) → Bool) (hnonconstant : ¬ ∀ x y, f x = f y) :
    (falseSupport f).Nonempty := by
  push Not at hnonconstant
  obtain ⟨x, y, hxy⟩ := hnonconstant
  cases hx : f x <;> cases hy : f y
  · exact ⟨x, by simp [falseSupport, hx]⟩
  · exact ⟨x, by simp [falseSupport, hx]⟩
  · exact ⟨y, by simp [falseSupport, hy]⟩
  · exact (hxy (by rw [hx, hy])).elim

/-! ## Exact formula certificates -/

theorem CubeCylinder.eval_eq_zero_or_one (C : CubeCylinder n)
    (bits : Fin n → Bool) : C.eval bits = 0 ∨ C.eval bits = 1 := by
  classical
  by_cases hp : ∀ i ∈ C.positive, bits i = true
  · have hpone : (∏ i ∈ C.positive, boolToReal (bits i)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [boolToReal, hp i hi]
    by_cases hn : ∀ i ∈ C.negative, bits i = false
    · right
      simp only [CubeCylinder.eval, hpone, one_mul]
      apply Finset.prod_eq_one
      intro i hi
      simp [boolToReal, hn i hi]
    · left
      push Not at hn
      obtain ⟨i, hi, hne⟩ := hn
      have htrue : bits i = true := by cases h : bits i <;> simp_all
      simp only [CubeCylinder.eval, hpone, one_mul]
      apply Finset.prod_eq_zero hi
      simp [boolToReal, htrue]
  · left
    push Not at hp
    obtain ⟨i, hi, hne⟩ := hp
    have hfalse : bits i = false := by cases h : bits i <;> simp_all
    simp only [CubeCylinder.eval]
    apply mul_eq_zero.mpr
    left
    apply Finset.prod_eq_zero hi
    simp [boolToReal, hfalse]

theorem CubeCylinder.eval_nonneg (C : CubeCylinder n)
    (bits : Fin n → Bool) : 0 ≤ C.eval bits := by
  rcases C.eval_eq_zero_or_one bits with h | h <;> simp [h]

theorem CubeCylinder.eval_eq_one_iff (C : CubeCylinder n)
    (bits : Fin n → Bool) :
    C.eval bits = 1 ↔
      (∀ i ∈ C.positive, bits i = true) ∧
      (∀ i ∈ C.negative, bits i = false) := by
  constructor
  · intro heval
    constructor
    · intro i hi
      cases hbit : bits i with
      | false =>
          have hzero : C.eval bits = 0 := by
            unfold CubeCylinder.eval
            apply mul_eq_zero.mpr
            left
            apply Finset.prod_eq_zero hi
            simp [boolToReal, hbit]
          linarith
      | true => rfl
    · intro i hi
      cases hbit : bits i with
      | false => rfl
      | true =>
          have hzero : C.eval bits = 0 := by
            unfold CubeCylinder.eval
            apply mul_eq_zero.mpr
            right
            apply Finset.prod_eq_zero hi
            simp [boolToReal, hbit]
          linarith
  · rintro ⟨hp, hn⟩
    unfold CubeCylinder.eval
    rw [show (∏ i ∈ C.positive, boolToReal (bits i)) = 1 by
      apply Finset.prod_eq_one
      intro i hi
      simp [boolToReal, hp i hi]]
    rw [show (∏ i ∈ C.negative, (1 - boolToReal (bits i))) = 1 by
      apply Finset.prod_eq_one
      intro i hi
      simp [boolToReal, hn i hi]]
    norm_num

/-- Assignments satisfying a cylinder. -/
abbrev CubeCylinder.Satisfies (C : CubeCylinder n) :=
  {bits : Fin n → Bool // C.eval bits = 1}

/-- Coordinates not fixed by a cylinder. -/
abbrev CubeCylinder.FreeCoordinate (C : CubeCylinder n) :=
  {i : Fin n // i ∉ C.positive ∪ C.negative}

/-- A satisfying assignment is freely and uniquely determined on the
coordinates outside the cylinder support. -/
noncomputable def CubeCylinder.satisfiesEquivFreeBits (C : CubeCylinder n) :
    C.Satisfies ≃ (C.FreeCoordinate → Bool) where
  toFun bits i := bits.1 i.1
  invFun free := ⟨fun i ↦
      if hiP : i ∈ C.positive then true
      else if hiN : i ∈ C.negative then false
      else free ⟨i, by simp [hiP, hiN]⟩, by
    rw [C.eval_eq_one_iff]
    constructor
    · intro i hi
      simp [hi]
    · intro i hi
      have hnotP : i ∉ C.positive := by
        intro hiP
        exact (Finset.disjoint_left.mp C.disjoint hiP hi).elim
      simp [hnotP, hi]⟩
  left_inv bits := by
    apply Subtype.ext
    funext i
    by_cases hiP : i ∈ C.positive
    · have h := (C.eval_eq_one_iff bits.1).mp bits.2
      simp [hiP, h.1 i hiP]
    · by_cases hiN : i ∈ C.negative
      · have h := (C.eval_eq_one_iff bits.1).mp bits.2
        simp [hiP, hiN, h.2 i hiN]
      · simp [hiP, hiN]
  right_inv free := by
    funext i
    have hiP : i.1 ∉ C.positive := fun h ↦ i.2 (Finset.mem_union_left _ h)
    have hiN : i.1 ∉ C.negative := fun h ↦ i.2 (Finset.mem_union_right _ h)
    simp [hiP, hiN]

/-- The finite support of a cylinder. -/
noncomputable def CubeCylinder.support (C : CubeCylinder n) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun bits ↦ C.eval bits = 1

/-- A width-`w` cylinder on the `n`-cube contains exactly `2^(n-w)` points. -/
theorem CubeCylinder.support_card (C : CubeCylinder n) :
    C.support.card = 2 ^ (n - (C.positive ∪ C.negative).card) := by
  classical
  calc
    C.support.card = Fintype.card C.Satisfies := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card (C.FreeCoordinate → Bool) :=
      Fintype.card_congr C.satisfiesEquivFreeBits
    _ = 2 ^ Fintype.card C.FreeCoordinate := by simp
    _ = 2 ^ (n - (C.positive ∪ C.negative).card) := by
      congr 1
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_fin]
      congr 1
      exact Fintype.card_coe _

/-- The usual multilinear polynomial indicator of a Boolean cylinder. -/
noncomputable def CubeCylinder.polynomial (C : CubeCylinder n) :
    MvPolynomial (Fin n) ℝ :=
  (∏ i ∈ C.positive, MvPolynomial.X i) *
    ∏ i ∈ C.negative, (MvPolynomial.C 1 - MvPolynomial.X i)

@[simp] theorem CubeCylinder.polynomial_eval (C : CubeCylinder n)
    (bits : Fin n → Bool) :
    MvPolynomial.eval (cubePoint bits) C.polynomial = C.eval bits := by
  simp [CubeCylinder.polynomial, CubeCylinder.eval, cubePoint]

theorem CubeCylinder.polynomial_totalDegree_le (C : CubeCylinder n) :
    C.polynomial.totalDegree ≤ (C.positive ∪ C.negative).card := by
  have hp :
      (∏ i ∈ C.positive,
        (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤
        C.positive.card := by
    exact totalDegree_prod_le_card C.positive MvPolynomial.X (fun i ↦ by simp)
  have hn :
      (∏ i ∈ C.negative,
        (MvPolynomial.C 1 - MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤
        C.negative.card := by
    apply totalDegree_prod_le_card C.negative
    intro i
    exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  unfold CubeCylinder.polynomial
  calc
    ((∏ i ∈ C.positive,
          (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) *
        ∏ i ∈ C.negative,
          (MvPolynomial.C 1 - MvPolynomial.X i)).totalDegree ≤
        (∏ i ∈ C.positive,
          (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree +
        (∏ i ∈ C.negative,
          (MvPolynomial.C 1 - MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ C.positive.card + C.negative.card := Nat.add_le_add hp hn
    _ = (C.positive ∪ C.negative).card := by
      rw [Finset.card_union_of_disjoint C.disjoint]

/-- A DNF on exactly `n` used variables, indexed by `Fin s`. -/
structure DNFFormulaCertificate (n s : ℕ)
    (f : (Fin n → Bool) → Bool) where
  term : Fin s → CubeCylinder n
  term_nonempty : ∀ a, (term a).positive ∪ (term a).negative |>.Nonempty
  uses_every_variable :
    (Finset.univ.biUnion fun a ↦ (term a).positive ∪ (term a).negative) =
      Finset.univ
  represents : ∀ bits, f bits = true ↔ ∃ a, (term a).eval bits = 1

namespace DNFFormulaCertificate

/-- Width of one DNF term. -/
def termWidth (C : DNFFormulaCertificate n s f) (a : Fin s) : ℕ :=
  ((C.term a).positive ∪ (C.term a).negative).card

/-- Maximum DNF width. -/
def width (C : DNFFormulaCertificate n s f) : ℕ :=
  Finset.univ.sup C.termWidth

theorem termWidth_le_width (C : DNFFormulaCertificate n s f) (a : Fin s) :
    C.termWidth a ≤ C.width :=
  Finset.le_sup (f := C.termWidth) (Finset.mem_univ a)

theorem termWidth_le_variables (C : DNFFormulaCertificate n s f) (a : Fin s) :
    C.termWidth a ≤ n := by
  unfold termWidth
  calc
    ((C.term a).positive ∪ (C.term a).negative).card ≤
        (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-- Oriented inclusion-exclusion cost, choosing the cheaper sign per term. -/
def literalCost (C : DNFFormulaCertificate n s f) : ℕ :=
  ∑ a, min (2 ^ (C.term a).positive.card) (2 ^ (C.term a).negative.card)

/-- Sparse-volume cost on the used-variable cube. -/
def volumeCost (C : DNFFormulaCertificate n s f) : ℕ :=
  2 * ∑ a, 2 ^ (n - C.termWidth a)

/-- Width-degree affine-free support cost. -/
def degreeCost (C : DNFFormulaCertificate n s f) : ℕ :=
  1 + ∑ r ∈ Finset.Icc 2 (min C.width n), n.choose r

/-- All four theorem-73 costs in their displayed order. -/
def hybridCost (C : DNFFormulaCertificate n s f) : ℕ :=
  min C.volumeCost (min C.literalCost (min (2 ^ n - 1) C.degreeCost))

theorem score_eq_neg_half_of_false (C : DNFFormulaCertificate n s f)
    {bits : Fin n → Bool} (hbits : f bits = false) :
    (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits = -1 / 2 := by
  have hzero : ∀ a, (C.term a).eval bits = 0 := by
    intro a
    rcases (C.term a).eval_eq_zero_or_one bits with h | h
    · exact h
    · exfalso
      have hex : ∃ a, (C.term a).eval bits = 1 := ⟨a, h⟩
      have := (C.represents bits).mpr hex
      simp [hbits] at this
  simp [hzero]

theorem score_ge_half_of_true (C : DNFFormulaCertificate n s f)
    {bits : Fin n → Bool} (hbits : f bits = true) :
    (1 / 2 : ℝ) ≤ (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits := by
  obtain ⟨a, ha⟩ := (C.represents bits).mp hbits
  have hsum : (1 : ℝ) ≤ ∑ j, (C.term j).eval bits := by
    calc
      (1 : ℝ) = (C.term a).eval bits := ha.symm
      _ ≤ ∑ j ∈ Finset.univ, (C.term j).eval bits :=
        Finset.single_le_sum (fun j _ ↦ (C.term j).eval_nonneg bits)
          (Finset.mem_univ a)
      _ = ∑ j, (C.term j).eval bits := by simp
  linarith

theorem strictSignRepresents (C : DNFFormulaCertificate n s f) :
    StrictSignRepresentsScore
      (fun bits ↦ (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits) f := by
  intro bits
  cases hbit : f bits with
  | false =>
      change ((0 < (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits ↔
        false = true) ∧
        (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits ≠ 0)
      rw [C.score_eq_neg_half_of_false hbit]
      norm_num
  | true =>
      have hge := C.score_ge_half_of_true hbit
      change ((0 < (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits ↔
        true = true) ∧
        (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits ≠ 0)
      simp only [iff_true]
      constructor <;> linarith

/-- The ordinary polynomial threshold attached to the DNF. -/
noncomputable def polynomial (C : DNFFormulaCertificate n s f) :
    MvPolynomial (Fin n) ℝ :=
  (∑ a, (C.term a).polynomial) - MvPolynomial.C (1 / 2)

@[simp] theorem polynomial_eval (C : DNFFormulaCertificate n s f)
    (bits : Fin n → Bool) :
    MvPolynomial.eval (cubePoint bits) C.polynomial =
      (-1 / 2 : ℝ) + ∑ a, (C.term a).eval bits := by
  simp [polynomial]
  ring

theorem polynomial_totalDegree_le (C : DNFFormulaCertificate n s f) :
    C.polynomial.totalDegree ≤ min C.width n := by
  unfold polynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    exact (C.term a).polynomial_totalDegree_le.trans
      (le_min (C.termWidth_le_width a) (C.termWidth_le_variables a))
  · simp

/-- The DNF width gives a threshold-degree certificate on its exact
used-variable cube. -/
theorem thresholdDegLE (C : DNFFormulaCertificate n s f) :
    ThresholdDegLE f (min C.width n) := by
  refine ⟨C.polynomial, C.polynomial_totalDegree_le, ?_⟩
  intro bits
  rw [C.polynomial_eval]
  exact (C.strictSignRepresents bits).1

/-- Width-degree affine-free sparsity bound. -/
theorem HStar_le_degreeCost (C : DNFFormulaCertificate n s f) :
    HStar n f ≤ C.degreeCost :=
  HStar_le_one_add_sum_choose_of_ThresholdDegLE C.thresholdDegLE

/-- The literal-expansion certificate, reusing the generic cylinder compiler. -/
noncomputable def cylinderCertificate (C : DNFFormulaCertificate n s f) :
    CylinderThresholdCertificate n f where
  bias := -1 / 2
  termCount := s
  cylinder := C.term
  coefficient := fun _ ↦ 1
  coefficient_ne_zero := fun _ ↦ one_ne_zero
  represents := by simpa using C.strictSignRepresents

theorem cylinderCertificate_cost (C : DNFFormulaCertificate n s f) :
    C.cylinderCertificate.cost = C.literalCost := by
  unfold cylinderCertificate CylinderThresholdCertificate.cost literalCost
  apply Finset.sum_congr rfl
  intro a _
  have hvac : ¬ ((C.term a).positive = ∅ ∧ (C.term a).negative = ∅) := by
    rintro ⟨hp, hn⟩
    have := C.term_nonempty a
    simp [hp, hn] at this
  simp [CubeCylinder.cost, hvac]

/-- Local oriented expansion bound. -/
theorem HStar_le_literalCost (C : DNFFormulaCertificate n s f) :
    HStar n f ≤ C.literalCost := by
  rw [← C.cylinderCertificate_cost]
  exact C.cylinderCertificate.HStar_le

/-- Generic junta interpolation bound on the exact used-variable cube. -/
theorem HStar_le_juntaCost (_C : DNFFormulaCertificate n s f) :
    HStar n f ≤ 2 ^ n - 1 :=
  HStar_le_universal_boolean f

theorem trueSupport_subset_termSupports (C : DNFFormulaCertificate n s f) :
    trueSupport f ⊆ Finset.univ.biUnion fun a ↦ (C.term a).support := by
  intro bits hbits
  have hf : f bits = true := by simpa [trueSupport] using hbits
  obtain ⟨a, ha⟩ := (C.represents bits).mp hf
  rw [Finset.mem_biUnion]
  exact ⟨a, Finset.mem_univ a, by simp [CubeCylinder.support, ha]⟩

theorem trueSupport_card_le_volumeSum (C : DNFFormulaCertificate n s f) :
    (trueSupport f).card ≤ ∑ a, 2 ^ (n - C.termWidth a) := by
  calc
    (trueSupport f).card ≤
        (Finset.univ.biUnion fun a ↦ (C.term a).support).card :=
      Finset.card_le_card C.trueSupport_subset_termSupports
    _ ≤ ∑ a ∈ Finset.univ, (C.term a).support.card :=
      Finset.card_biUnion_le
    _ = ∑ a, 2 ^ (n - C.termWidth a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (C.term a).support_card

/-- Sparse-volume bound for a nonconstant DNF. -/
theorem HStar_le_volumeCost (C : DNFFormulaCertificate n s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.volumeCost := by
  calc
    HStar n f ≤ 2 * (trueSupport f).card :=
      HStar_le_two_mul_trueSupport f
        (falseSupport_nonempty_of_nonconstant f hnonconstant)
    _ ≤ 2 * ∑ a, 2 ^ (n - C.termWidth a) :=
      Nat.mul_le_mul_left 2 C.trueSupport_card_le_volumeSum
    _ = C.volumeCost := rfl

/-- The four simultaneous DNF bounds from theorem 73. -/
theorem HStar_le_four_costs (C : DNFFormulaCertificate n s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.volumeCost ∧
      HStar n f ≤ C.literalCost ∧
      HStar n f ≤ 2 ^ n - 1 ∧
      HStar n f ≤ C.degreeCost :=
  ⟨C.HStar_le_volumeCost hnonconstant, C.HStar_le_literalCost,
    C.HStar_le_juntaCost, C.HStar_le_degreeCost⟩

/-- Minimum form of the DNF hybrid theorem. -/
theorem HStar_le_hybridCost (C : DNFFormulaCertificate n s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.hybridCost := by
  obtain ⟨hvol, hlit, hjunta, hdeg⟩ := C.HStar_le_four_costs hnonconstant
  exact le_min hvol (le_min hlit (le_min hjunta hdeg))

end DNFFormulaCertificate

/-! ## CNF duality -/

/-- Swap the positive and negative fixed coordinates.  For a CNF clause this
is exactly the cylinder on which the clause is false. -/
def CubeCylinder.swap (C : CubeCylinder n) : CubeCylinder n where
  positive := C.negative
  negative := C.positive
  disjoint := C.disjoint.symm

@[simp] theorem CubeCylinder.swap_positive (C : CubeCylinder n) :
    C.swap.positive = C.negative := rfl

@[simp] theorem CubeCylinder.swap_negative (C : CubeCylinder n) :
    C.swap.negative = C.positive := rfl

/-- A CNF on exactly `n` used variables.  `clause.positive` indexes positive
literals, `clause.negative` indexes negative literals, and `clause.swap` is
the falsifying cylinder. -/
structure CNFFormulaCertificate (n s : ℕ)
    (f : (Fin n → Bool) → Bool) where
  clause : Fin s → CubeCylinder n
  clause_nonempty :
    ∀ a, ((clause a).positive ∪ (clause a).negative).Nonempty
  uses_every_variable :
    (Finset.univ.biUnion fun a ↦ (clause a).positive ∪ (clause a).negative) =
      Finset.univ
  represents : ∀ bits, f bits = false ↔ ∃ a, (clause a).swap.eval bits = 1

namespace CNFFormulaCertificate

/-- The false inputs of a CNF form a DNF in the falsifying cylinders. -/
def complementDNF (C : CNFFormulaCertificate n s f) :
    DNFFormulaCertificate n s (fun bits ↦ !(f bits)) where
  term := fun a ↦ (C.clause a).swap
  term_nonempty := by
    intro a
    simpa [CubeCylinder.swap, Finset.union_comm] using C.clause_nonempty a
  uses_every_variable := by
    simpa [CubeCylinder.swap, Finset.union_comm] using C.uses_every_variable
  represents := by
    intro bits
    cases hbit : f bits <;> simpa [hbit] using C.represents bits

/-- Width of one CNF clause. -/
def clauseWidth (C : CNFFormulaCertificate n s f) (a : Fin s) : ℕ :=
  ((C.clause a).positive ∪ (C.clause a).negative).card

/-- Maximum CNF width. -/
def width (C : CNFFormulaCertificate n s f) : ℕ :=
  Finset.univ.sup C.clauseWidth

/-- Sparse false-volume cost. -/
def volumeCost (C : CNFFormulaCertificate n s f) : ℕ :=
  2 * ∑ a, 2 ^ (n - C.clauseWidth a)

/-- Oriented literal-expansion cost. -/
def literalCost (C : CNFFormulaCertificate n s f) : ℕ :=
  ∑ a, min (2 ^ (C.clause a).positive.card)
    (2 ^ (C.clause a).negative.card)

/-- Width-degree affine-free support cost. -/
def degreeCost (C : CNFFormulaCertificate n s f) : ℕ :=
  1 + ∑ r ∈ Finset.Icc 2 (min C.width n), n.choose r

/-- All four dual costs in theorem 73. -/
def hybridCost (C : CNFFormulaCertificate n s f) : ℕ :=
  min C.volumeCost (min C.literalCost (min (2 ^ n - 1) C.degreeCost))

@[simp] theorem complementDNF_termWidth
    (C : CNFFormulaCertificate n s f) (a : Fin s) :
    C.complementDNF.termWidth a = C.clauseWidth a := by
  simp [complementDNF, DNFFormulaCertificate.termWidth, clauseWidth,
    CubeCylinder.swap, Finset.union_comm]

@[simp] theorem complementDNF_width (C : CNFFormulaCertificate n s f) :
    C.complementDNF.width = C.width := by
  unfold DNFFormulaCertificate.width width
  apply Finset.sup_congr rfl
  intro a _
  exact C.complementDNF_termWidth a

@[simp] theorem complementDNF_volumeCost (C : CNFFormulaCertificate n s f) :
    C.complementDNF.volumeCost = C.volumeCost := by
  simp [DNFFormulaCertificate.volumeCost, volumeCost]

@[simp] theorem complementDNF_literalCost (C : CNFFormulaCertificate n s f) :
    C.complementDNF.literalCost = C.literalCost := by
  unfold DNFFormulaCertificate.literalCost literalCost
  apply Finset.sum_congr rfl
  intro a _
  simp [complementDNF, CubeCylinder.swap, Nat.min_comm]

@[simp] theorem complementDNF_degreeCost (C : CNFFormulaCertificate n s f) :
    C.complementDNF.degreeCost = C.degreeCost := by
  simp [DNFFormulaCertificate.degreeCost, degreeCost]

theorem complement_nonconstant (_C : CNFFormulaCertificate n s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    ¬ ∀ x y, Bool.not (f x) = Bool.not (f y) := by
  intro h
  apply hnonconstant
  intro x y
  exact Bool.not_inj (h x y)

/-- The four simultaneous CNF bounds, obtained from the exact DNF of false
inputs and output-complement invariance. -/
theorem HStar_le_four_costs (C : CNFFormulaCertificate n s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.volumeCost ∧
      HStar n f ≤ C.literalCost ∧
      HStar n f ≤ 2 ^ n - 1 ∧
      HStar n f ≤ C.degreeCost := by
  have h := C.complementDNF.HStar_le_four_costs
    (C.complement_nonconstant hnonconstant)
  rw [HStar_complement f] at h
  simpa using h

/-- Minimum form of the CNF hybrid theorem. -/
theorem HStar_le_hybridCost (C : CNFFormulaCertificate n s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.hybridCost := by
  obtain ⟨hvol, hlit, hjunta, hdeg⟩ := C.HStar_le_four_costs hnonconstant
  exact le_min hvol (le_min hlit (le_min hjunta hdeg))

end CNFFormulaCertificate

/-! ## Used-variable transport -/

/-- An ambient Boolean function displayed as a DNF on exactly `v` used
coordinates. -/
structure DNFJuntaCertificate (n v s : ℕ)
    (f : (Fin n → Bool) → Bool) where
  embedding : Fin v ↪ Fin n
  core : (Fin v → Bool) → Bool
  formula : DNFFormulaCertificate v s core
  factors : IsJuntaVia embedding core f

namespace DNFJuntaCertificate

theorem HStar_eq_core (C : DNFJuntaCertificate n v s f) :
    HStar n f = HStar v C.core :=
  C.factors.HStar_eq

theorem core_nonconstant (C : DNFJuntaCertificate n v s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    ¬ ∀ x y, C.core x = C.core y := by
  intro hcore
  apply hnonconstant
  intro x y
  rw [C.factors x, C.factors y]
  exact hcore _ _

/-- **Theorem 73, DNF form.**  All four bounds hold after exact junta
transport from the `v` used variables. -/
theorem HStar_le_four_costs (C : DNFJuntaCertificate n v s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.formula.volumeCost ∧
      HStar n f ≤ C.formula.literalCost ∧
      HStar n f ≤ 2 ^ v - 1 ∧
      HStar n f ≤ C.formula.degreeCost := by
  rw [C.HStar_eq_core]
  exact C.formula.HStar_le_four_costs (C.core_nonconstant hnonconstant)

/-- Minimum form of theorem 73 for an ambient DNF junta. -/
theorem HStar_le_hybridCost (C : DNFJuntaCertificate n v s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.formula.hybridCost := by
  rw [C.HStar_eq_core]
  exact C.formula.HStar_le_hybridCost (C.core_nonconstant hnonconstant)

end DNFJuntaCertificate

/-- An ambient Boolean function displayed as a CNF on exactly `v` used
coordinates. -/
structure CNFJuntaCertificate (n v s : ℕ)
    (f : (Fin n → Bool) → Bool) where
  embedding : Fin v ↪ Fin n
  core : (Fin v → Bool) → Bool
  formula : CNFFormulaCertificate v s core
  factors : IsJuntaVia embedding core f

namespace CNFJuntaCertificate

theorem HStar_eq_core (C : CNFJuntaCertificate n v s f) :
    HStar n f = HStar v C.core :=
  C.factors.HStar_eq

theorem core_nonconstant (C : CNFJuntaCertificate n v s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    ¬ ∀ x y, C.core x = C.core y := by
  intro hcore
  apply hnonconstant
  intro x y
  rw [C.factors x, C.factors y]
  exact hcore _ _

/-- **Theorem 73, CNF form.**  All four dual bounds hold after exact junta
transport from the `v` used variables. -/
theorem HStar_le_four_costs (C : CNFJuntaCertificate n v s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.formula.volumeCost ∧
      HStar n f ≤ C.formula.literalCost ∧
      HStar n f ≤ 2 ^ v - 1 ∧
      HStar n f ≤ C.formula.degreeCost := by
  rw [C.HStar_eq_core]
  exact C.formula.HStar_le_four_costs (C.core_nonconstant hnonconstant)

/-- Minimum form of theorem 73 for an ambient CNF junta. -/
theorem HStar_le_hybridCost (C : CNFJuntaCertificate n v s f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    HStar n f ≤ C.formula.hybridCost := by
  rw [C.HStar_eq_core]
  exact C.formula.HStar_le_hybridCost (C.core_nonconstant hnonconstant)

end CNFJuntaCertificate

/-- Constant branch of theorem 73. -/
theorem HStar_eq_zero_of_constant (f : (Fin n → Bool) → Bool)
    (hconstant : ∀ x y, f x = f y) : HStar n f = 0 :=
  (HStar_eq_zero_iff f).2 hconstant

end HeadComplexity
