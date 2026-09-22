import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Results.DeterminantSpan
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.style.header false

/-!
# Degree-restricted cleared-span certificates

This is the degree-restricted form of the determinant-span method.  A fixed
family of positive affine denominators need only span the squarefree
polynomial functions of degree at most `d`.  It then computes every Boolean
function of threshold degree at most `d`.

The same certificate also carries the sharp parameter-count obstruction.  A
constant numerator at head `h` is redundant because `B_h / B_h = 1`, so the
cleared score space has dimension at most `1 + n * H`, rather than the raw
feature count `1 + (n + 1) * H`.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H d : ℕ}

/-- Squarefree monomials of degree at most `d`. -/
abbrev LowDegreeMonomialIndex (n d : ℕ) :=
  { S : Finset (Fin n) // S.card ≤ d }

/-- The dimension of the multilinear degree-at-most-`d` function space on
the `n`-cube. -/
def thresholdDegreeDimension (n d : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (d + 1), n.choose r

/-- The low-degree monomial index has the expected binomial-sum cardinality. -/
theorem card_lowDegreeMonomialIndex (n d : ℕ) :
    Fintype.card (LowDegreeMonomialIndex n d) =
      thresholdDegreeDimension n d := by
  classical
  rw [Fintype.card_subtype]
  unfold thresholdDegreeDimension
  calc
    ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun S ↦ S.card ≤ d)).card =
        ((Finset.univ : Finset (Finset (Fin n))).filter
          (fun S ↦ S.card ∈ Finset.range (d + 1))).card := by
            congr 1
            ext S
            simp
    _ = ∑ r ∈ Finset.range (d + 1),
          ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun S ↦ S.card = r)).card := by
          symm
          exact Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Finset (Fin n)))
            (Finset.range (d + 1)) Finset.card
    _ = ∑ r ∈ Finset.range (d + 1), n.choose r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [show
            (Finset.univ : Finset (Finset (Fin n))).filter
                (fun S ↦ S.card = r) =
              (Finset.univ : Finset (Fin n)).powersetCard r by
            ext S
            simp]
          simp

/-- Boolean assignment with ones exactly on `S`. -/
def finsetBits (S : Finset (Fin n)) (i : Fin n) : Bool :=
  decide (i ∈ S)

@[simp] theorem squarefreeMonomial_finsetBits
    (S T : Finset (Fin n)) :
    squarefreeMonomial S (finsetBits T) = if S ⊆ T then 1 else 0 := by
  classical
  by_cases hST : S ⊆ T
  · rw [if_pos hST]
    unfold squarefreeMonomial
    apply Finset.prod_eq_one
    intro i hi
    simp [finsetBits, hST hi, boolToReal]
  · rw [if_neg hST]
    obtain ⟨i, hiS, hiT⟩ : ∃ i ∈ S, i ∉ T := by
      simpa [Finset.subset_iff] using hST
    unfold squarefreeMonomial
    apply Finset.prod_eq_zero hiS
    simp [finsetBits, hiT, boolToReal]

/-- Distinct low-degree squarefree monomials are linearly independent as
functions on the Boolean cube. -/
theorem linearIndependent_lowDegreeMonomials (n d : ℕ) :
    LinearIndependent ℝ
      (fun S : LowDegreeMonomialIndex n d ↦
        squarefreeMonomial S.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficient hsum
  have hzero : ∀ k : ℕ, ∀ S : LowDegreeMonomialIndex n d,
      S.1.card = k → coefficient S = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro S hSk
        have heval := congrFun hsum (finsetBits S.1)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at heval
        have hsingle :
            (∑ T : LowDegreeMonomialIndex n d,
                coefficient T * squarefreeMonomial T.1 (finsetBits S.1)) =
              coefficient S := by
          rw [Finset.sum_eq_single S]
          · simp
          · intro T hT hTS
            rw [squarefreeMonomial_finsetBits]
            by_cases hsub : T.1 ⊆ S.1
            · rw [if_pos hsub, ih T.1.card]
              · simp
              · have hne : T.1 ≠ S.1 := fun heq ↦ hTS (Subtype.ext heq)
                have hcard : T.1.card < S.1.card :=
                  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
                    ⟨hsub, hne⟩)
                simpa [hSk] using hcard
              · rfl
            · simp [hsub]
          · intro hS
            simp at hS
        rw [hsingle] at heval
        exact heval
  exact fun S ↦ hzero S.1.card S rfl

/-- Nonredundant cleared features: one global product and one raw-coordinate
numerator for each head and coordinate. -/
abbrev ReducedClearedFeatureIndex (n H : ℕ) :=
  Option (Fin H × Fin n)

/-- Evaluation of a nonredundant cleared feature. -/
noncomputable def reducedClearedFeatureValue
    (denConst : Fin H → ℝ) (denCoeff : Fin H → Fin n → ℝ)
    (feature : ReducedClearedFeatureIndex n H)
    (bits : Fin n → Bool) : ℝ :=
  match feature with
  | none => ∏ h, affineValue (denConst h) (denCoeff h) bits
  | some (h, i) =>
      boolToReal (bits i) *
        ∏ g ∈ Finset.univ.erase h,
          affineValue (denConst g) (denCoeff g) bits

/-- Expansion of a sum over the nonredundant cleared-feature family. -/
theorem sum_reducedClearedFeatureValue
    (denConst : Fin H → ℝ) (denCoeff : Fin H → Fin n → ℝ)
    (coefficient : ReducedClearedFeatureIndex n H → ℝ)
    (bits : Fin n → Bool) :
    (∑ feature, coefficient feature *
        reducedClearedFeatureValue denConst denCoeff feature bits) =
      coefficient none *
          ∏ h, affineValue (denConst h) (denCoeff h) bits +
        ∑ h, (∑ i, coefficient (some (h, i)) * boolToReal (bits i)) *
          ∏ g ∈ Finset.univ.erase h,
            affineValue (denConst g) (denCoeff g) bits := by
  classical
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [reducedClearedFeatureValue, Finset.sum_mul, mul_assoc]

/-- Positive affine denominators whose cleared affine-numerator features span
all squarefree polynomial functions of degree at most `d` on the Boolean
cube. -/
structure DegreeClearedSpanCertificate (n H d : ℕ) where
  denConst : Fin H → ℝ
  denCoeff : Fin H → Fin n → ℝ
  denConst_pos : ∀ h, 0 < denConst h
  denCoeff_pos : ∀ h i, 0 < denCoeff h i
  spans : ∀ P : SquarefreePolynomial n, P.DegreeLE d →
    ∃ (bias : ℝ) (numConst : Fin H → ℝ)
      (numCoeff : Fin H → Fin n → ℝ),
      ∀ bits,
        P.eval bits =
          bias * ∏ h, affineValue (denConst h) (denCoeff h) bits +
            ∑ h, affineValue (numConst h) (numCoeff h) bits *
              ∏ g ∈ Finset.univ.erase h,
                affineValue (denConst g) (denCoeff g) bits

namespace DegreeClearedSpanCertificate

/-- A universal cleared-span certificate restricts to every degree bound. -/
noncomputable def ofClearedSpanCertificate
    (C : ClearedSpanCertificate n H) :
    DegreeClearedSpanCertificate n H d where
  denConst := C.denConst
  denCoeff := C.denCoeff
  denConst_pos := C.denConst_pos
  denCoeff_pos := C.denCoeff_pos
  spans := fun P _ ↦ C.spans P.eval

/-- The redundant constant numerator of every head can be absorbed into the
global bias and its raw-coordinate numerators. -/
theorem spans_reduced (C : DegreeClearedSpanCertificate n H d)
    (P : SquarefreePolynomial n) (hPdeg : P.DegreeLE d) :
    ∃ coefficient : ReducedClearedFeatureIndex n H → ℝ,
      ∀ bits,
        P.eval bits = ∑ feature, coefficient feature *
          reducedClearedFeatureValue C.denConst C.denCoeff feature bits := by
  classical
  obtain ⟨bias, numConst, numCoeff, hspan⟩ := C.spans P hPdeg
  let coefficient : ReducedClearedFeatureIndex n H → ℝ
    | none => bias + ∑ h, numConst h / C.denConst h
    | some (h, i) =>
        numCoeff h i - (numConst h / C.denConst h) * C.denCoeff h i
  refine ⟨coefficient, fun bits ↦ ?_⟩
  let D : Fin H → ℝ := fun h ↦
    affineValue (C.denConst h) (C.denCoeff h) bits
  let Q : ℝ := ∏ h, D h
  let Qh : Fin H → ℝ := fun h ↦
    ∏ g ∈ Finset.univ.erase h, D g
  let denLinear : Fin H → ℝ := fun h ↦
    ∑ i, C.denCoeff h i * boolToReal (bits i)
  let numLinear : Fin H → ℝ := fun h ↦
    ∑ i, numCoeff h i * boolToReal (bits i)
  have hfactor : ∀ h, Q = D h * Qh h := fun h ↦ by
    exact (Finset.mul_prod_erase Finset.univ D (Finset.mem_univ h)).symm
  have hden : ∀ h, D h = C.denConst h + denLinear h := fun h ↦ by
    rfl
  have hnum : ∀ h,
      affineValue (numConst h) (numCoeff h) bits =
        numConst h + numLinear h := fun h ↦ by
    rfl
  have hlinear : ∀ h,
      (∑ i, (numCoeff h i -
          (numConst h / C.denConst h) * C.denCoeff h i) *
            boolToReal (bits i)) =
        numLinear h - (numConst h / C.denConst h) * denLinear h := by
    intro h
    dsimp [numLinear, denLinear]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hhead : ∀ h,
      (numConst h / C.denConst h) * Q +
          (numLinear h - (numConst h / C.denConst h) * denLinear h) * Qh h =
        affineValue (numConst h) (numCoeff h) bits * Qh h := by
    intro h
    rw [hfactor h, hden h, hnum h]
    field_simp [(C.denConst_pos h).ne']
    ring
  rw [hspan bits, sum_reducedClearedFeatureValue]
  change
    bias * Q + ∑ h, affineValue (numConst h) (numCoeff h) bits * Qh h =
      (bias + ∑ h, numConst h / C.denConst h) * Q +
        ∑ h,
          (∑ i, (numCoeff h i -
              (numConst h / C.denConst h) * C.denCoeff h i) *
                boolToReal (bits i)) * Qh h
  simp_rw [hlinear]
  rw [add_mul, Finset.sum_mul, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  exact (hhead h).symm

/-- Every low-degree monomial lies in the span of the certificate's
nonredundant cleared features. -/
private theorem monomial_mem_reduced_span
    (C : DegreeClearedSpanCertificate n H d)
    (S : LowDegreeMonomialIndex n d) :
    squarefreeMonomial S.1 ∈
      Submodule.span ℝ (Set.range fun feature : ReducedClearedFeatureIndex n H ↦
        reducedClearedFeatureValue C.denConst C.denCoeff feature) := by
  classical
  let P : SquarefreePolynomial n :=
    ⟨fun T ↦ if T = S.1 then 1 else 0⟩
  have hPdeg : P.DegreeLE d := by
    intro T hT
    by_cases hTS : T = S.1
    · simpa [hTS] using S.2
    · simp [P, hTS] at hT
  have hPeval : ∀ bits, P.eval bits = squarefreeMonomial S.1 bits := by
    intro bits
    rw [← SquarefreePolynomial.fullSum_eq_eval]
    simp [P]
  obtain ⟨coefficient, hcoefficient⟩ := C.spans_reduced P hPdeg
  have heq : squarefreeMonomial S.1 =
      ∑ feature, coefficient feature •
        reducedClearedFeatureValue C.denConst C.denCoeff feature := by
    funext bits
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hPeval bits, hcoefficient bits]
  rw [heq]
  exact Submodule.sum_mem _ fun feature _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span ⟨feature, rfl⟩)

/-- The degree-`d` fixed-denominator span method has at most `1 + n * H`
independent parameters. -/
theorem dimension_obstruction
    (C : DegreeClearedSpanCertificate n H d) :
    thresholdDegreeDimension n d ≤ 1 + n * H := by
  let lowFamily : LowDegreeMonomialIndex n d →
      ((Fin n → Bool) → ℝ) :=
    fun S ↦ squarefreeMonomial S.1
  let featureFamily : ReducedClearedFeatureIndex n H →
      ((Fin n → Bool) → ℝ) :=
    fun feature ↦
      reducedClearedFeatureValue C.denConst C.denCoeff feature
  have hspan :
      Submodule.span ℝ (Set.range lowFamily) ≤
        Submodule.span ℝ (Set.range featureFamily) := by
    apply Submodule.span_le.mpr
    rintro value ⟨S, rfl⟩
    exact C.monomial_mem_reduced_span S
  calc
    thresholdDegreeDimension n d =
        Fintype.card (LowDegreeMonomialIndex n d) :=
      (card_lowDegreeMonomialIndex n d).symm
    _ = Module.finrank ℝ
        (Submodule.span ℝ (Set.range lowFamily)) := by
      symm
      exact finrank_span_eq_card (linearIndependent_lowDegreeMonomials n d)
    _ ≤ Module.finrank ℝ
        (Submodule.span ℝ (Set.range featureFamily)) :=
      Submodule.finrank_mono hspan
    _ ≤ Fintype.card (ReducedClearedFeatureIndex n H) :=
      finrank_range_le_card featureFamily
    _ = 1 + n * H := by
      simp [ReducedClearedFeatureIndex, Nat.mul_comm, Nat.add_comm]

/-- A degree-restricted cleared-span certificate computes every Boolean
function whose threshold degree is at most the certified degree. -/
theorem computable_of_ThresholdDegLE
    (C : DegreeClearedSpanCertificate n H d)
    {f : (Fin n → Bool) → Bool} (hf : ThresholdDegLE f d) :
    computableWithHeadsN n H f := by
  classical
  obtain ⟨P, hPdeg, hPstrict⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE hf
  obtain ⟨bias, numConst, numCoeff, hspan⟩ := C.spans P hPdeg
  let phi : Fin H → FracAtom n := fun h ↦
    FracAtom.ofPositiveAffineRatio (numConst h) (numCoeff h)
      (C.denConst h) (C.denCoeff h)
      (C.denConst_pos h) (C.denCoeff_pos h)
  apply computable_of_fracComputable
  refine ⟨phi, bias, fun bits ↦ ?_⟩
  let D : Fin H → ℝ := fun h ↦
    affineValue (C.denConst h) (C.denCoeff h) bits
  let N : Fin H → ℝ := fun h ↦
    affineValue (numConst h) (numCoeff h) bits
  have hDpos : ∀ h, 0 < D h := fun h ↦
    affineValue_pos _ _ (C.denConst_pos h) (C.denCoeff_pos h) bits
  have hDne : ∀ h, D h ≠ 0 := fun h ↦ (hDpos h).ne'
  have hQpos : 0 < ∏ h, D h := Finset.prod_pos fun h _ ↦ hDpos h
  have hfactor : ∀ h, (∏ g, D g) = D h * ∏ g ∈ Finset.univ.erase h, D g :=
    fun h ↦ (Finset.mul_prod_erase Finset.univ D (Finset.mem_univ h)).symm
  have hclear :
      (bias + ∑ h, N h / D h) * ∏ h, D h =
        bias * ∏ h, D h +
          ∑ h, N h * ∏ g ∈ Finset.univ.erase h, D g := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    rw [hfactor h]
    field_simp [hDne h]
  have hscore : bias + ∑ h, N h / D h = P.eval bits / ∏ h, D h := by
    apply (eq_div_iff hQpos.ne').2
    rw [hclear]
    symm
    simpa [D, N] using hspan bits
  simp_rw [show ∀ h, (phi h).eval bits = N h / D h by
    intro h
    exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ bits]
  rw [hscore, div_pos_iff_of_pos_right hQpos]
  exact (hPstrict bits).1

/-- Degree-restricted determinant-span upper bound. -/
theorem HStar_le_of_ThresholdDegLE
    (C : DegreeClearedSpanCertificate n H d)
    {f : (Fin n → Bool) → Bool} (hf : ThresholdDegLE f d) :
    HStar n f ≤ H :=
  HStar_le_of_computableWithHeadsN (C.computable_of_ThresholdDegLE hf)

end DegreeClearedSpanCertificate

end HeadComplexity
