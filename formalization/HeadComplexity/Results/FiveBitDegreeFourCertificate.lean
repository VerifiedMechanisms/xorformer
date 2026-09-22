import HeadComplexity.Results.IntegralClearedCertificate
import HeadComplexity.Results.StructuralInvariances
import HeadComplexity.Results.ThresholdDegree

set_option linter.style.header false

/-!
# Lightweight certificates for five-bit degree-four exactness

This module contains only the symbolic certificate boundary.  It does not
embed or evaluate the large five-bit archives.  In particular, the final
theorem states exactly which reduction, family-shattering, and residual-orbit
coverage claims those archives must supply.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- Coefficients of one integral score in a fixed cleared-feature space. -/
structure IntegralClearedScoreRow (n H : ℕ) where
  coefficient : ClearedFeatureIndex n H → ℤ

namespace IntegralClearedScoreRow

/-- Exact evaluation of a coefficient row against fixed denominators. -/
def score (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (bits : Fin n → Bool) : ℤ :=
  ∑ feature, R.coefficient feature *
    clearedFeatureValue
      (fun h ↦ (denominator h).constant)
      (fun h i ↦ (denominator h).coefficient i) feature bits

/-- Add an integral multiple of a base row to a perturbation row. -/
def addScaled (perturbation base : IntegralClearedScoreRow n H)
    (scale : ℤ) : IntegralClearedScoreRow n H where
  coefficient := fun feature ↦
    perturbation.coefficient feature + scale * base.coefficient feature

@[simp] theorem score_addScaled
    (perturbation base : IntegralClearedScoreRow n H) (scale : ℤ)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (bits : Fin n → Bool) :
    (perturbation.addScaled base scale).score denominator bits =
      perturbation.score denominator bits + scale * base.score denominator bits := by
  unfold score addScaled
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro feature _
  ring

/-- The finite exact sign condition checked for one target. -/
def StrictlyRepresents (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ bits, (0 < R.score denominator bits ↔ f bits = true) ∧
    R.score denominator bits ≠ 0

instance (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (f : (Fin n → Bool) → Bool) :
    Decidable (R.StrictlyRepresents denominator f) := by
  unfold StrictlyRepresents
  infer_instance

/-- Boolean entry point for an individual archived score row. -/
def check (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (f : (Fin n → Bool) → Bool) : Bool :=
  decide (R.StrictlyRepresents denominator f)

theorem valid_of_check_eq_true (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (f : (Fin n → Bool) → Bool)
    (hcheck : R.check denominator f = true) :
    R.StrictlyRepresents denominator f :=
  of_decide_eq_true hcheck

/-- A checked row is the existing analytic integral certificate. -/
def toCertificate (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (f : (Fin n → Bool) → Bool)
    (hR : R.StrictlyRepresents denominator f) :
    IntegralClearedScoreCertificate n H f where
  denominator := denominator
  bias := R.coefficient none
  numConstant := fun h ↦ R.coefficient (some (h, none))
  numCoefficient := fun h i ↦ R.coefficient (some (h, some i))
  represents := by
    intro bits
    have hscore :
        integralClearedScore denominator (R.coefficient none)
            (fun h ↦ R.coefficient (some (h, none)))
            (fun h i ↦ R.coefficient (some (h, some i))) bits =
          R.score denominator bits := by
      rw [score, sum_clearedFeatureValue]
      rfl
    rw [hscore]
    exact hR bits

/-- A checked row gives the corresponding head upper bound. -/
theorem HStar_le (R : IntegralClearedScoreRow n H)
    (denominator : Fin H → IntegralOrientedDenominator n)
    (f : (Fin n → Bool) → Bool)
    (hR : R.StrictlyRepresents denominator f) : HStar n f ≤ H :=
  (R.toCertificate denominator f hR).HStar_le

end IntegralClearedScoreRow

/-- Finite gluing lemma behind the family-shattering argument.  A sufficiently
large positive integral multiple of a base score preserves all strict signs
off the zero set, while its vanishing leaves the perturbation signs unchanged
on the zero set. -/
theorem exists_integral_scale_strict_sign_glue
    {X : Type*} [Finite X]
    (zeroSet : X → Prop) (target : X → Bool)
    (base perturbation : X → ℤ)
    (hbaseZero : ∀ x, zeroSet x → base x = 0)
    (hbaseOff : ∀ x, ¬ zeroSet x →
      (0 < base x ↔ target x = true) ∧ base x ≠ 0)
    (hperturbation : ∀ x, zeroSet x →
      (0 < perturbation x ↔ target x = true) ∧ perturbation x ≠ 0) :
    ∃ scale : ℤ, 0 < scale ∧ ∀ x,
      (0 < perturbation x + scale * base x ↔ target x = true) ∧
        perturbation x + scale * base x ≠ 0 := by
  classical
  letI := Fintype.ofFinite X
  let scale : ℤ := ∑ x, |perturbation x| + 1
  have hsum_nonneg : 0 ≤ ∑ x, |perturbation x| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hscale : 0 < scale := by
    dsimp [scale]
    omega
  refine ⟨scale, hscale, fun x ↦ ?_⟩
  by_cases hx : zeroSet x
  · simpa [hbaseZero x hx] using hperturbation x hx
  · have hbase := hbaseOff x hx
    have hterm_le : |perturbation x| ≤ ∑ y, |perturbation y| :=
      Finset.single_le_sum (fun y _ ↦ abs_nonneg (perturbation y))
        (Finset.mem_univ x)
    have hperturbation_lt : |perturbation x| < scale := by
      dsimp [scale]
      omega
    have habs_pos : 0 < |base x| := abs_pos.mpr hbase.2
    have hone : (1 : ℤ) ≤ |base x| := by omega
    have hscale_le : scale ≤ scale * |base x| := by
      have h := mul_le_mul_of_nonneg_left hone (le_of_lt hscale)
      simpa using h
    have hdom : |perturbation x| < scale * |base x| :=
      hperturbation_lt.trans_le hscale_le
    rcases lt_or_gt_of_ne hbase.2 with hnegative | hpositive
    · rw [abs_of_neg hnegative] at hdom
      have htotal : perturbation x + scale * base x < 0 := by
        have hle := le_abs_self (perturbation x)
        nlinarith
      refine ⟨?_, ne_of_lt htotal⟩
      constructor
      · intro h
        exfalso
        linarith
      · intro h
        have := hbase.1.mpr h
        linarith
    · rw [abs_of_pos hpositive] at hdom
      have htotal : 0 < perturbation x + scale * base x := by
        have hle := neg_abs_le (perturbation x)
        nlinarith
      refine ⟨?_, ne_of_gt htotal⟩
      constructor
      · intro _
        exact hbase.1.mp hpositive
      · intro _
        exact htotal

/-- A fixed denominator tuple, a score vanishing on a zero set with the
forced signs off it, and perturbations realizing arbitrary signs on the zero
set.  Unlike an explicit family table, this is the reusable rank-and-margin
certificate used by the sixty non-residual normal orbits. -/
structure IntegralFamilyShatteringCertificate (n H : ℕ) where
  zeroSet : (Fin n → Bool) → Prop
  forced : (Fin n → Bool) → Bool
  denominator : Fin H → IntegralOrientedDenominator n
  base : IntegralClearedScoreRow n H
  base_zero : ∀ bits, zeroSet bits → base.score denominator bits = 0
  base_forced : ∀ bits, ¬ zeroSet bits →
    (0 < base.score denominator bits ↔ forced bits = true) ∧
      base.score denominator bits ≠ 0
  shatters : ∀ target : (Fin n → Bool) → Bool,
    ∃ perturbation : IntegralClearedScoreRow n H, ∀ bits,
      zeroSet bits →
        (0 < perturbation.score denominator bits ↔ target bits = true) ∧
          perturbation.score denominator bits ≠ 0

namespace IntegralFamilyShatteringCertificate

/-- The family covered by a shattering certificate consists of all extensions
of its forced signs away from the certified zero set. -/
def Covers (C : IntegralFamilyShatteringCertificate n H)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ bits, ¬ C.zeroSet bits → f bits = C.forced bits

/-- Rank-and-margin family shattering yields a head upper bound for every
extension, using only a finite integral scaling argument. -/
theorem HStar_le (C : IntegralFamilyShatteringCertificate n H)
    {f : (Fin n → Bool) → Bool} (hf : C.Covers f) :
    HStar n f ≤ H := by
  obtain ⟨perturbation, hperturbation⟩ := C.shatters f
  have hbaseOff : ∀ bits, ¬ C.zeroSet bits →
      (0 < C.base.score C.denominator bits ↔ f bits = true) ∧
        C.base.score C.denominator bits ≠ 0 := by
    intro bits hbits
    simpa [hf bits hbits] using C.base_forced bits hbits
  obtain ⟨scale, _, hglue⟩ := exists_integral_scale_strict_sign_glue
    C.zeroSet f
    (fun bits ↦ C.base.score C.denominator bits)
    (fun bits ↦ perturbation.score C.denominator bits)
    C.base_zero hbaseOff hperturbation
  apply (perturbation.addScaled C.base scale).HStar_le C.denominator f
  intro bits
  simpa using hglue bits

end IntegralFamilyShatteringCertificate

/-- A residual archive may select a different denominator tuple for each
target.  Keeping this separate from fixed-denominator shattering makes the
five exceptional orbit premises explicit. -/
structure IntegralResidualCoverageCertificate
    (family : Set ((Fin n → Bool) → Bool)) (H : ℕ) where
  denominator : ∀ f, f ∈ family → Fin H → IntegralOrientedDenominator n
  row : ∀ f, f ∈ family → IntegralClearedScoreRow n H
  valid : ∀ f hf, (row f hf).StrictlyRepresents (denominator f hf) f

namespace IntegralResidualCoverageCertificate

theorem HStar_le {family : Set ((Fin n → Bool) → Bool)}
    (C : IntegralResidualCoverageCertificate family H)
    {f : (Fin n → Bool) → Bool} (hf : f ∈ family) :
    HStar n f ≤ H :=
  (C.row f hf).HStar_le (C.denominator f hf) f (C.valid f hf)

end IntegralResidualCoverageCertificate

/-- Five-bit Boolean functions. -/
abbrev FiveBitFunction := (Fin 5 → Bool) → Bool

/-- The exact quotient symmetries used by the external orbit reduction. -/
structure FiveBitOrbitSymmetry where
  permutation : Equiv.Perm (Fin 5)
  flipInput : Bool
  complementOutput : Bool

namespace FiveBitOrbitSymmetry

/-- Apply coordinate permutation, optional simultaneous input complement, and
optional output complement. -/
def act (S : FiveBitOrbitSymmetry) (f : FiveBitFunction) : FiveBitFunction :=
  let inputAction := if S.flipInput then fun bits ↦ f (flipBits bits) else f
  let permuted := fun bits ↦ inputAction (permuteBits S.permutation bits)
  if S.complementOutput then fun bits ↦ !(permuted bits) else permuted

/-- All three quotient operations preserve head complexity. -/
theorem HStar_act (S : FiveBitOrbitSymmetry) (f : FiveBitFunction) :
    HStar 5 (S.act f) = HStar 5 f := by
  cases hinput : S.flipInput <;> cases houtput : S.complementOutput
  · simpa [act, hinput, houtput] using HStar_permute S.permutation f
  · simpa [act, hinput, houtput] using
      (HStar_complement
        (fun bits ↦ f (permuteBits S.permutation bits))).trans
          (HStar_permute S.permutation f)
  · simpa [act, hinput, houtput] using
      (HStar_permute S.permutation (fun bits ↦ f (flipBits bits))).trans
        (HStar_flip f)
  · simpa [act, hinput, houtput] using
      (HStar_complement
        (fun bits ↦ f (flipBits (permuteBits S.permutation bits)))).trans
          ((HStar_permute S.permutation
            (fun bits ↦ f (flipBits bits))).trans (HStar_flip f))

end FiveBitOrbitSymmetry

/-- Kernel-facing decomposition of the external five-bit computation.

The `reduction` field is the cocircuit/orbit classification.  The sixty
uniform families share one denominator tuple per family.  The remaining five
sets correspond exactly to residual orbit indices `8`, `44`, `62`, `63`, and
`64`; each has its own finite-coverage premise. -/
structure FiveBitDegreeFourCertificate where
  uniformShattering : Fin 60 → IntegralFamilyShatteringCertificate 5 4
  orbit8 : Set FiveBitFunction
  orbit44 : Set FiveBitFunction
  orbit62 : Set FiveBitFunction
  orbit63 : Set FiveBitFunction
  orbit64 : Set FiveBitFunction
  orbit8Coverage : IntegralResidualCoverageCertificate orbit8 4
  orbit44Coverage : IntegralResidualCoverageCertificate orbit44 4
  orbit62Coverage : IntegralResidualCoverageCertificate orbit62 4
  orbit63Coverage : IntegralResidualCoverageCertificate orbit63 4
  orbit64Coverage : IntegralResidualCoverageCertificate orbit64 4
  reduction : ∀ f : FiveBitFunction, thresholdDeg f = 4 →
    ∃ representative : FiveBitFunction, ∃ symmetry : FiveBitOrbitSymmetry,
      f = symmetry.act representative ∧
        ((∃ i, (uniformShattering i).Covers representative) ∨
          representative ∈ orbit8 ∨ representative ∈ orbit44 ∨
            representative ∈ orbit62 ∨ representative ∈ orbit63 ∨
              representative ∈ orbit64)

namespace FiveBitDegreeFourCertificate

/-- The archive boundary supplies the four-head upper bound for every
five-bit function of threshold degree four. -/
theorem HStar_le_four (C : FiveBitDegreeFourCertificate)
    (f : FiveBitFunction) (hdegree : thresholdDeg f = 4) :
    HStar 5 f ≤ 4 := by
  obtain ⟨representative, symmetry, rfl, hcase⟩ := C.reduction f hdegree
  rw [symmetry.HStar_act]
  rcases hcase with
    ⟨i, hi⟩ | h8 | h44 | h62 | h63 | h64
  · exact (C.uniformShattering i).HStar_le hi
  · exact C.orbit8Coverage.HStar_le h8
  · exact C.orbit44Coverage.HStar_le h44
  · exact C.orbit62Coverage.HStar_le h62
  · exact C.orbit63Coverage.HStar_le h63
  · exact C.orbit64Coverage.HStar_le h64

/-- **Conditional five-bit degree-four exactness.**  Once the six exact
archive premises above are imported, the headline theorem follows without
any further finite search or trusted computation. -/
theorem exact (C : FiveBitDegreeFourCertificate)
    (f : FiveBitFunction) (hdegree : thresholdDeg f = 4) :
    HStar 5 f = 4 := by
  apply le_antisymm (C.HStar_le_four f hdegree)
  rw [← hdegree]
  exact thresholdDeg_le_HStar f

end FiveBitDegreeFourCertificate

end HeadComplexity
