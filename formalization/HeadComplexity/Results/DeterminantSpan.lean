import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Universal cleared-span certificates

This is the machine-checkable algebraic schema behind determinant upper-bound
certificates.  A certificate supplies positive affine denominators and states
that their cleared tangent features span every real function on the Boolean
cube.  The conclusion compiles the supplied coordinates into one fractional
atom per denominator.

Finite determinant computations, such as the numerical certificates for
dimensions three through twelve, can target this structure without repeating
the analytic argument.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- Positive affine denominators whose cleared affine-numerator features span
all real-valued functions on the Boolean cube. -/
structure ClearedSpanCertificate (n H : ℕ) where
  denConst : Fin H → ℝ
  denCoeff : Fin H → Fin n → ℝ
  denConst_pos : ∀ h, 0 < denConst h
  denCoeff_pos : ∀ h i, 0 < denCoeff h i
  spans : ∀ target : (Fin n → Bool) → ℝ,
    ∃ (bias : ℝ) (numConst : Fin H → ℝ)
      (numCoeff : Fin H → Fin n → ℝ),
      ∀ bits,
        target bits =
          bias * ∏ h, affineValue (denConst h) (denCoeff h) bits +
            ∑ h, affineValue (numConst h) (numCoeff h) bits *
              ∏ g ∈ Finset.univ.erase h,
                affineValue (denConst g) (denCoeff g) bits

namespace ClearedSpanCertificate

/-- The target sign vector associated with a Boolean function. -/
noncomputable def signTarget (f : (Fin n → Bool) → Bool)
    (bits : Fin n → Bool) : ℝ :=
  if f bits then 1 else -1

/-- A cleared-span certificate computes every Boolean function with its fixed
number of heads. -/
theorem computable (C : ClearedSpanCertificate n H)
    (f : (Fin n → Bool) → Bool) : computableWithHeadsN n H f := by
  classical
  obtain ⟨bias, numConst, numCoeff, hspan⟩ := C.spans (signTarget f)
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
  have hscore : bias + ∑ h, N h / D h =
      signTarget f bits / ∏ h, D h := by
    apply (eq_div_iff hQpos.ne').2
    rw [hclear]
    symm
    simpa [D, N] using hspan bits
  simp_rw [show ∀ h, (phi h).eval bits = N h / D h by
    intro h
    exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ bits]
  rw [hscore, div_pos_iff_of_pos_right hQpos]
  cases h : f bits <;> simp [signTarget, h]

/-- **Determinant-span upper-bound schema.** Every Boolean function is bounded
by the head count of a universal cleared-span certificate. -/
theorem HStar_le (C : ClearedSpanCertificate n H)
    (f : (Fin n → Bool) → Bool) : HStar n f ≤ H :=
  HStar_le_of_computableWithHeadsN (C.computable f)

end ClearedSpanCertificate

end HeadComplexity
