import HeadComplexity.Atoms.UniformApproximationSum
import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Fourier support-cost upper bounds

The affine part of a Walsh score is charged once.  Every remaining Walsh
character on a coordinate set `S` is charged `|S|` heads.  The proof retains
the Fourier structure instead of expanding characters into monomials.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ} {f : (Fin n → Bool) → Bool}

/-- A finite Walsh score, with its constant and singleton contribution
already collected into one affine function. -/
structure FourierSupportCertificate (n : ℕ)
    (f : (Fin n → Bool) → Bool) where
  affineUsed : Bool
  affineConst : ℝ
  affineCoeff : Fin n → ℝ
  affineCoeff_eq_zero : affineUsed = false → ∀ i, affineCoeff i = 0
  affineCoeff_ne_zero : affineUsed = true → ∃ i, affineCoeff i ≠ 0
  termCount : ℕ
  support : Fin termCount → Finset (Fin n)
  coefficient : Fin termCount → ℝ
  support_card_ge_two : ∀ j, 2 ≤ (support j).card
  support_injective : Function.Injective support
  coefficient_ne_zero : ∀ j, coefficient j ≠ 0
  represents : StrictSignRepresentsScore
    (fun bits ↦ affineValue affineConst affineCoeff bits +
      ∑ j, coefficient j * walshCharacter (support j) bits) f

namespace FourierSupportCertificate

/-- The theorem-45 support cost: one head for a nonconstant affine part, plus
the cardinality of every nonlinear Walsh support. -/
def cost (C : FourierSupportCertificate n f) : ℕ :=
  (if C.affineUsed then 1 else 0) + ∑ j, (C.support j).card

/-- Component labels used to flatten the affine block and all Walsh blocks. -/
abbrev Component (C : FourierSupportCertificate n f) : Type :=
  Fin (if C.affineUsed then 1 else 0) ⊕ Fin C.termCount

/-- Number of atoms belonging to one Fourier component. -/
abbrev atomCount (C : FourierSupportCertificate n f) (j : C.Component) : ℕ :=
  match j with
  | Sum.inl _ => 1
  | Sum.inr t => (C.support t).card

/-- Atom indices belonging to one Fourier component. -/
abbrev AtomIndex (C : FourierSupportCertificate n f) (j : C.Component) : Type :=
  Fin (C.atomCount j)

/-- The real score contributed by one Fourier component. -/
noncomputable def componentScore (C : FourierSupportCertificate n f) (j : C.Component)
    (bits : Fin n → Bool) : ℝ :=
  match j with
  | Sum.inl _ => affineValue 0 C.affineCoeff bits
  | Sum.inr t => C.coefficient t * walshCharacter (C.support t) bits

theorem card_sigma_atomIndex (C : FourierSupportCertificate n f) :
    Fintype.card (Sigma C.AtomIndex) = C.cost := by
  classical
  unfold cost
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  simp [AtomIndex, atomCount]

theorem affineConst_add_sum_componentScore
    (C : FourierSupportCertificate n f) (bits : Fin n → Bool) :
    C.affineConst + ∑ j, C.componentScore j bits =
      affineValue C.affineConst C.affineCoeff bits +
        ∑ j, C.coefficient j * walshCharacter (C.support j) bits := by
  classical
  have haffine :
      (∑ _a : Fin (if C.affineUsed then 1 else 0),
          affineValue 0 C.affineCoeff bits) =
        affineValue 0 C.affineCoeff bits := by
    cases hused : C.affineUsed
    · have hzero := C.affineCoeff_eq_zero hused
      simp [affineValue, hzero]
    · simp
  unfold componentScore
  rw [Fintype.sum_sum_type]
  simp only [haffine]
  unfold affineValue
  ring

theorem component_uniformlyAtomsApproximable
    (C : FourierSupportCertificate n f) :
    ∀ j, UniformlyAtomsApproximable (C.AtomIndex j) (C.componentScore j) := by
  intro j ε hε
  cases j with
  | inl a =>
      obtain ⟨φ, hφ⟩ := exists_fracAtom_approx_affineValue
        0 C.affineCoeff ε hε
      refine ⟨fun _ ↦ φ, 0, fun bits ↦ ?_⟩
      simpa [componentScore, atomCount] using hφ bits
  | inr t =>
      obtain ⟨φ, c, hφ⟩ := exists_walsh_atoms_uniform
        (C.support t) (C.coefficient t) ε hε
      exact ⟨φ, c, fun bits ↦ by simpa [componentScore, atomCount] using hφ bits⟩

/-- **Fourier support-cost upper bound.** -/
theorem computable (C : FourierSupportCertificate n f) :
    computableWithHeadsN n C.cost f := by
  have hstrict : StrictSignRepresentsScore
      (fun bits ↦ C.affineConst + ∑ j, C.componentScore j bits) f := by
    intro bits
    change ((0 < C.affineConst + ∑ j, C.componentScore j bits ↔
      f bits = true) ∧ C.affineConst + ∑ j, C.componentScore j bits ≠ 0)
    rw [C.affineConst_add_sum_componentScore bits]
    exact C.represents bits
  have h := computableWithHeadsCard_of_uniformlyAtomsApproximable
    C.componentScore C.component_uniformlyAtomsApproximable C.affineConst hstrict
  rwa [C.card_sigma_atomIndex] at h

/-- Minimum head complexity is bounded by the Fourier support cost. -/
theorem HStar_le (C : FourierSupportCertificate n f) : HStar n f ≤ C.cost :=
  HStar_le_of_computableWithHeadsN C.computable

/-- If all nonlinear active supports have size at most `d`, their total charge
is at most `d` times the number of such supports. -/
theorem cost_le_affine_add_mul (C : FourierSupportCertificate n f) {d : ℕ}
    (hdegree : ∀ j, (C.support j).card ≤ d) :
    C.cost ≤ (if C.affineUsed then 1 else 0) + d * C.termCount := by
  unfold cost
  apply Nat.add_le_add_left
  calc
    (∑ j, (C.support j).card) ≤ ∑ _j : Fin C.termCount, d :=
      Finset.sum_le_sum fun j _ ↦ hdegree j
    _ = d * C.termCount := by simp [Nat.mul_comm]

theorem HStar_le_affine_add_mul (C : FourierSupportCertificate n f) {d : ℕ}
    (hdegree : ∀ j, (C.support j).card ≤ d) :
    HStar n f ≤ (if C.affineUsed then 1 else 0) + d * C.termCount :=
  C.HStar_le.trans (C.cost_le_affine_add_mul hdegree)

/-- Sign-valued form of a Boolean predicate. -/
def signValue (f : (Fin n → Bool) → Bool) (bits : Fin n → Bool) : ℝ :=
  if f bits then 1 else -1

/-- Uniform error below one from the sign-valued truth table supplies the
strict sign condition required by a Fourier support certificate. -/
theorem strictSignRepresentsScore_of_uniform_lt_one
    (score : (Fin n → Bool) → ℝ)
    (hclose : ∀ bits, |signValue f bits - score bits| < 1) :
    StrictSignRepresentsScore score f := by
  intro bits
  cases hfb : f bits
  · have h := abs_lt.mp (hclose bits)
    simp [signValue, hfb] at h
    constructor
    · constructor
      · intro hpos
        linarith
      · intro htrue
        simp at htrue
    · linarith
  · have h := abs_lt.mp (hclose bits)
    simp [signValue, hfb] at h
    constructor
    · constructor
      · intro _
        simp
      · intro _
        linarith
    · linarith

/-- Fourier-tail form of the support-cost theorem. -/
theorem HStar_le_of_fourier_uniform_lt_one
    (affineUsed : Bool) (affineConst : ℝ) (affineCoeff : Fin n → ℝ)
    (haffine : affineUsed = false → ∀ i, affineCoeff i = 0)
    (haffine_active : affineUsed = true → ∃ i, affineCoeff i ≠ 0)
    (termCount : ℕ) (support : Fin termCount → Finset (Fin n))
    (coefficient : Fin termCount → ℝ)
    (hsupport : ∀ j, 2 ≤ (support j).card)
    (hsupport_injective : Function.Injective support)
    (hcoefficient : ∀ j, coefficient j ≠ 0)
    (hclose : ∀ bits,
      |signValue f bits -
        (affineValue affineConst affineCoeff bits +
          ∑ j, coefficient j * walshCharacter (support j) bits)| < 1) :
    HStar n f ≤
      (if affineUsed then 1 else 0) + ∑ j, (support j).card := by
  let C : FourierSupportCertificate n f :=
    { affineUsed := affineUsed
      affineConst := affineConst
      affineCoeff := affineCoeff
      affineCoeff_eq_zero := haffine
      affineCoeff_ne_zero := haffine_active
      termCount := termCount
      support := support
      coefficient := coefficient
      support_card_ge_two := hsupport
      support_injective := hsupport_injective
      coefficient_ne_zero := hcoefficient
      represents := strictSignRepresentsScore_of_uniform_lt_one
        (score := fun bits ↦ affineValue affineConst affineCoeff bits +
          ∑ j, coefficient j * walshCharacter (support j) bits) hclose }
  exact C.HStar_le

end FourierSupportCertificate

end HeadComplexity
