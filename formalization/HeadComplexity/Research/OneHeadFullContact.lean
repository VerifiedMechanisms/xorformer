import HeadComplexity.Research.PositiveReciprocalGradient

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.OneHeadFullContact
open scoped BigOperators

variable {ι κ : Type*} [Fintype κ]

def eval (A : ι → κ → ℝ) (θ : κ → ℝ) (x : ι) : ℝ :=
  ∑ j, A x j * θ j

def denominator (B : ι → κ → ℝ) (c : ι → ℝ) (θ : κ → ℝ) (x : ι) : ℝ :=
  c x + eval B θ x

def score (A B : ι → κ → ℝ) (c : ι → ℝ) (θ : κ → ℝ) (x : ι) : ℝ :=
  eval A θ x / denominator B c θ x

def contactMatrix (A B : ι → κ → ℝ) (f : ι → ℝ) (x : ι) (j : κ) : ℝ :=
  A x j - f x * B x j

/-- Clearing one affine denominator turns all prescribed-value equations into
one affine linear system in every numerator and denominator parameter. -/
theorem contact_iff (A B : ι → κ → ℝ) (c f : ι → ℝ) (θ : κ → ℝ)
    (hden : ∀ x, denominator B c θ x ≠ 0) :
    (∀ x, score A B c θ x = f x) ↔
      ∀ x, eval (contactMatrix A B f) θ x = f x * c x := by
  have hrow (x : ι) : eval (contactMatrix A B f) θ x =
      eval A θ x - f x * eval B θ x := by
    simp only [eval, contactMatrix, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, Finset.mul_sum]
  constructor
  · intro h x
    have hx := (div_eq_iff (hden x)).mp (h x)
    rw [hrow]
    unfold denominator at hx
    nlinarith
  · intro h x
    apply (div_eq_iff (hden x)).mpr
    have hx := h x
    rw [hrow] at hx
    unfold denominator
    nlinarith

/-- A full-rank contact system for one head has a unique solution, without a
restriction to a local neighborhood or a particular denominator component. -/
theorem unique_of_injective_contactMatrix
    (A B : ι → κ → ℝ) (c f : ι → ℝ)
    (hinj : Function.Injective (fun θ : κ → ℝ ↦ eval (contactMatrix A B f) θ))
    (θ ψ : κ → ℝ)
    (hθ : ∀ x, denominator B c θ x ≠ 0)
    (hψ : ∀ x, denominator B c ψ x ≠ 0)
    (hfθ : ∀ x, score A B c θ x = f x)
    (hfψ : ∀ x, score A B c ψ x = f x) : θ = ψ := by
  apply hinj
  funext x
  change eval (contactMatrix A B f) θ x = eval (contactMatrix A B f) ψ x
  rw [(contact_iff A B c f θ hθ).mp hfθ x,
    (contact_iff A B c f ψ hψ).mp hfψ x]

/-- The numerator in the usual quotient-rule differential. -/
def differential (A B : ι → κ → ℝ) (c : ι → ℝ)
    (θ v : κ → ℝ) (x : ι) : ℝ :=
  (eval A v x * denominator B c θ x - eval A θ x * eval B v x) /
    (denominator B c θ x)^2

/-- At prescribed contacts, the differential is exactly the cleared linear
contact map followed by invertible row scaling. -/
theorem differential_eq_contactMatrix
    (A B : ι → κ → ℝ) (c f : ι → ℝ) (θ v : κ → ℝ)
    (hden : ∀ x, denominator B c θ x ≠ 0)
    (hf : ∀ x, score A B c θ x = f x) (x : ι) :
    differential A B c θ v x =
      eval (contactMatrix A B f) v x / denominator B c θ x := by
  have hx := (div_eq_iff (hden x)).mp (hf x)
  have hr : eval (contactMatrix A B f) v x = eval A v x - f x * eval B v x := by
    simp only [eval, contactMatrix, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, Finset.mul_sum]
  rw [differential, hx, hr]
  field_simp [hden x]

/-- Nonsingularity of the full contact differential is enough for global
uniqueness, because the cleared one-head contact equations are linear. -/
theorem unique_of_injective_differential
    (A B : ι → κ → ℝ) (c f : ι → ℝ) (θ ψ : κ → ℝ)
    (hθ : ∀ x, denominator B c θ x ≠ 0)
    (hψ : ∀ x, denominator B c ψ x ≠ 0)
    (hfθ : ∀ x, score A B c θ x = f x)
    (hfψ : ∀ x, score A B c ψ x = f x)
    (hinj : Function.Injective (fun v : κ → ℝ ↦ differential A B c θ v)) :
    θ = ψ := by
  apply unique_of_injective_contactMatrix A B c f _ θ ψ hθ hψ hfθ hfψ
  intro v w hvw
  apply hinj
  funext x
  change differential A B c θ v x = differential A B c θ w x
  rw [differential_eq_contactMatrix A B c f θ v hθ hfθ,
    differential_eq_contactMatrix A B c f θ w hθ hfθ]
  exact congrArg (fun z : ℝ ↦ z / denominator B c θ x) (congrFun hvw x)

namespace Moebius

def transform (t s : ℝ) : ℝ := (s+t)/(1+t*s)

theorem unit_residual (t s f : ℝ) (hf : f^2 = 1) (hden : 1+t*s ≠ 0) :
    f * transform t s - 1 = (f*s-1)*(1-f*t)/(1+t*s) := by
  unfold transform
  have hd : 1+s*t ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hden, hd]
  nlinarith [congrArg (fun z : ℝ ↦ z*(s*t)) hf]

theorem fixes_unit (t f : ℝ) (hf : f^2 = 1) (hden : 1+t*f ≠ 0) :
    transform t f = f := by
  unfold transform
  apply (div_eq_iff hden).mpr
  nlinarith [congrArg (fun z : ℝ ↦ z*t) hf]

/-- Every signed unit inequality is preserved while the two elementary
Möbius factors remain positive. -/
theorem preserves_unit_gap (t s f : ℝ) (hf : f^2 = 1)
    (hgap : 1 ≤ f*s) (hfactor : 0 < 1-f*t) (hden : 0 < 1+t*s) :
    1 ≤ f * transform t s := by
  have h := unit_residual t s f hf hden.ne'
  have hp : 0 ≤ (f*s-1)*(1-f*t)/(1+t*s) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hgap) hfactor.le) hden.le
  linarith

theorem transform_ratio (t A B : ℝ) (hB : B ≠ 0) (hnew : B+t*A ≠ 0) :
    transform t (A/B) = (A+t*B)/(B+t*A) := by
  have hden : 1+t*(A/B) ≠ 0 := by
    have he : 1+t*(A/B) = (B+t*A)/B := by field_simp
    rw [he]
    exact div_ne_zero hnew hB
  unfold transform
  field_simp [hB, hnew, hden]

theorem changes_nonunit (t s : ℝ) (ht : t ≠ 0) (hs : s^2 ≠ 1)
    (hden : 1+t*s ≠ 0) : transform t s ≠ s := by
  intro he
  have h := (div_eq_iff hden).mp he
  have hz : t*(1-s^2) = 0 := by nlinarith
  have hs' := (mul_eq_zero.mp hz).resolve_left ht
  exact hs (by linarith)

end Moebius

end HeadComplexity.OneHeadFullContact
