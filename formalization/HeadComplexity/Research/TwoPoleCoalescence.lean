import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
Exact sign-preserving coalescence of two affine-ratio poles.  The base pole
has strictly positive coefficients; the other pole need only be positive on
the full Boolean cube.  Arbitrarily small positive parameters preserve
admissibility.  The affine numerators are allowed to diverge as the parameter
tends to zero, as permitted in the original unrestricted model.
-/

noncomputable section
namespace HeadComplexity.TwoPoleCoalescence

open scoped BigOperators
open Filter Topology

variable {n : ℕ}

def movingConstant (b₁ b₂ t : ℝ) : ℝ := b₂ + t * (b₁ - b₂)

def movingSlopes (b₁ b₂ : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  b₂ i + t * (b₁ i - b₂ i)

theorem movingValue (b₁₀ b₂₀ t : ℝ) (b₁ b₂ : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (movingConstant b₁₀ b₂₀ t) (movingSlopes b₁ b₂ t) x =
      affineValue b₂₀ b₂ x + t * (affineValue b₁₀ b₁ x - affineValue b₂₀ b₂ x) := by
  have hc : movingConstant b₁₀ b₂₀ t = b₂₀ + t * b₁₀ + (-t) * b₂₀ := by
    unfold movingConstant
    ring
  have hs : movingSlopes b₁ b₂ t = fun i ↦ b₂ i + t * b₁ i + (-t) * b₂ i := by
    funext i
    unfold movingSlopes
    ring
  rw [hc, hs, affineValue_add, affineValue_add, affineValue_smul, affineValue_smul]
  ring

theorem eventually_positive_coefficients (b₁₀ b₂₀ : ℝ) (b₁ b₂ : Fin n → ℝ)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i) :
    ∀ᶠ t : ℝ in 𝓝 0,
      0 < movingConstant b₁₀ b₂₀ t ∧ ∀ i, 0 < movingSlopes b₁ b₂ t i := by
  have hc : Continuous (movingConstant b₁₀ b₂₀) := by
    unfold movingConstant
    fun_prop
  have hs (i : Fin n) : Continuous (fun t ↦ movingSlopes b₁ b₂ t i) := by
    unfold movingSlopes
    fun_prop
  have h₀ : ∀ᶠ t : ℝ in 𝓝 0, 0 < movingConstant b₁₀ b₂₀ t :=
    (hc.tendsto 0).eventually (eventually_gt_nhds (by simpa [movingConstant] using hb₂₀))
  have hi (i : Fin n) : ∀ᶠ t : ℝ in 𝓝 0, 0 < movingSlopes b₁ b₂ t i :=
    (hs i |>.tendsto 0).eventually
      (eventually_gt_nhds (by simpa [movingSlopes] using hb₂ i))
  exact h₀.and (Filter.eventually_all.mpr hi)

/-- The exact identity behind coalescence.  It is an identity of values,
with no sign, norm, or genericity hypothesis on either numerator. -/
theorem score_identity (A₁ A₂ B₁ B₂ t : ℝ)
    (ht : t ≠ 0) (hB₂ : B₂ ≠ 0) (hD : B₂ + t * (B₁ - B₂) ≠ 0) :
    (A₂ / t) / B₂ + (A₁ + (1 - 1 / t) * A₂) / (B₂ + t * (B₁ - B₂)) =
      (A₁ * B₂ + A₂ * B₁) / (B₂ * (B₂ + t * (B₁ - B₂))) := by
  field_simp
  ring

/-- The limiting score uses only the first two reciprocal jets of the
single affine germ `B₂ + s * (B₁ - B₂)`. -/
theorem coalesced_score_identity (A₁ A₂ B₁ B₂ : ℝ) (hB₂ : B₂ ≠ 0) :
    (A₁ + A₂) / B₂ - A₂ * (-(B₁ - B₂) / B₂ ^ 2) =
      (A₁ * B₂ + A₂ * B₁) / B₂ ^ 2 := by
  field_simp
  ring

theorem coalesced_sign (A₁ A₂ B₁ B₂ : ℝ) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) :
    (0 < (A₁ + A₂) / B₂ - A₂ * (-(B₁ - B₂) / B₂ ^ 2)) ↔
      0 < A₁ / B₁ + A₂ / B₂ := by
  rw [coalesced_score_identity A₁ A₂ B₁ B₂ hB₂.ne',
    div_pos_iff_of_pos_right (sq_pos_of_pos hB₂),
    div_add_div _ _ hB₁.ne' hB₂.ne',
    div_pos_iff_of_pos_right (mul_pos hB₁ hB₂), mul_comm B₁ A₂]

def atoms (a₁₀ a₂₀ b₁₀ b₂₀ t : ℝ)
    (a₁ a₂ b₁ b₂ : Fin n → ℝ)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i)
    (hd₀ : 0 < movingConstant b₁₀ b₂₀ t)
    (hd : ∀ i, 0 < movingSlopes b₁ b₂ t i) : Fin 2 → FracAtom n :=
  ![FracAtom.ofPositiveAffineRatio ((1 / t) * a₂₀) (fun i ↦ (1 / t) * a₂ i)
      b₂₀ b₂ hb₂₀ hb₂,
    FracAtom.ofPositiveAffineRatio (a₁₀ + (1 - 1 / t) * a₂₀)
      (fun i ↦ a₁ i + (1 - 1 / t) * a₂ i)
      (movingConstant b₁₀ b₂₀ t) (movingSlopes b₁ b₂ t) hd₀ hd]

theorem atoms_score (a₁₀ a₂₀ b₁₀ b₂₀ t : ℝ)
    (a₁ a₂ b₁ b₂ : Fin n → ℝ)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i)
    (hd₀ : 0 < movingConstant b₁₀ b₂₀ t)
    (hd : ∀ i, 0 < movingSlopes b₁ b₂ t i) (ht : t ≠ 0)
    (x : Fin n → Bool) :
    ∑ h, (atoms a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hd₀ hd h).eval x =
      (affineValue a₁₀ a₁ x * affineValue b₂₀ b₂ x +
        affineValue a₂₀ a₂ x * affineValue b₁₀ b₁ x) /
      (affineValue b₂₀ b₂ x *
        affineValue (movingConstant b₁₀ b₂₀ t) (movingSlopes b₁ b₂ t) x) := by
  have hB₂ := affineValue_pos b₂₀ b₂ hb₂₀ hb₂ x
  have hD := affineValue_pos _ _ hd₀ hd x
  simp only [Fin.sum_univ_two, atoms, Matrix.cons_val_zero, Matrix.cons_val_one,
    FracAtom.ofPositiveAffineRatio_eval, affineValue_add, affineValue_smul]
  rw [movingValue] at hD ⊢
  convert score_identity (affineValue a₁₀ a₁ x) (affineValue a₂₀ a₂ x)
    (affineValue b₁₀ b₁ x) (affineValue b₂₀ b₂ x) t ht hB₂.ne' hD.ne' using 1
  congr 2
  ring

/-- Each admissible member of the coalescence family has exactly the
original full Boolean truth table. -/
theorem atoms_sign (a₁₀ a₂₀ b₁₀ b₂₀ t : ℝ)
    (a₁ a₂ b₁ b₂ : Fin n → ℝ)
    (hb₁ : ∀ x, 0 < affineValue b₁₀ b₁ x)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i)
    (hd₀ : 0 < movingConstant b₁₀ b₂₀ t)
    (hd : ∀ i, 0 < movingSlopes b₁ b₂ t i) (ht : t ≠ 0)
    (x : Fin n → Bool) :
    (0 < ∑ h, (atoms a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hd₀ hd h).eval x) ↔
      0 < affineValue a₁₀ a₁ x / affineValue b₁₀ b₁ x +
        affineValue a₂₀ a₂ x / affineValue b₂₀ b₂ x := by
  rw [atoms_score a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hd₀ hd ht]
  have hB₂ := affineValue_pos b₂₀ b₂ hb₂₀ hb₂ x
  have hD := affineValue_pos _ _ hd₀ hd x
  rw [div_pos_iff_of_pos_right (mul_pos hB₂ hD),
    div_add_div _ _ (hb₁ x).ne' hB₂.ne',
    div_pos_iff_of_pos_right (mul_pos (hb₁ x) hB₂)]
  rw [mul_comm (affineValue b₁₀ b₁ x)]

theorem atoms_denom_zero (a₁₀ a₂₀ b₁₀ b₂₀ t : ℝ)
    (a₁ a₂ b₁ b₂ : Fin n → ℝ)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i)
    (hd₀ : 0 < movingConstant b₁₀ b₂₀ t)
    (hd : ∀ i, 0 < movingSlopes b₁ b₂ t i) (x : Fin n → Bool) :
    let phi := atoms a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hd₀ hd 0
    phi.γ + ∑ i, phi.wt x i = affineValue b₂₀ b₂ x := by
  simp only [atoms, Matrix.cons_val_zero, FracAtom.ofPositiveAffineRatio_denom]

theorem atoms_denom_one (a₁₀ a₂₀ b₁₀ b₂₀ t : ℝ)
    (a₁ a₂ b₁ b₂ : Fin n → ℝ)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i)
    (hd₀ : 0 < movingConstant b₁₀ b₂₀ t)
    (hd : ∀ i, 0 < movingSlopes b₁ b₂ t i) (x : Fin n → Bool) :
    let phi := atoms a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hd₀ hd 1
    phi.γ + ∑ i, phi.wt x i = affineValue b₂₀ b₂ x +
      t * (affineValue b₁₀ b₁ x - affineValue b₂₀ b₂ x) := by
  simp only [atoms, Matrix.cons_val_one, Matrix.cons_val_zero,
    FracAtom.ofPositiveAffineRatio_denom, movingValue]

/-- Arbitrarily close to zero, the prescribed two coalescing denominators
admit original heads preserving the complete truth table. -/
theorem eventually_admissible_coalescence (a₁₀ a₂₀ b₁₀ b₂₀ : ℝ)
    (a₁ a₂ b₁ b₂ : Fin n → ℝ)
    (hb₁ : ∀ x, 0 < affineValue b₁₀ b₁ x)
    (hb₂₀ : 0 < b₂₀) (hb₂ : ∀ i, 0 < b₂ i) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ phi : Fin 2 → FracAtom n,
      (∀ x, (0 < ∑ h, (phi h).eval x) ↔
        0 < affineValue a₁₀ a₁ x / affineValue b₁₀ b₁ x +
          affineValue a₂₀ a₂ x / affineValue b₂₀ b₂ x) ∧
      (∀ x, (phi 0).γ + ∑ i, (phi 0).wt x i = affineValue b₂₀ b₂ x) ∧
      (∀ x, (phi 1).γ + ∑ i, (phi 1).wt x i = affineValue b₂₀ b₂ x +
        t * (affineValue b₁₀ b₁ x - affineValue b₂₀ b₂ x)) := by
  have hcoeff := (eventually_positive_coefficients b₁₀ b₂₀ b₁ b₂ hb₂₀ hb₂).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  filter_upwards [hcoeff, self_mem_nhdsWithin] with t hc ht
  refine ⟨atoms a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hc.1 hc.2, ?_, ?_, ?_⟩
  · exact atoms_sign a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₁ hb₂₀ hb₂ hc.1 hc.2
      (ne_of_gt ht)
  · exact atoms_denom_zero a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hc.1 hc.2
  · exact atoms_denom_one a₁₀ a₂₀ b₁₀ b₂₀ t a₁ a₂ b₁ b₂ hb₂₀ hb₂ hc.1 hc.2

end HeadComplexity.TwoPoleCoalescence
