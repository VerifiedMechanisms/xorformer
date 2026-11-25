import HeadComplexity.Research.PositiveReciprocalExpansion
import HeadComplexity.Research.OriginalMarginCapacity

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.OriginalAnchoredExpansion
open scoped BigOperators
open Finset RelativeMarginQuantifiers OriginalMarginCapacity

variable {n : ℕ}

theorem norm_eval_eq_atomSup (φ : FracAtom n) : ‖φ.eval‖ = atomSup φ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (atomSup_nonneg φ)).mpr
    intro x
    simpa only [Real.norm_eq_abs] using abs_eval_le_atomSup φ x
  · unfold atomSup
    apply sup'_le
    intro x hx
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm φ.eval x

theorem coordinates_involutive (t : Bool) (x : Fin n → Bool) :
    CoefficientOrderChart.coordinates t (CoefficientOrderChart.coordinates t x) = x := by
  funext i
  cases t <;> cases h : x i <;> simp [CoefficientOrderChart.coordinates, h]

theorem uniformly_coordinates (g : (Fin n → Bool) → ℝ)
    (hg : UniformlyOneAtomApproximable g) (t : Bool) :
    UniformlyOneAtomApproximable (fun x => g (CoefficientOrderChart.coordinates t x)) := by
  intro ε hε
  obtain ⟨φ, hφ⟩ := hg ε hε
  cases t
  · exact ⟨φ, hφ⟩
  · refine ⟨φ.flip, fun x => ?_⟩
    have hx : CoefficientOrderChart.coordinates true x = flipBits x := by
      funext i
      simp [CoefficientOrderChart.coordinates, flipBits]
    change |φ.flip.eval x - g (CoefficientOrderChart.coordinates true x)| < ε
    rw [FracAtom.flip_eval, hx]
    exact hφ (flipBits x)

theorem uniformly_scaled_face_affine (s : Finset (Fin n)) (k a : ℝ)
    (u : Fin n → ℝ) : UniformlyOneAtomApproximable
      (fun x => k * PositiveReciprocalExpansion.face s x * HeadComplexity.affineValue a u x) := by
  have hh := PositiveReciprocalExpansion.uniformlyOneAtomApproximable_face_affine
    s (k*a) (fun i => k*u i)
  convert hh using 1
  funext x
  unfold HeadComplexity.affineValue
  have he : (∑ i, (k * u i) * boolToReal (x i)) = k * ∑ i, u i * boolToReal (x i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

/-- Every original head has an exact anchored affine-block expansion with
full-cube total block norm at most `n+1` times its requested atom supremum.
Each block is uniformly approximable by one genuine original head. This
uses all subsets, and therefore supplies no constant-overhead repair. -/
theorem original_head_expansion (φ : FracAtom n) :
    ∃ blocks : Finset (Fin n) → (Fin n → Bool) → ℝ,
      (∀ s, UniformlyOneAtomApproximable (blocks s)) ∧
      (∀ x, φ.eval x = ∑ s, blocks s x) ∧
      (∑ s, ‖blocks s‖) ≤ ((n : ℝ) + 1) * atomSup φ := by
  classical
  let ψ := orientedAtom φ
  let t := orientation φ
  let a := numeratorCoefficients ψ none
  let u : Fin n → ℝ := fun i => numeratorCoefficients ψ (some i)
  let c := denominatorCoefficients ψ none
  let w : Fin n → ℝ := fun i => denominatorCoefficients ψ (some i)
  let A := HeadComplexity.affineValue a u
  have hc : 0 < c := denominatorCoefficients_constant_pos ψ
  have hw (i : Fin n) : 0 ≤ w i :=
    denominatorCoefficients_nonneg ψ (orientedAtom_alpha φ) (some i)
  have hratio (x : Fin n → Bool) :
      A x / (c + ∑ i, w i * (if x i then 1 else 0)) = ψ.eval x := by
    simpa only [A, a, u, c, w, HeadComplexity.affineValue,
      CoefficientOrderChart.affineValue, boolToReal, mul_comm] using affineRatio_eq_eval ψ x
  obtain ⟨κ, hκ, he, hmass⟩ :=
    PositiveReciprocalExpansion.ratio_with_full_cube_mass A w hw c hc
  let blocks : Finset (Fin n) → (Fin n → Bool) → ℝ := fun s x =>
    κ s * PositiveReciprocalExpansion.face s (CoefficientOrderChart.coordinates t x) *
      A (CoefficientOrderChart.coordinates t x)
  have hnorm : ‖ψ.eval‖ ≤ atomSup φ := by
    apply (pi_norm_le_iff_of_nonneg (atomSup_nonneg φ)).mpr
    intro x
    have hh := orientedAtom_eval φ (CoefficientOrderChart.coordinates t x)
    rw [coordinates_involutive] at hh
    rw [show ψ.eval x = φ.eval (CoefficientOrderChart.coordinates t x) from hh]
    simpa only [Real.norm_eq_abs] using abs_eval_le_atomSup φ _
  refine ⟨blocks, ?_, ?_, ?_⟩
  · intro s
    exact uniformly_coordinates _ (uniformly_scaled_face_affine s (κ s) a u) t
  · intro x
    simp_rw [hratio] at he
    exact (orientedAtom_eval φ x).symm.trans (he (CoefficientOrderChart.coordinates t x))
  · have hblocks : (∑ s, ‖blocks s‖) ≤
        ∑ s, ‖fun x => κ s * PositiveReciprocalExpansion.face s x * A x‖ := by
      apply sum_le_sum
      intro s hs
      exact pi_norm_comp_le (fun x : Fin n → Bool =>
        κ s * PositiveReciprocalExpansion.face s x * A x) (CoefficientOrderChart.coordinates t)
    have hefun : (fun x => A x / (c + ∑ i, w i * (if x i then 1 else 0))) = ψ.eval :=
      funext hratio
    rw [hefun] at hmass
    exact hblocks.trans (hmass.trans (mul_le_mul_of_nonneg_left hnorm (by positivity)))

end HeadComplexity.OriginalAnchoredExpansion
