import HeadComplexity.Research.OneHeadMarginOptimum
import HeadComplexity.Research.OneHeadLayerAverages
import HeadComplexity.Research.OriginalMarginCapacity
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.OneHeadOriginalMarginOptimum
open Finset
open scoped BigOperators
open RelativeMarginQuantifiers

/-- Every genuine one-head score, with arbitrary bias and either coherent
orientation, is an affine ratio with positive denominator on the full cube. -/
theorem exists_affine_score {n : ℕ} (φ : Fin 1 → FracAtom n) (bias : ℝ) :
    ∃ (a₀ b₀ : ℝ) (a b : Fin n → ℝ),
      (∀ x, 0 < affineValue b₀ b x) ∧
      (∀ x, score φ bias x = affineValue a₀ a x / affineValue b₀ b x) := by
  let A := OriginalMarginCapacity.numeratorCoefficients (φ 0)
  let B := OriginalMarginCapacity.denominatorCoefficients (φ 0)
  have hA (x : Fin n → Bool) :
      affineValue (A none) (fun i => A (some i)) x =
        CoefficientOrderChart.affineValue A x := by
    simp only [affineValue, CoefficientOrderChart.affineValue, mul_comm]
  have hB (x : Fin n → Bool) :
      affineValue (B none) (fun i => B (some i)) x =
        CoefficientOrderChart.affineValue B x := by
    simp only [affineValue, CoefficientOrderChart.affineValue, mul_comm]
  have hpos (x : Fin n → Bool) : 0 < affineValue (B none) (fun i => B (some i)) x := by
    rw [hB, OriginalMarginCapacity.affineValue_denominatorCoefficients]
    exact (φ 0).denom_pos x
  refine ⟨A none+bias*B none, B none,
    (fun i => A (some i)+bias*B (some i)), (fun i => B (some i)), hpos, ?_⟩
  intro x
  rw [affineValue_add, affineValue_smul]
  have he := OriginalMarginCapacity.affineRatio_eq_eval (φ 0) x
  change CoefficientOrderChart.affineValue A x /
    CoefficientOrderChart.affineValue B x = (φ 0).eval x at he
  simp only [score, Fin.sum_univ_one]
  rw [← he, ← hA, ← hB]
  field_simp [(hpos x).ne']
  ring

/-- A universal upper bound over every original one-head representation,
with arbitrary bias, coefficients, and either admissible denominator orientation. -/
theorem relativeMargin_le (φ : Fin 1 → FracAtom 5) (bias : ℝ)
    (hs : StrictlyRepresents OneHeadLayerAverages.thresholdTwo φ bias) :
    relativeMargin OneHeadLayerAverages.thresholdTwo φ bias ≤
      5/(11+4*Real.sqrt 6) := by
  obtain ⟨a₀,b₀,a,b,hB,he⟩ := exists_affine_score φ bias
  let m := minimumSignedScore OneHeadLayerAverages.thresholdTwo φ bias
  let D := amplitude φ bias
  have hm : 0 < m := minimumSignedScore_pos_iff.mpr hs
  have hD : 0 < D := amplitude_pos_of_strict hs
  have he' (x : Fin 5 → Bool) :
      affineValue (a₀/m) (fun i => a i/m) x / affineValue b₀ b x =
        score φ bias x / m := by
    rw [he]
    have ha : affineValue (a₀/m) (fun i => a i/m) x =
        affineValue a₀ a x / m := by
      simp only [affineValue, div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
    rw [ha]
    ring
  have hnorm (x : Fin 5 → Bool) :
      |affineValue (a₀/m) (fun i => a i/m) x / affineValue b₀ b x| ≤ D/m := by
    rw [he', abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right (abs_score_le_amplitude φ bias x) hm.le
  have hgap (x : Fin 5 → Bool) :
      1 ≤ signedLabel OneHeadLayerAverages.thresholdTwo x *
        (affineValue (a₀/m) (fun i => a i/m) x / affineValue b₀ b x) := by
    rw [he', ← mul_div_assoc, le_div_iff₀ hm, one_mul]
    exact Finset.inf'_le _ (Finset.mem_univ x)
  have hk := OneHeadLayerAverages.affine_ratio_budget
    (a₀/m) b₀ (D/m) (fun i => a i/m) b hB hnorm hgap
  have hroot : 0 < 11+4*Real.sqrt 6 := by positivity
  have hkm : ((11+4*Real.sqrt 6)/5)*m ≤ D :=
    (le_div_iff₀ hm).mp hk
  change m/D ≤ 5/(11+4*Real.sqrt 6)
  apply (div_le_div_iff₀ hD hroot).mpr
  nlinarith

/-- The failure quantifies over every representation at width one. -/
theorem not_hasRelativeMargin {γ : ℝ}
    (hγ : 5/(11+4*Real.sqrt 6) < γ) :
    ¬ HasRelativeMargin 5 1 OneHeadLayerAverages.thresholdTwo γ := by
  rintro ⟨φ,bias,hs,hmargin⟩
  exact (not_lt_of_ge (hmargin.trans (relativeMargin_le φ bias hs))) hγ

/-- A genuine strictly positive-slope head attains the universal bound. -/
theorem exists_attaining :
    ∃ (φ : Fin 1 → FracAtom 5) (bias : ℝ),
      StrictlyRepresents OneHeadLayerAverages.thresholdTwo φ bias ∧
      relativeMargin OneHeadLayerAverages.thresholdTwo φ bias =
        5/(11+4*Real.sqrt 6) := by
  let K : ℝ := (11+4*Real.sqrt 6)/5
  let d : ℝ := (K-3)/4
  have hd : 0 < d := by
    simpa [K, d] using OneHeadMarginOptimum.sharp_parameters.1
  have hK : 0 < K := by dsimp [K]; positivity
  let ψ : FracAtom 5 := FracAtom.ofPositiveAffineRatio
    (-K) (fun _ => 2+3*d) 1 (fun _ => d) zero_lt_one (fun _ => hd)
  let φ : Fin 1 → FracAtom 5 := fun _ => ψ
  have he (x : Fin 5 → Bool) :
      ψ.eval x = affineValue (-K) (fun _ => 2+3*d) x /
        affineValue 1 (fun _ => d) x :=
    FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x
  have hb (x : Fin 5 → Bool) : |ψ.eval x| ≤ K ∧
      1 ≤ signedLabel OneHeadLayerAverages.thresholdTwo x * ψ.eval x := by
    let k : Fin 6 := ⟨(Finset.univ.filter fun i => x i = true).card, by
      have hc := Finset.card_filter_le (Finset.univ : Finset (Fin 5)) (fun i => x i = true)
      norm_num at hc
      omega⟩
    have hh := OneHeadLayerAverages.witness_layer_bounds k
    rw [he, OneHeadLayerAverages.affine_uniformSlope,
      OneHeadLayerAverages.affine_uniformSlope]
    simpa [K, d, k, signedLabel, OneHeadLayerAverages.thresholdTwo] using hh.2
  have hs : StrictlyRepresents OneHeadLayerAverages.thresholdTwo φ 0 := by
    intro x
    have hx := (hb x).2
    simpa [score, φ] using (show 0 < signedLabel OneHeadLayerAverages.thresholdTwo x * ψ.eval x by linarith)
  have hsup : atomSup ψ ≤ K := by
    unfold atomSup
    exact Finset.sup'_le _ _ (fun x _ => (hb x).1)
  have ha : amplitude φ 0 ≤ K := by simpa [amplitude, φ] using hsup
  have hlo : 5/(11+4*Real.sqrt 6) ≤
      relativeMargin OneHeadLayerAverages.thresholdTwo φ 0 := by
    apply (le_relativeMargin_iff hs).mpr
    intro x
    have hratio : 5/(11+4*Real.sqrt 6) = 1/K := by
      have hp : 11+4*Real.sqrt 6 ≠ 0 := by positivity
      dsimp [K]
      field_simp [hp]
    rw [hratio]
    have hbudget : (1/K)*amplitude φ 0 ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hK]
      simpa using ha
    exact hbudget.trans (by simpa [score, φ] using (hb x).2)
  exact ⟨φ,0,hs,le_antisymm (relativeMargin_le φ 0 hs) hlo⟩

/-- Exact characterization of all attainable relative margins, with the
existential quantifier ranging over the original unrestricted one-head model. -/
theorem hasRelativeMargin_iff (γ : ℝ) :
    HasRelativeMargin 5 1 OneHeadLayerAverages.thresholdTwo γ ↔
      γ ≤ 5/(11+4*Real.sqrt 6) := by
  constructor
  · rintro ⟨φ,bias,hs,hmargin⟩
    exact hmargin.trans (relativeMargin_le φ bias hs)
  · intro hγ
    obtain ⟨φ,bias,hs,he⟩ := exists_attaining
    exact ⟨φ,bias,hs,by simpa [he] using hγ⟩

/-- One explicit table has a globally optimal width-one representation, and
no arbitrary width-one replacement has a better relative margin. -/
theorem exists_no_same_width_improvement :
    ∃ (φ : Fin 1 → FracAtom 5) (bias : ℝ),
      StrictlyRepresents OneHeadLayerAverages.thresholdTwo φ bias ∧
      relativeMargin OneHeadLayerAverages.thresholdTwo φ bias < 1 ∧
      ∀ (ψ : Fin 1 → FracAtom 5) (b : ℝ),
        StrictlyRepresents OneHeadLayerAverages.thresholdTwo ψ b →
        relativeMargin OneHeadLayerAverages.thresholdTwo ψ b ≤
          relativeMargin OneHeadLayerAverages.thresholdTwo φ bias := by
  obtain ⟨φ,bias,hs,he⟩ := exists_attaining
  refine ⟨φ,bias,hs,?_,?_⟩
  · rw [he]
    have hp : 0 < 11+4*Real.sqrt 6 := by positivity
    apply (div_lt_one hp).mpr
    linarith [Real.sqrt_nonneg (6:ℝ)]
  · intro ψ b hψ
    rw [he]
    exact relativeMargin_le ψ b hψ

end HeadComplexity.OneHeadOriginalMarginOptimum
