import HeadComplexity.Research.LiteralMarginNonattainmentWitness
import HeadComplexity.Research.MarginOneCollapse
import HeadComplexity.Research.MarginInvariance
import HeadComplexity.Research.OriginalMarginCapacity
import HeadComplexity.Research.UnitGapBasisGeometry

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.LiteralMarginNonattainment
open Finset RelativeMarginQuantifiers OriginalMarginCapacity
open LiteralMarginNonattainmentWitness
open scoped BigOperators

private theorem affine_update {d : ℕ} (a : Option (Fin d) → ℝ)
    (x : Fin d → Bool) (i : Fin d) (hi : x i = false) :
    CoefficientOrderChart.affineValue a (Function.update x i true) =
      CoefficientOrderChart.affineValue a x + a (some i) := by
  simpa only [HeadComplexity.affineValue, CoefficientOrderChart.affineValue, mul_comm] using
    UnitGapBasisGeometry.affineValue_update_true (a none) (fun j => a (some j)) x i hi

/-- An admissible original head in dimension at least two cannot take exactly
opposite nonzero values according to one input coordinate. The common alpha
and common numerator shift in the original model are essential. -/
theorem no_atom_signed_literal (n : ℕ) (φ : FracAtom (n+2)) (M : ℝ) (hM : 0 < M) :
    ¬ (∀ x, φ.eval x = M * signedLabel (literal (n+1)) x) := by
  intro he
  let A := numeratorCoefficients φ
  let B := denominatorCoefficients φ
  let z : Fin (n+2) → Bool := fun _ => false
  let u := Function.update z (0 : Fin (n+2)) true
  let v := Function.update z (1 : Fin (n+2)) true
  let w := Function.update u (1 : Fin (n+2)) true
  have h01 : (0 : Fin (n+2)) ≠ 1 := by intro h; have := congrArg Fin.val h; simp at this
  have h10 : (1 : Fin (n+2)) ≠ 0 := Ne.symm h01
  have hrel (x : Fin (n+2) → Bool) :
      CoefficientOrderChart.affineValue A x =
        M * signedLabel (literal (n+1)) x * CoefficientOrderChart.affineValue B x := by
    have hp : 0 < CoefficientOrderChart.affineValue B x := by
      dsimp [B]
      rw [affineValue_denominatorCoefficients]
      exact φ.denom_pos x
    apply (div_eq_iff hp.ne').mp
    simpa only [A, B, affineRatio_eq_eval] using he x
  have hA0 : CoefficientOrderChart.affineValue A z = A none := by simp [CoefficientOrderChart.affineValue,z,boolToReal]
  have hB0 : CoefficientOrderChart.affineValue B z = B none := by simp [CoefficientOrderChart.affineValue,z,boolToReal]
  have hAu : CoefficientOrderChart.affineValue A u = A none + A (some 0) := by
    rw [show u = Function.update z 0 true from rfl, affine_update A z 0 rfl, hA0]
  have hBu : CoefficientOrderChart.affineValue B u = B none + B (some 0) := by
    rw [show u = Function.update z 0 true from rfl, affine_update B z 0 rfl, hB0]
  have hAv : CoefficientOrderChart.affineValue A v = A none + A (some 1) := by
    rw [show v = Function.update z 1 true from rfl, affine_update A z 1 rfl, hA0]
  have hBv : CoefficientOrderChart.affineValue B v = B none + B (some 1) := by
    rw [show v = Function.update z 1 true from rfl, affine_update B z 1 rfl, hB0]
  have hu : u 1 = false := by simp [u,z,h10]
  have hAw : CoefficientOrderChart.affineValue A w = A none + A (some 0) + A (some 1) := by
    rw [show w = Function.update u 1 true from rfl, affine_update A u 1 hu, hAu]
  have hBw : CoefficientOrderChart.affineValue B w = B none + B (some 0) + B (some 1) := by
    rw [show w = Function.update u 1 true from rfl, affine_update B u 1 hu, hBu]
  have hz := hrel z
  have hu' := hrel u
  have hv := hrel v
  have hw := hrel w
  rw [hA0,hB0] at hz
  rw [hAu,hBu] at hu'
  rw [hAv,hBv] at hv
  rw [hAw,hBw] at hw
  have hzsign : signedLabel (literal (n+1)) z = -1 := by simp [signedLabel,literal,z]
  rw [hzsign,mul_neg_one] at hz
  have hlu : signedLabel (literal (n+1)) u = 1 := by simp [signedLabel,literal,u]
  have hlv : signedLabel (literal (n+1)) v = -1 := by simp [signedLabel,literal,v,z,h01]
  have hlw : signedLabel (literal (n+1)) w = 1 := by simp [signedLabel,literal,w,u,h01]
  rw [hlu,mul_one] at hu'
  rw [hlv,mul_neg_one] at hv
  rw [hlw,mul_one] at hw
  have hb1 : B (some 1) = 0 := by nlinarith
  have ha1 : A (some 1) = 0 := by nlinarith
  have halpha : φ.α = 1 := by
    have hp := φ.hρ (1 : Fin (n+2))
    change φ.ρ 1 * (φ.α - 1) = 0 at hb1
    have hh := (mul_eq_zero.mp hb1).resolve_left hp.ne'
    linarith
  have hdelta : φ.δ = 0 := by
    change φ.ρ 1 * (φ.α * (φ.m 1 + φ.δ) - φ.m 1) = 0 at ha1
    rw [halpha,one_mul,add_sub_cancel_left] at ha1
    exact (mul_eq_zero.mp ha1).resolve_left (φ.hρ 1).ne'
  have hbzero : B (some 0) = 0 := by simp [B,denominatorCoefficients,halpha]
  have hazero : A (some 0) = 0 := by simp [A,numeratorCoefficients,halpha,hdelta]
  have hbp : 0 < B none := denominatorCoefficients_constant_pos φ
  rw [hbzero,hazero] at hu'
  nlinarith

/-- No finite-width representation of a literal in dimension at least two
attains relative margin one in the original admissible model. -/
theorem not_hasRelativeMargin_one (n H : ℕ) :
    ¬ HasRelativeMargin (n+2) H (literal (n+1)) 1 := by
  rintro ⟨φ,b,hs,hm⟩
  have hf : ∃ x, literal (n+1) x = false := ⟨(fun _ => false),rfl⟩
  have ht : ∃ x, literal (n+1) x = true := ⟨(fun _ => true),rfl⟩
  have hb := MarginOneCollapse.bias_eq_zero_of_margin_one hs hm hf ht
  have hsum : 0 < ∑ h, atomSup (φ h) := by
    simpa [amplitude,hb] using amplitude_pos_of_strict hs
  have hex : ∃ h, 0 < atomSup (φ h) := by
    by_contra hn
    push Not at hn
    have hle := Finset.sum_nonpos (s := Finset.univ) (fun h _ => hn h)
    linarith
  obtain ⟨h,hh⟩ := hex
  exact no_atom_signed_literal n (φ h) (atomSup (φ h)) hh
    (MarginOneCollapse.eval_eq_norm_mul_signedLabel hs hm h)

/-- At every fixed positive width, the achievable relative-margin thresholds
for this literal form the open interval below one. In particular the optimal
margin supremum is not attained in the original admissible parameter space. -/
theorem hasRelativeMargin_iff_lt_one (n H : ℕ) (hH : 1 ≤ H) (γ : ℝ) :
    HasRelativeMargin (n+2) H (literal (n+1)) γ ↔ γ < 1 := by
  constructor
  · intro hf
    by_contra hn
    exact not_hasRelativeMargin_one n H
      (hasRelativeMargin_mono (le_of_not_gt hn) hf)
  · intro hγ
    exact hasRelativeMargin_mono_width hH
      (hasRelativeMargin_below_one (n+1) γ hγ)

end HeadComplexity.LiteralMarginNonattainment
