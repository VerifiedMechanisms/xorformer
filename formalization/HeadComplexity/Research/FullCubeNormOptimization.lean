import HeadComplexity.Research.MidrangeMarginCentering
import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.FullCubeNormOptimization
open scoped BigOperators
open MidrangeMarginCentering RelativeMarginQuantifiers
variable {n H : ℕ}

/-- An affine form's full Boolean maximum is a sum of positive parts. -/
theorem affine_le_iff (a₀ : ℝ) (a : Fin n → ℝ) (t : ℝ) :
    (∀ x : Fin n → Bool, affineValue a₀ a x ≤ t) ↔
      a₀ + ∑ i, max (a i) 0 ≤ t := by
  constructor
  · intro h
    let x : Fin n → Bool := fun i => decide (0 < a i)
    have hx : affineValue a₀ a x = a₀ + ∑ i, max (a i) 0 := by
      unfold affineValue
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 < a i
      · simp [x, hi, boolToReal, max_eq_left hi.le]
      · simp [x, hi, boolToReal, max_eq_right (le_of_not_gt hi)]
    simpa only [hx] using h x
  · intro h x
    apply le_trans ?_ h
    unfold affineValue
    gcongr with i
    cases x i <;> simp [boolToReal]

/-- The full-cube norm constraint for an affine ratio needs only two
coordinate positive-part sums. No denominator coefficient sign is assumed. -/
theorem ratio_norm_bound_iff (a₀ b₀ m : ℝ) (a b : Fin n → ℝ)
    (hb : ∀ x, 0 < affineValue b₀ b x) :
    (∀ x, |affineValue a₀ a x / affineValue b₀ b x| ≤ m) ↔
      (a₀-m*b₀ + ∑ i, max (a i-m*b i) 0 ≤ 0) ∧
      (-a₀-m*b₀ + ∑ i, max (-a i-m*b i) 0 ≤ 0) := by
  have hpoint : ∀ x, |affineValue a₀ a x / affineValue b₀ b x| ≤ m ↔
      affineValue (a₀-m*b₀) (fun i => a i-m*b i) x ≤ 0 ∧
      affineValue (-a₀-m*b₀) (fun i => -a i-m*b i) x ≤ 0 := by
    intro x
    rw [abs_div, abs_of_pos (hb x), div_le_iff₀ (hb x), abs_le]
    have h₁ : affineValue (a₀-m*b₀) (fun i => a i-m*b i) x =
        affineValue a₀ a x-m*affineValue b₀ b x := by
      simp only [affineValue, sub_mul, Finset.sum_sub_distrib, mul_assoc,
        ← Finset.mul_sum]
      ring
    have h₂ : affineValue (-a₀-m*b₀) (fun i => -a i-m*b i) x =
        -affineValue a₀ a x-m*affineValue b₀ b x := by
      simp only [affineValue, sub_mul, neg_mul, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    rw [h₁, h₂]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp_rw [hpoint]
  rw [forall_and, affine_le_iff, affine_le_iff]

/-- For coherent nonnegative denominator slopes the maximizing vertices for
both residuals can be chosen with disjoint supports. -/
theorem residual_positive_parts_disjoint (a b m : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m) :
    ¬ (0 < a-m*b ∧ 0 < -a-m*b) := by
  have h := mul_nonneg hm hb
  rintro ⟨h₁,h₂⟩
  linarith

theorem rangeMax_le_atomSup (phi : FracAtom n) : rangeMax phi ≤ atomSup phi := by
  apply Finset.sup'_le
  intro x _
  exact (le_abs_self _).trans (abs_eval_le_atomSup phi x)

theorem neg_rangeMin_le_atomSup (phi : FracAtom n) : -rangeMin phi ≤ atomSup phi := by
  have h : -atomSup phi ≤ rangeMin phi := by
    apply Finset.le_inf'
    intro x _
    exact (neg_le_neg (abs_eval_le_atomSup phi x)).trans (neg_abs_le _)
  linarith

theorem atomSup_center_eq_radius (phi : FracAtom n) :
    atomSup (center phi) = radius phi := by
  apply le_antisymm (atomSup_center_le_radius phi)
  simpa only [rangeMax_center] using rangeMax_le_atomSup (center phi)

/-- The interval sum budget after optimally transferring constants to the bias. -/
def intervalBudget (phi : Fin H → FracAtom n) (c : ℝ) : ℝ :=
  max (c + ∑ h, rangeMax (phi h)) (-c - ∑ h, rangeMin (phi h))

theorem intervalBudget_le_amplitude (phi : Fin H → FracAtom n) (c : ℝ) :
    intervalBudget phi c ≤ amplitude phi c := by
  unfold intervalBudget amplitude
  apply max_le
  · exact add_le_add (le_abs_self c)
      (Finset.sum_le_sum fun h _ => rangeMax_le_atomSup (phi h))
  · calc
      -c - ∑ h, rangeMin (phi h) = -c + ∑ h, -rangeMin (phi h) := by
        rw [Finset.sum_neg_distrib]
        ring
      _ ≤ |c| + ∑ h, atomSup (phi h) :=
        add_le_add (neg_le_abs c)
          (Finset.sum_le_sum fun h _ => neg_rangeMin_le_atomSup (phi h))

theorem centered_amplitude_eq_intervalBudget (phi : Fin H → FracAtom n) (c : ℝ) :
    amplitude (centeredHeads phi) (centeredBias phi c) = intervalBudget phi c := by
  unfold amplitude centeredHeads centeredBias intervalBudget
  simp_rw [atomSup_center_eq_radius]
  have hsum : (∑ h, midrange (phi h)) =
      ((∑ h, rangeMin (phi h)) + (∑ h, rangeMax (phi h)))/2 := by
    simp only [midrange]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hrad : (∑ h, radius (phi h)) =
      ((∑ h, rangeMax (phi h)) - (∑ h, rangeMin (phi h)))/2 := by
    simp only [radius]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsum, hrad]
  by_cases hc : 0 ≤ c + ((∑ h, rangeMin (phi h)) + (∑ h, rangeMax (phi h)))/2
  · rw [abs_of_nonneg hc, max_eq_left (by linarith)]
    ring
  · rw [abs_of_neg (lt_of_not_ge hc), max_eq_right (by linarith)]
    ring

/-- The centered amplitude is no larger than that of any redistribution of
constants among the original heads and their free bias. -/
theorem optimal_constant_redistribution (phi : Fin H → FracAtom n) (c : ℝ)
    (t : Fin H → ℝ) :
    intervalBudget phi c ≤ amplitude (fun h => subtractConstant (phi h) (t h))
      (c + ∑ h, t h) := by
  have hupper (h : Fin H) : rangeMax (phi h)-t h ≤
      atomSup (subtractConstant (phi h) (t h)) := by
    have hh : rangeMax (phi h) ≤ atomSup (subtractConstant (phi h) (t h))+t h := by
      apply Finset.sup'_le
      intro x _
      have hx := (le_abs_self ((subtractConstant (phi h) (t h)).eval x)).trans
        (abs_eval_le_atomSup (subtractConstant (phi h) (t h)) x)
      rw [subtractConstant_eval] at hx
      linarith
    linarith
  have hlower (h : Fin H) : t h-rangeMin (phi h) ≤
      atomSup (subtractConstant (phi h) (t h)) := by
    have hh : t h-atomSup (subtractConstant (phi h) (t h)) ≤ rangeMin (phi h) := by
      apply Finset.le_inf'
      intro x _
      have hx := (neg_abs_le ((subtractConstant (phi h) (t h)).eval x))
      have hy := abs_eval_le_atomSup (subtractConstant (phi h) (t h)) x
      rw [subtractConstant_eval] at hx hy
      linarith
    linarith
  unfold intervalBudget amplitude
  apply max_le
  · have h₁ := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hupper h)
    have h₂ := le_abs_self (c+∑ h, t h)
    rw [Finset.sum_sub_distrib] at h₁
    linarith
  · have h₁ := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hlower h)
    have h₂ := neg_le_abs (c+∑ h, t h)
    rw [Finset.sum_sub_distrib] at h₁
    linarith

/-- At an upper-extremum smooth norm branch, the two stationarity equations
imply a signed moment identity for nonnegative head gaps. -/
theorem stationary_gap_identity {ι : Type*} [Fintype ι]
    (mu q z invB : ι → ℝ) (u v : ℝ)
    (hnum : (∑ x, mu x*z x*invB x) = v)
    (hden : (∑ x, mu x*q x*z x*invB x) = u*v) :
    (∑ x, mu x*(u-q x)*z x*invB x) = 0 := by
  calc
    (∑ x, mu x*(u-q x)*z x*invB x) =
        u*(∑ x, mu x*z x*invB x) - ∑ x, mu x*q x*z x*invB x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intros
      ring
    _ = 0 := by rw [hnum,hden]; ring

/-- A necessary elementary condition for a quadratic form with an unrestricted
mixed direction to be nonnegative. -/
theorem coefficient_eq_zero_of_all_nonneg (c d : ℝ)
    (h : ∀ t : ℝ, 0 ≤ c+t*d) : d = 0 := by
  by_contra hd
  have hh := h (-(c+1)/d)
  have he : c+(-(c+1)/d)*d = -1 := by
    field_simp
    ring
  rw [he] at hh
  norm_num at hh

/-- The algebraic consequence of the head-duplication second-order test.
The analytic local-minimum/LICQ hypothesis is deliberately not hidden here:
`hsecond` is the precise nonnegative mixed-direction condition it must supply. -/
theorem split_second_moment {ι κ : Type*} [Fintype ι]
    (Z : ι → κ → ℝ) (B mu gap : ι → ℝ) (p : ι)
    (hB : ∀ x, B x ≠ 0)
    (hnum : ∀ j, (∑ x, mu x*Z x j/B x) = Z p j/B p)
    (hsecond : ∀ (i j : κ) (t : ℝ), 0 ≤
      (∑ x, mu x*gap x*(Z x j)^2/(B x)^2) +
      t*(∑ x, mu x*(Z x i-Z p i/B p*B x)*Z x j/(B x)^2)) :
    ∀ i j, (∑ x, mu x*Z x i*Z x j/(B x)^2) =
      Z p i*Z p j/(B p)^2 := by
  intro i j
  have hz := coefficient_eq_zero_of_all_nonneg _ _ (hsecond i j)
  have he : (∑ x, mu x*(Z x i-Z p i/B p*B x)*Z x j/(B x)^2) =
      (∑ x, mu x*Z x i*Z x j/(B x)^2) -
      (Z p i/B p)*(∑ x, mu x*Z x j/B x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    field_simp [hB x, hB p]
  rw [he, hnum] at hz
  have hh := sub_eq_zero.mp hz
  rw [hh]
  field_simp [hB p]

end HeadComplexity.FullCubeNormOptimization
