import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 2048

/-! Positive reciprocal moment coordinates are injective on a full-rank
positive affine domain. The positivity of the observation weights is essential;
a full Boolean two-dimensional example has a noninjective signed gradient. -/

noncomputable section
namespace HeadComplexity.PositiveReciprocalGradient
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def evaluation (Z : ι → κ → ℝ) (b : κ → ℝ) (x : ι) : ℝ :=
  ∑ j, Z x j * b j

def gradient (Z : ι → κ → ℝ) (w : ι → ℝ) (b : κ → ℝ) (j : κ) : ℝ :=
  ∑ x, w x * Z x j / evaluation Z b x

/-- The monotonicity identity behind positive reciprocal likelihood uniqueness. -/
theorem monotonicity_identity (Z : ι → κ → ℝ) (w : ι → ℝ) (b c : κ → ℝ)
    (hb : ∀ x, evaluation Z b x ≠ 0) (hc : ∀ x, evaluation Z c x ≠ 0) :
    (∑ j, (b j-c j) * (gradient Z w b j-gradient Z w c j)) =
      -(∑ x, w x * (evaluation Z b x-evaluation Z c x)^2 /
        (evaluation Z b x * evaluation Z c x)) := by
  simp only [gradient, ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_sub]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hs : ∑ j, (b j-c j)*Z x j = evaluation Z b x-evaluation Z c x := by
    simp only [evaluation, sub_mul, Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  calc
    (∑ j, ((b j-c j)*(w x*Z x j/evaluation Z b x)-
        (b j-c j)*(w x*Z x j/evaluation Z c x))) =
        w x * (∑ j, (b j-c j)*Z x j) *
          (1/evaluation Z b x-1/evaluation Z c x) := by
      simp only [Finset.sum_sub_distrib]
      simp_rw [show ∀ j, (b j-c j)*(w x*Z x j/evaluation Z b x) =
        w x*((b j-c j)*Z x j)/evaluation Z b x by intro j; ring]
      simp_rw [show ∀ j, (b j-c j)*(w x*Z x j/evaluation Z c x) =
        w x*((b j-c j)*Z x j)/evaluation Z c x by intro j; ring]
      rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
      ring
    _ = -(w x*(evaluation Z b x-evaluation Z c x)^2/
        (evaluation Z b x*evaluation Z c x)) := by
      rw [hs]
      field_simp [hb x, hc x]
      ring

/-- Positive weights force equal evaluation vectors from equal reciprocal moments. -/
theorem evaluation_eq_of_gradient_eq (Z : ι → κ → ℝ) (w : ι → ℝ)
    (hw : ∀ x, 0 < w x) (b c : κ → ℝ)
    (hb : ∀ x, 0 < evaluation Z b x) (hc : ∀ x, 0 < evaluation Z c x)
    (h : gradient Z w b = gradient Z w c) :
    ∀ x, evaluation Z b x = evaluation Z c x := by
  have hid := monotonicity_identity Z w b c (fun x ↦ (hb x).ne') (fun x ↦ (hc x).ne')
  rw [h] at hid
  simp only [sub_self, mul_zero, Finset.sum_const_zero, zero_eq_neg] at hid
  have hnonneg : ∀ x, 0 ≤ w x*(evaluation Z b x-evaluation Z c x)^2/
      (evaluation Z b x*evaluation Z c x) := by
    intro x
    exact div_nonneg (mul_nonneg (hw x).le (sq_nonneg _)) (mul_pos (hb x) (hc x)).le
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ ↦ hnonneg x)).mp hid
  intro x
  have hx := hz x (Finset.mem_univ x)
  have hx' : (evaluation Z b x-evaluation Z c x)^2 = 0 := by
    rcases (div_eq_zero_iff).mp hx with hn | hd
    · exact (mul_eq_zero.mp hn).resolve_left (hw x).ne'
    · exact False.elim ((mul_pos (hb x) (hc x)).ne' hd)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx')

theorem injective_gradient_on_positive_domain (Z : ι → κ → ℝ) (w : ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hinj : Function.Injective (fun b : κ → ℝ ↦ evaluation Z b))
    (b c : κ → ℝ) (hb : ∀ x, 0 < evaluation Z b x)
    (hc : ∀ x, 0 < evaluation Z c x) (h : gradient Z w b = gradient Z w c) : b = c := by
  apply hinj
  funext x
  exact evaluation_eq_of_gradient_eq Z w hw b c hb hc h x

namespace SignedCounterexample

def rows : Fin 4 → Fin 3 → ℝ := ![![1,0,0],![1,1,0],![1,0,1],![1,1,1]]
def weights : Fin 4 → ℝ := ![2,-6,-12,20]
def parameters : Fin 2 → Fin 3 → ℝ := ![![1,1,2],![2,1,2]]

theorem parameters_pos (k : Fin 2) (j : Fin 3) : 0 < parameters k j := by
  fin_cases k <;> fin_cases j <;> norm_num [parameters]

theorem evaluations_pos (k : Fin 2) (x : Fin 4) :
    0 < evaluation rows (parameters k) x := by
  fin_cases k <;> fin_cases x <;> norm_num [evaluation, rows, parameters, Fin.sum_univ_succ]

/-- Two different strictly positive denominator vectors have the same full
signed reciprocal gradient, using all four augmented Boolean rows. -/
theorem gradient_values (k : Fin 2) : gradient rows weights (parameters k) = ![0,2,1] := by
  ext j
  fin_cases k <;> fin_cases j <;>
    norm_num [gradient, evaluation, rows, weights, parameters, Fin.sum_univ_succ]

theorem parameters_ne : parameters 0 ≠ parameters 1 := by
  intro h
  have h0 := congrFun h 0
  norm_num [parameters] at h0

end SignedCounterexample
end HeadComplexity.PositiveReciprocalGradient
