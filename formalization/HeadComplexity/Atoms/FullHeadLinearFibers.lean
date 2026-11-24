import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! General odd-cycle kernel algebra and a finite full-head fiber certificate.
The inverse-function theorem and general family are proved in the writeup. -/
namespace HeadComplexity.FullHeadLinearFibers

theorem pair_kernel_factor (a b v w : ℝ) :
    (a*v+b*w)*(1+a+b)-(a*(1+a)*v+b*(1+b)*w) = a*b*(v+w) := by ring

theorem odd_triangle_zero (v₀ v₁ v₂ : ℝ)
    (h₁ : v₀+v₁=0) (h₂ : v₁+v₂=0) (h₃ : v₂+v₀=0) :
    v₀=0 ∧ v₁=0 ∧ v₂=0 := by constructor; linarith; constructor <;> linarith

theorem triangle_star_zero {ι : Type*} [DecidableEq ι]
    (v : ι → ℝ) (i₀ i₁ i₂ : ι)
    (h₁ : v i₀+v i₁=0) (h₂ : v i₁+v i₂=0) (h₃ : v i₂+v i₀=0)
    (he : ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → v i₀+v i=0) :
    ∀ i, v i=0 := by
  obtain ⟨hz₀, hz₁, hz₂⟩ := odd_triangle_zero _ _ _ h₁ h₂ h₃
  intro i
  by_cases h : i=i₀
  · simpa [h] using hz₀
  by_cases h' : i=i₁
  · simpa [h'] using hz₁
  by_cases h'' : i=i₂
  · simpa [h''] using hz₂
  have ht := he i h h' h''
  linarith

theorem selector_det (r s : ℝ) :
    Matrix.det (!![0, 2*r; (1/2:ℝ), 2*s]) = -r := by
  norm_num [Matrix.det_fin_two] <;> ring

def residueR : Fin 8 → ℚ := ![-8, 252, -2520, 11550, -27720, 36036, -24024, 6435]
def residueQ : Fin 7 → ℚ := ![28, -756, 6300, -23100, 41580, -36036, 12012]
def responseR (t : ℚ) := ∑ j, residueR j / (t+j.val+1)
def responseQ (t : ℚ) := ∑ j, residueQ j / (t+j.val+1)
def derivativeR (t : ℚ) := -∑ j, residueR j / (t+j.val+1)^2
theorem rational_roots : ∀ r : Fin 7, responseR (r.val+1)=0 ∧ responseQ (r.val+1)=1/2 := by decide +kernel
theorem rational_simple : ∀ r : Fin 7, derivativeR (r.val+1) ≠ 0 := by decide +kernel
def anchorJacobian : Matrix (Fin 7) (Fin 7) ℚ := ![![1, 0, 0, 0, 0, 0, 0], ![(1 / 2), (1 / 2), 0, 0, (-1 / 4), 0, 0], ![(1 / 3), 0, (1 / 3), 0, 0, (-1 / 9), 0], ![(1 / 5), 0, 0, (1 / 5), 0, 0, (-1 / 25)], ![(1 / 4), (1 / 4), (1 / 4), 0, (-1 / 16), (-1 / 16), 0], ![(1 / 7), 0, (1 / 7), (1 / 7), 0, (-1 / 49), (-1 / 49)], ![(1 / 6), (1 / 6), 0, (1 / 6), (-1 / 36), 0, (-1 / 36)]]
def anchorInverse : Matrix (Fin 7) (Fin 7) ℚ := ![![1, 0, 0, 0, 0, 0, 0], ![(5 / 16), (-3 / 2), (-27 / 16), (-25 / 16), 4, (-49 / 16), (9 / 2)], ![(3 / 8), -1, (-45 / 8), (25 / 8), 8, (49 / 8), -9], ![(-1 / 4), 2, (27 / 4), (-75 / 4), -16, (49 / 4), 18], ![(21 / 8), -7, (-27 / 8), (-25 / 8), 8, (-49 / 8), 9], ![(33 / 8), -3, (-207 / 8), (75 / 8), 24, (147 / 8), -27], ![(15 / 4), 10, (135 / 4), (-475 / 4), -80, (245 / 4), 90]]
theorem anchor_inverse_mul : anchorInverse*anchorJacobian=1 := by decide +kernel

theorem table_positive {d k : ℕ} (B : Fin d → ℝ) (t : Fin k → ℝ)
    (hB : ∀ j, 0 < B j) (ht : ∀ i, 0 < t i)
    (y : Fin d → ℝ) (x : Fin k → ℝ)
    (hy : ∀ j, 0 ≤ y j) (hx : ∀ i, 0 ≤ x i) :
    0 < (1+∑ i, x i)/(1+∑ j, B j*y j+∑ i, t i*x i) := by
  have h₁ : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ ↦ hx i
  have h₂ : 0 ≤ ∑ j, B j*y j := Finset.sum_nonneg fun j _ ↦ mul_nonneg (hB j).le (hy j)
  have h₃ : 0 ≤ ∑ i, t i*x i := Finset.sum_nonneg fun i _ ↦ mul_nonneg (ht i).le (hx i)
  exact div_pos (by linarith) (by linarith)

end HeadComplexity.FullHeadLinearFibers
