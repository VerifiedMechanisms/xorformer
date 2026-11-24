import Mathlib.Tactic

set_option linter.style.header false

/-! A fixed-direction denominator deformation can lose strict sign patterns.
This does not exclude deformations which change the denominator directions. -/

namespace HeadComplexity.HomotheticFlattening
open Finset

def bit (x : Fin 16) (i : Fin 4) : ℤ := (x.val / 2 ^ i.val) % 2

def slope (h : Fin 2) : Fin 4 → ℤ := if h = 0 then ![1, 1, 1, 1] else ![1, 2, 3, 4]

def value (h : Fin 2) (x : Fin 16) : ℤ := ∑ i, slope h i * bit x i

def labels : Fin 16 → ℤ := ![1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1]

def numerator : Fin 2 → Fin 4 → ℤ := ![![71, 117, -224, 401], ![-20, -259, 397, -1000]]

def originalScore (x : Fin 16) : ℚ :=
  10 + ∑ h : Fin 2, (∑ i : Fin 4, (numerator h i : ℚ) * bit x i) / (1 + value h x)

def limitRow (x : Fin 16) (j : Fin 9) : ℤ :=
  if h₀ : j.val = 0 then 1
  else if h₁ : j.val ≤ 4 then bit x ⟨j.val - 1, by omega⟩
  else bit x ⟨j.val - 5, by omega⟩ * (value 1 x - value 0 x)

def limitDual : Fin 16 → ℤ := ![1, 1, 3, 1, 3, 1, 1, 3, 5, 7, 5, 3, 1, 3, 3, 1]

def flatRow (x : Fin 16) (j : Fin 9) : ℚ :=
  if h₀ : j.val = 0 then 1
  else if h₁ : j.val ≤ 4 then (bit x ⟨j.val - 1, by omega⟩ : ℚ) / (100 + value 0 x)
  else (bit x ⟨j.val - 5, by omega⟩ : ℚ) / (100 + value 1 x)

def flatDual : Fin 16 → ℤ :=
  ![47535753, 47535753, 142736747, 47535753, 151161341, 47535753, 47535753, 148353143,
    273746053, 352830671, 207256959, 124143247, 47535753, 136436759, 137486757, 47535753]

def flatWeight (x : Fin 16) : ℤ :=
  flatDual x * (100 + value 0 x) * (100 + value 1 x)

theorem slopes_positive : ∀ h i, 0 < slope h i := by decide +kernel

theorem denominators_positive : ∀ h x, 0 < 1 + value h x := by decide +kernel

theorem original_strict_signs : ∀ x, 0 < (labels x : ℚ) * originalScore x := by
  decide +kernel

theorem limit_dual_positive : ∀ x, 0 < limitDual x := by decide +kernel

theorem limit_annihilation : ∀ j, ∑ x, limitDual x * labels x * limitRow x j = 0 := by
  decide +kernel

theorem flat_weight_positive : ∀ x, 0 < flatWeight x := by decide +kernel

theorem flat_annihilation : ∀ j, ∑ x, (flatWeight x : ℚ) * labels x * flatRow x j = 0 := by
  decide +kernel


def minorRow : Fin 9 → Fin 16 := ![0, 1, 2, 3, 4, 6, 8, 10, 12]

def limitMinor : Matrix (Fin 9) (Fin 9) ℚ :=
  Matrix.of (fun i j => (limitRow (minorRow i) j : ℚ))

def limitInverse : Matrix (Fin 9) (Fin 9) ℚ :=
  ![![(1), (0), (0), (0), (0), (0), (0), (0), (0)],
    ![(-1), (1), (0), (0), (0), (0), (0), (0), (0)],
    ![(-4/3), (0), (17/12), (0), (1/6), (-1/4), (1/12), (-1/6), (1/12)],
    ![(-5/3), (0), (1/3), (0), (7/3), (-1), (-1/3), (2/3), (-1/3)],
    ![(-1), (0), (-3/4), (0), (-3/2), (9/4), (13/4), (-3/2), (-3/4)],
    ![(1), (-1), (-1), (1), (0), (0), (0), (0), (0)],
    ![(1/3), (0), (-5/12), (0), (-1/6), (1/4), (-1/12), (1/6), (-1/12)],
    ![(1/3), (0), (-1/6), (0), (-2/3), (1/2), (1/6), (-1/3), (1/6)],
    ![(0), (0), (1/4), (0), (1/2), (-3/4), (-3/4), (1/2), (1/4)]]

theorem limit_inverse_mul : limitInverse * limitMinor = 1 := by decide +kernel

theorem positive_certificate_excludes {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] (R : ι → κ → ℝ) (y w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hz : ∀ j, ∑ i, w i * y i * R i j = 0)
    (a : κ → ℝ) : ¬ ∀ i, 0 < y i * ∑ j, a j * R i j := by
  intro hs
  have hp : 0 < ∑ i, w i * (y i * ∑ j, a j * R i j) :=
    sum_pos (fun i _ => mul_pos (hw i) (hs i)) univ_nonempty
  have he : ∑ i, w i * (y i * ∑ j, a j * R i j) = 0 := by
    simp_rw [mul_sum]
    rw [sum_comm]
    have ht (j : κ) : ∑ i, w i * (y i * (a j * R i j)) = 0 := by
      calc
        _ = a j * ∑ i, w i * y i * R i j := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [hz, mul_zero]
    simp_rw [ht]
    simp
  linarith

theorem no_flat_separator (a : Fin 9 → ℝ) :
    ¬ ∀ x, 0 < (labels x : ℝ) * ∑ j, a j * (flatRow x j : ℝ) := by
  apply positive_certificate_excludes (fun x j => (flatRow x j : ℝ))
    (fun x => (labels x : ℝ)) (fun x => (flatWeight x : ℝ)) _ _ a
  · intro x
    exact_mod_cast flat_weight_positive x
  · intro j
    exact_mod_cast flat_annihilation j

theorem no_limit_separator (a : Fin 9 → ℝ) :
    ¬ ∀ x, 0 < (labels x : ℝ) * ∑ j, a j * (limitRow x j : ℝ) := by
  apply positive_certificate_excludes (fun x j => (limitRow x j : ℝ))
    (fun x => (labels x : ℝ)) (fun x => (limitDual x : ℝ)) _ _ a
  · intro x
    exact_mod_cast limit_dual_positive x
  · intro j
    exact_mod_cast limit_annihilation j

end HeadComplexity.HomotheticFlattening
