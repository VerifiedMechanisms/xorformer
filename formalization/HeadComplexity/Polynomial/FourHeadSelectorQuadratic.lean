import HeadComplexity.Results.PureRoPEThreeHeadObstruction

set_option linter.style.header false

/-!
# A selector projection of four cleared affine fractions

The odd part in one selector coordinate, followed by the even part in all
remaining coordinates, is a quadratic sum of four products. The right factors
are the original denominator directions. No symmetry of the classifier is
assumed in this algebraic identity.
-/

namespace HeadComplexity.FourHeadSelectorQuadratic

noncomputable section

open Finset
open scoped BigOperators

def cleared (c : ℝ) (N D : Fin 4 → ℝ) : ℝ :=
  c * D 0 * D 1 * D 2 * D 3 + N 0 * D 1 * D 2 * D 3 +
    N 1 * D 0 * D 2 * D 3 + N 2 * D 0 * D 1 * D 3 + N 3 * D 0 * D 1 * D 2

theorem cleared_eq (c : ℝ) (N D : Fin 4 → ℝ) (hD : ∀ h, D h ≠ 0) :
    cleared c N D = (D 0 * D 1 * D 2 * D 3) * (c + ∑ h, N h / D h) := by
  have h0 := hD 0
  have h1 := hD 1
  have h2 := hD 2
  have h3 := hD 3
  simp [cleared, Fin.sum_univ_succ]
  field_simp
  ring

def extracted (c : ℝ) (d e n a U B : Fin 4 → ℝ) : ℝ :=
  (cleared c (fun h ↦ n h + a h + U h) (fun h ↦ d h + e h + B h) -
    cleared c (fun h ↦ n h - a h + U h) (fun h ↦ d h - e h + B h) +
    cleared c (fun h ↦ n h + a h - U h) (fun h ↦ d h + e h - B h) -
    cleared c (fun h ↦ n h - a h - U h) (fun h ↦ d h - e h - B h)) / 4

def mixed (d e : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, e 2 * d 3 + e 3 * d 2, e 1 * d 3 + e 3 * d 1, e 1 * d 2 + e 2 * d 1],
    ![e 2 * d 3 + e 3 * d 2, 0, e 0 * d 3 + e 3 * d 0, e 0 * d 2 + e 2 * d 0],
    ![e 1 * d 3 + e 3 * d 1, e 0 * d 3 + e 3 * d 0, 0, e 0 * d 1 + e 1 * d 0],
    ![e 1 * d 2 + e 2 * d 1, e 0 * d 2 + e 2 * d 0, e 0 * d 1 + e 1 * d 0, 0]]

def pair (c : ℝ) (d e n a : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  c * mixed d e i j + mixed d a i j + mixed n e i j

def firstFactor (c : ℝ) (d e n a U B : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  (∑ i, mixed d e i j * U i) + (∑ i, pair c d e n a i j * B i) / 2

set_option maxHeartbeats 3000000 in
-- Normalize the complete quartic identity before its selector projection.
theorem extracted_eq (c : ℝ) (d e n a U B : Fin 4 → ℝ) :
    extracted c d e n a U B = extracted c d e n a 0 0 +
      ∑ j, firstFactor c d e n a U B j * B j := by
  simp [extracted, cleared, firstFactor, pair, mixed, Fin.sum_univ_succ]
  ring

open PureRoPEThreeHead in
theorem firstFactor_linear {N : ℕ} (c : ℝ) (d e n a : Fin 4 → ℝ)
    (U B : Fin 4 → Fin N → ℝ) (x : Fin N → Bool) (j : Fin 4) :
    firstFactor c d e n a (fun h ↦ linear (U h) x) (fun h ↦ linear (B h) x) j =
      linear (fun k ↦ firstFactor c d e n a (fun h ↦ U h k) (fun h ↦ B h k) j) x := by
  simp only [firstFactor, linear, add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i k ↦ mixed d e i j * (U i k * spin (x k))),
    Finset.sum_comm (f := fun i k ↦ pair c d e n a i j * (B i k * spin (x k)) / 2)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;>
    apply Finset.sum_congr rfl <;> intro i _ <;> ring

end

end HeadComplexity.FourHeadSelectorQuadratic
