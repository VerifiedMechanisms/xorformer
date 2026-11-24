import HeadComplexity.Research.FilteredMomentLift
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
The positive-grid filtered correction is a finite sum of genuine original
fractional atoms, including for fixed arbitrary affine numerators.  It is an
exact zero score under the projection-moment hypothesis.  This theorem does
not assert that adding the correction improves relative margin.
-/

noncomputable section
namespace HeadComplexity.PositiveGridGhostAtoms

open Finset FilteredMomentLift SimplexPolynomialInterpolation RadialMomentTransfer
open scoped BigOperators

variable {n : ℕ} {ι : Type*} [Fintype ι]

def extendInput (x : Fin n → Bool) : Option (Fin n) → Bool
  | none => true
  | some i => x i

theorem booleanProjection_extendInput (w : Option (Fin n) → ℝ) (x : Fin n → Bool) :
    booleanProjection w (extendInput x) =
      affineValue (w none) (fun i => w (some i)) x := by
  simp only [booleanProjection, Fintype.sum_option, extendInput, ite_true,
    affineValue]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases hxi : x i = true <;> simp [hxi, boolToReal]

theorem gridResidue_affineValue (r : ℕ) (v : Option (Fin n) → ℝ)
    (a : ι → ℝ) (u : ι → Fin n → ℝ) (w : ι → Option (Fin n) → ℝ)
    (β : Grid (σ := Option (Fin n)) r) (x : Fin n → Bool) :
    affineValue (gridResidue r v a w β)
      (fun i => gridResidue r v (fun h => u h i) w β) x =
      gridResidue r v (fun h => affineValue (a h) (u h) x) w β := by
  classical
  simp only [gridResidue, affineValue, add_mul, sum_add_distrib, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro i _
  ring

def ghostAtom (r : ℕ) (a : ι → ℝ) (u : ι → Fin n → ℝ)
    (w : ι → Option (Fin n) → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (β : Grid (σ := Option (Fin n)) r) : FracAtom n :=
  FracAtom.ofPositiveAffineRatio
    (gridResidue r (fun _ => 1) a w β)
    (fun i => gridResidue r (fun _ => 1) (fun h => u h i) w β)
    (b + ε * gridNode (fun _ => 1) β none)
    (fun i => ε * gridNode (fun _ => 1) β (some i))
    (add_pos hb (mul_pos hε (gridNode_positive r _ (fun _ => one_pos) β none)))
    (fun i => mul_pos hε (gridNode_positive r _ (fun _ => one_pos) β (some i)))

theorem ghostAtom_eval (r : ℕ) (a : ι → ℝ) (u : ι → Fin n → ℝ)
    (w : ι → Option (Fin n) → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (β : Grid (σ := Option (Fin n)) r) (x : Fin n → Bool) :
    (ghostAtom r a u w b ε hb hε β).eval x =
      gridResidue r (fun _ => 1) (fun h => affineValue (a h) (u h) x) w β /
        (b + ε * booleanProjection (gridNode (fun _ => 1) β) (extendInput x)) := by
  rw [ghostAtom, FracAtom.ofPositiveAffineRatio_eval, gridResidue_affineValue,
    booleanProjection_extendInput, affineValue_const_add, affineValue_smul]

/-- Fixed affine numerators need only satisfy the combined moment identities.
Every auxiliary head is admissible and the auxiliary score is exactly zero on
the full Boolean cube. -/
theorem sum_ghostAtoms_eq_zero (r : ℕ) (a : ι → ℝ) (u : ι → Fin n → ℝ)
    (w : ι → Option (Fin n) → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hz : ∀ x : Fin n → Bool, ∀ k ≤ r,
      moment (fun h => affineValue (a h) (u h) x)
        (fun h => booleanProjection (w h) (extendInput x)) k = 0)
    (x : Fin n → Bool) :
    ∑ β : Grid (σ := Option (Fin n)) r,
      (ghostAtom r a u w b ε hb hε β).eval x = 0 := by
  simp_rw [ghostAtom_eval, div_eq_mul_inv]
  exact gridResidue_is_exact_ghost r (fun _ => 1)
    (fun h => affineValue (a h) (u h) x) w (extendInput x) (hz x)
    (fun t => (b + ε * t)⁻¹)

theorem ghost_head_count (r : ℕ) :
    Fintype.card (Grid (σ := Option (Fin n)) r) = (n + 1 + r).choose r := by
  rw [card_grid]
  simp

end HeadComplexity.PositiveGridGhostAtoms
