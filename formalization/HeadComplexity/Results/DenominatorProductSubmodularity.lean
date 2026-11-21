import HeadComplexity.Atoms.ClearedNormalForm
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open Finset MvPolynomial Head
open scoped BigOperators

variable {n H : ℕ}

namespace FracAtom

private theorem denPoly_eval_square (phi : FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    MvPolynomial.eval (cubePoint (restrictBits base i j (a, b))) phi.denPoly =
      MvPolynomial.eval (cubePoint (restrictBits base i j (false, false)))
        phi.denPoly + phi.ρ i * (phi.α - 1) * boolToReal a +
          phi.ρ j * (phi.α - 1) * boolToReal b := by
  classical
  rw [denPoly_eval, denPoly_eval]
  have hterm (k : Fin n) :
      phi.wt (restrictBits base i j (a, b)) k =
        phi.wt (restrictBits base i j (false, false)) k +
          (if k = i then phi.ρ i * (phi.α - 1) * boolToReal a else 0) +
          (if k = j then phi.ρ j * (phi.α - 1) * boolToReal b else 0) := by
    by_cases hki : k = i
    · subst k
      cases a <;> simp [wt, restrictBits, hij, boolToReal]; ring
    · by_cases hkj : k = j
      · subst k
        cases b <;> simp [wt, restrictBits, hki, boolToReal]; ring
      · simp [wt, restrictBits, hki, hkj]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp
  ring

/-- The multiplicative defect on a coordinate square is the product of the
two positive position weights and the square of the common token increment. -/
theorem denPoly_square_defect (phi : FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.eval (cubePoint (restrictBits base i j (true, false))) phi.denPoly *
        MvPolynomial.eval (cubePoint (restrictBits base i j (false, true))) phi.denPoly -
      MvPolynomial.eval (cubePoint (restrictBits base i j (false, false))) phi.denPoly *
        MvPolynomial.eval (cubePoint (restrictBits base i j (true, true))) phi.denPoly =
          phi.ρ i * phi.ρ j * (phi.α - 1) ^ 2 := by
  rw [denPoly_eval_square phi base i j hij true false,
    denPoly_eval_square phi base i j hij false true,
    denPoly_eval_square phi base i j hij true true]
  simp [boolToReal]
  ring

theorem denPoly_square_le (phi : FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.eval (cubePoint (restrictBits base i j (false, false))) phi.denPoly *
        MvPolynomial.eval (cubePoint (restrictBits base i j (true, true))) phi.denPoly ≤
      MvPolynomial.eval (cubePoint (restrictBits base i j (true, false))) phi.denPoly *
        MvPolynomial.eval (cubePoint (restrictBits base i j (false, true))) phi.denPoly := by
  have hdef := phi.denPoly_square_defect base i j hij
  have hpos : 0 ≤ phi.ρ i * phi.ρ j * (phi.α - 1) ^ 2 :=
    mul_nonneg (mul_pos (phi.hρ i) (phi.hρ j)).le (sq_nonneg _)
  linarith

theorem denPoly_square_lt (phi : FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (ha : phi.α ≠ 1) :
    MvPolynomial.eval (cubePoint (restrictBits base i j (false, false))) phi.denPoly *
        MvPolynomial.eval (cubePoint (restrictBits base i j (true, true))) phi.denPoly <
      MvPolynomial.eval (cubePoint (restrictBits base i j (true, false))) phi.denPoly *
        MvPolynomial.eval (cubePoint (restrictBits base i j (false, true))) phi.denPoly := by
  have hdef := phi.denPoly_square_defect base i j hij
  have hpos : 0 < phi.ρ i * phi.ρ j * (phi.α - 1) ^ 2 :=
    mul_pos (mul_pos (phi.hρ i) (phi.hρ j)) (sq_pos_of_ne_zero (sub_ne_zero.mpr ha))
  linarith

end FracAtom

/-- A product of native head denominators is log-submodular on every
coordinate square, even when the heads have different orientations. -/
theorem atomDenProduct_eval_square_le (phi : Fin H → FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.eval (cubePoint (restrictBits base i j (false, false))) (atomDenProduct phi) *
        MvPolynomial.eval (cubePoint (restrictBits base i j (true, true))) (atomDenProduct phi) ≤
      MvPolynomial.eval (cubePoint (restrictBits base i j (true, false))) (atomDenProduct phi) *
        MvPolynomial.eval (cubePoint (restrictBits base i j (false, true)))
          (atomDenProduct phi) := by
  simp only [atomDenProduct, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀
    (fun h _ ↦ (mul_pos ((phi h).denPoly_pos _) ((phi h).denPoly_pos _)).le)
    (fun h _ ↦ (phi h).denPoly_square_le base i j hij)

/-- One nonconstant native denominator makes the product inequality strict. -/
theorem atomDenProduct_eval_square_lt (phi : Fin H → FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j)
    (ha : ∃ h, (phi h).α ≠ 1) :
    MvPolynomial.eval (cubePoint (restrictBits base i j (false, false))) (atomDenProduct phi) *
        MvPolynomial.eval (cubePoint (restrictBits base i j (true, true))) (atomDenProduct phi) <
      MvPolynomial.eval (cubePoint (restrictBits base i j (true, false))) (atomDenProduct phi) *
        MvPolynomial.eval (cubePoint (restrictBits base i j (false, true)))
          (atomDenProduct phi) := by
  simp only [atomDenProduct, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_lt_prod₀
    (fun h _ ↦ mul_pos ((phi h).denPoly_pos _) ((phi h).denPoly_pos _))
    (fun h _ ↦ (phi h).denPoly_square_le base i j hij) ?_
  obtain ⟨h, hh⟩ := ha
  exact ⟨h, Finset.mem_univ h, (phi h).denPoly_square_lt base i j hij hh⟩

/-- Equality on even one square forces every denominator to be constant. -/
theorem atomDenProduct_square_eq_forces_alpha_one (phi : Fin H → FracAtom n)
    (base : Fin n → Bool) (i j : Fin n) (hij : i ≠ j)
    (heq :
      MvPolynomial.eval (cubePoint (restrictBits base i j (false, false))) (atomDenProduct phi) *
          MvPolynomial.eval (cubePoint (restrictBits base i j (true, true))) (atomDenProduct phi) =
        MvPolynomial.eval (cubePoint (restrictBits base i j (true, false))) (atomDenProduct phi) *
          MvPolynomial.eval (cubePoint (restrictBits base i j (false, true)))
            (atomDenProduct phi)) :
    ∀ h, (phi h).α = 1 := by
  intro h
  by_contra hh
  have hlt := atomDenProduct_eval_square_lt phi base i j hij ⟨h, hh⟩
  exact (ne_of_lt hlt) heq

/-- A constant positive denominator product cannot conceal nonconstant
factors in the manuscript's native one-layer model. -/
theorem atomDenProduct_constant_forces_alpha_one (phi : Fin H → FracAtom n)
    (hn : 2 ≤ n) (d : ℝ)
    (hd : ∀ bits, MvPolynomial.eval (cubePoint bits) (atomDenProduct phi) = d) :
    ∀ h, (phi h).α = 1 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  apply atomDenProduct_square_eq_forces_alpha_one phi (fun _ ↦ false) i j hij
  simp only [hd]

end HeadComplexity
