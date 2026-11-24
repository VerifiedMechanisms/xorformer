import Mathlib.LinearAlgebra.Lagrange
import HeadComplexity.Atoms.PartialFraction

set_option linter.style.header false

/-! Exact finite decoding by exterior Cauchy kernels. The poles and tokens may
be placed in arbitrarily small disjoint intervals. This is a scalar ingredient
of the affine-plane compiler, not by itself a head-complexity saving. -/

namespace HeadComplexity

open Finset Polynomial
open scoped BigOperators

/-- Arbitrary values at finitely many tokens are a constant plus a linear
combination of exterior reciprocal kernels with prescribed distinct poles. -/
theorem exists_cauchy_grid_decoder {q : ℕ} (pole token : Fin q → ℝ)
    (hpole : Function.Injective pole) (htoken : Function.Injective token)
    (hsep : ∀ i j, token j < pole i) (target : Fin q → ℝ) :
    ∃ (c : ℝ) (η : Fin q → ℝ), ∀ j,
      c + ∑ i, η i / (pole i - token j) = target j := by
  classical
  let nodes : Fin q → ℝ := fun j ↦ -token j
  let denom : ℝ → ℝ := fun t ↦ ∏ i, (t + pole i)
  let values : Fin q → ℝ := fun j ↦ target j * denom (nodes j)
  let P : ℝ[X] := Lagrange.interpolate Finset.univ nodes values
  have hnodes : Function.Injective nodes := fun i j h ↦ htoken (neg_injective h)
  have hPdeg : P.natDegree ≤ q := by
    apply Polynomial.natDegree_le_iff_degree_le.mpr
    have h := Lagrange.degree_interpolate_le
      (s := (Finset.univ : Finset (Fin q))) (r := values) hnodes.injOn
    exact h.trans (by simp only [Finset.card_univ, Fintype.card_fin]; exact_mod_cast Nat.sub_le q 1)
  have hPeval (j : Fin q) : P.eval (nodes j) = values j := by
    exact Lagrange.eval_interpolate_at_node values hnodes.injOn (Finset.mem_univ j)
  obtain ⟨c, η, hpartial⟩ := real_partial_fraction P pole hpole hPdeg
  refine ⟨c, η, fun j ↦ ?_⟩
  have hpos (i : Fin q) : 0 < nodes j + pole i := by
    dsimp [nodes]
    linarith [hsep i j]
  have hprodne : denom (nodes j) ≠ 0 := by
    exact (Finset.prod_pos (fun i _ ↦ hpos i)).ne'
  have herase (i : Fin q) :
      (∏ k ∈ Finset.univ.erase i, (nodes j + pole k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ (hpos k).ne'
  have hfactor (i : Fin q) :
      denom (nodes j) = (nodes j + pole i) *
        ∏ k ∈ Finset.univ.erase i, (nodes j + pole k) :=
    (Finset.mul_prod_erase Finset.univ (fun k ↦ nodes j + pole k)
      (Finset.mem_univ i)).symm
  have hsum : (∑ i, η i / (nodes j + pole i)) =
      (∑ i, η i * ∏ k ∈ Finset.univ.erase i, (nodes j + pole k)) /
        denom (nodes j) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [hfactor i, mul_div_mul_right _ _ (herase i)]
  have hratio : c + ∑ i, η i / (nodes j + pole i) =
      P.eval (nodes j) / denom (nodes j) := by
    rw [hsum, hpartial (nodes j)]
    field_simp
    ring
  have hresult : c + ∑ i, η i / (nodes j + pole i) = target j := by
    rw [hratio, hPeval]
    dsimp [values]
    field_simp [hprodne]
  simpa [nodes, sub_eq_add_neg, add_comm] using hresult

/-- Distinct tokens in an arbitrarily small positive interval. -/
noncomputable def compactCauchyToken {q : ℕ} (ε : ℝ) (i : Fin q) : ℝ :=
  ε * ((i : ℝ) + 1) / ((q : ℝ) + 1)

/-- Distinct exterior poles in an arbitrarily small interval below one. -/
noncomputable def compactCauchyPole {q : ℕ} (ε : ℝ) (i : Fin q) : ℝ :=
  1 - compactCauchyToken ε i

theorem compactCauchyToken_pos {q : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin q) :
    0 < compactCauchyToken ε i := by
  dsimp [compactCauchyToken]
  positivity

theorem compactCauchyToken_lt {q : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin q) :
    compactCauchyToken ε i < ε := by
  have hi : (i : ℝ) < q := by exact_mod_cast i.isLt
  dsimp [compactCauchyToken]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) + 1)).mpr
  nlinarith

theorem compactCauchyToken_injective {q : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (compactCauchyToken (q := q) ε) := by
  intro i j hij
  have hden : (q : ℝ) + 1 ≠ 0 := by positivity
  dsimp [compactCauchyToken] at hij
  have hmul := (div_left_inj' hden).mp hij
  have hcast : (i : ℝ) = (j : ℝ) := by nlinarith
  exact Fin.ext (Nat.cast_inj.mp hcast)

theorem compactCauchyPole_bounds {q : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin q) :
    1 - ε < compactCauchyPole ε i ∧ compactCauchyPole ε i < 1 := by
  dsimp [compactCauchyPole]
  constructor <;> linarith [compactCauchyToken_pos hε i, compactCauchyToken_lt hε i]

theorem compactCauchyPole_injective {q : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (compactCauchyPole (q := q) ε) := by
  intro i j hij
  apply compactCauchyToken_injective hε
  dsimp [compactCauchyPole] at hij
  linarith

theorem compactCauchy_separated {q : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2) (i j : Fin q) :
    compactCauchyToken ε j < compactCauchyPole ε i := by
  have hp := (compactCauchyPole_bounds hε i).1
  have ht := compactCauchyToken_lt hε j
  linarith

/-- Every finite target has an exact decoder with the same compact poles and
tokens; only its scalar coefficients and constant change. -/
theorem exists_compact_cauchy_grid_decoder {q : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2) (target : Fin q → ℝ) :
    ∃ (c : ℝ) (η : Fin q → ℝ), ∀ j,
      c + ∑ i, η i / (compactCauchyPole ε i - compactCauchyToken ε j) = target j :=
  exists_cauchy_grid_decoder (compactCauchyPole ε) (compactCauchyToken ε)
    (compactCauchyPole_injective hε) (compactCauchyToken_injective hε)
    (compactCauchy_separated hε hsmall) target

end HeadComplexity
