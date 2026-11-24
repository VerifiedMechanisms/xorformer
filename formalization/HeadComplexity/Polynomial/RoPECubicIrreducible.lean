import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Irreducibility of the three-head cleared cubic

The six essential affine coordinates of the separating family turn its
cleared polynomial into the cubic below. Twelve additional variables are
included explicitly, so no extension-of-scalars claim is hidden here.
-/

namespace HeadComplexity.RoPECubic

open MvPolynomial

abbrev Poly := MvPolynomial (Fin 18) ℝ

noncomputable def core : Poly :=
  X 3 * X 1 * X 2 + X 4 * X 0 * X 2 + X 5 * X 0 * X 1

private theorem not_mem_vars_mul (p q : Poly) (i : Fin 18)
    (hp : i ∉ p.vars) (hq : i ∉ q.vars) : i ∉ (p * q).vars := by
  intro h
  exact (Finset.mem_union.mp (vars_mul p q h)).elim hp hq

private theorem not_mem_vars_add (p q : Poly) (i : Fin 18)
    (hp : i ∉ p.vars) (hq : i ∉ q.vars) : i ∉ (p + q).vars := by
  intro h
  exact (Finset.mem_union.mp (vars_add_subset p q h)).elim hp hq

/-- The cleared cubic is irreducible, even in the full eighteen-variable
polynomial ring. -/
theorem core_irreducible : Irreducible core := by
  let f : Poly := X 0 * X 1
  let g : Poly := X 2 * (X 3 * X 1 + X 4 * X 0)
  have hcore : core = f * X 5 + g := by dsimp [core, f, g]; ring
  rw [hcore]
  apply irreducible_mul_X_add f g 5
  · exact mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)
  · exact not_mem_vars_mul _ _ _ (by simp) (by simp)
  · apply not_mem_vars_mul _ _ _ (by simp)
    apply not_mem_vars_add
    · exact not_mem_vars_mul _ _ _ (by simp) (by simp)
    · exact not_mem_vars_mul _ _ _ (by simp) (by simp)
  · have h0 : ¬(X 0 : Poly) ∣ g := by
      rintro ⟨r, hr⟩
      have he := congrArg (eval (fun i : Fin 18 ↦ if i = 0 then 0 else 1)) hr
      norm_num [g] at he
      exact (by decide : (2 : Fin 18) ≠ 0) (he (by decide))
    have h1 : ¬(X 1 : Poly) ∣ g := by
      rintro ⟨r, hr⟩
      have he := congrArg (eval (fun i : Fin 18 ↦ if i = 1 then 0 else 1)) hr
      norm_num [g] at he
      exact (by decide : (2 : Fin 18) ≠ 1) (he (by decide))
    have hp0 : IsRelPrime (X 0 : Poly) g :=
      (X_prime.irreducible).isRelPrime_iff_not_dvd.mpr h0
    have hp1 : IsRelPrime (X 1 : Poly) g :=
      (X_prime.irreducible).isRelPrime_iff_not_dvd.mpr h1
    exact hp0.mul_left hp1

theorem core_totalDegree : core.totalDegree = 3 := by
  have hterm (i j k : Fin 18) : IsHomogeneous (X i * X j * X k : Poly) 3 :=
    ((isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ j)).mul (isHomogeneous_X ℝ k)
  exact ((hterm 3 1 2).add (hterm 4 0 2) |>.add (hterm 5 0 1)).totalDegree
    core_irreducible.ne_zero

/-- Clearing powers of the two nonzero denominator coordinates does not
create a spurious factor of the irreducible cubic. -/
theorem core_dvd_of_cleared_power_dvd (Q : Poly) (k : ℕ)
    (h : core ∣ (X 0 * X 1 : Poly) ^ k * Q) : core ∣ Q := by
  have hp : Prime core := UniqueFactorizationMonoid.irreducible_iff_prime.mp core_irreducible
  have hn : ¬core ∣ (X 0 * X 1 : Poly) := by
    rintro ⟨r, hr⟩
    have he := congrArg (eval (fun i : Fin 18 ↦ if i.val < 3 then 1 else 0)) hr
    norm_num [core] at he
  exact (hp.dvd_mul.mp h).resolve_left (fun hk ↦ hn (hp.dvd_of_dvd_pow hk))

/-- A nonzero polynomial of degree at most three divisible by the source
cubic is a nonzero scalar multiple of it. -/
theorem scalar_multiple_of_core_dvd (Q : Poly) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ 3) (hdiv : core ∣ Q) :
    ∃ c : ℝ, c ≠ 0 ∧ Q = C c * core := by
  obtain ⟨R, rfl⟩ := hdiv
  have hR : R ≠ 0 := by intro hz; simp [hz] at hQ
  rw [totalDegree_mul_of_isDomain core_irreducible.ne_zero hR, core_totalDegree] at hdeg
  have hRdeg : R.totalDegree = 0 := by omega
  have hRc := totalDegree_eq_zero_iff_eq_C.mp hRdeg
  refine ⟨R.coeff 0, ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hRc
    exact hR hRc
  · rw [hRc, mul_comm]
    simp

/-- The local parameterization used in the divisibility argument annihilates
the cleared cubic exactly wherever the first two denominator coordinates are
nonzero. -/
theorem core_rational_zero (y₁ y₂ y₃ z₁ z₂ : ℝ)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    z₁ * y₂ * y₃ + z₂ * y₁ * y₃ +
      (-(y₃ * (z₁ * y₂ + z₂ * y₁)) / (y₁ * y₂)) * y₁ * y₂ = 0 := by
  field_simp
  ring

/-- Vanishing on a product of infinite coordinate sets forces a polynomial
to vanish identically. This applies to the open box after clearing the
denominators in the local parameterization. -/
theorem zero_of_vanishes_on_box (Q : Poly) (s : Fin 18 → Set ℝ)
    (hs : ∀ i, (s i).Infinite)
    (hQ : ∀ x ∈ Set.pi Set.univ s, eval x Q = 0) : Q = 0 := by
  apply MvPolynomial.funext_set s hs
  intro x hx
  simpa using hQ x hx

end HeadComplexity.RoPECubic
