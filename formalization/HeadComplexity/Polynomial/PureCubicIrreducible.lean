import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization

set_option linter.style.header false

/-!
# Irreducibility of the coordinate cubic used by the pure separation

The homogeneous six-variable cubic is primitive and linear in its first
numerator coordinate. Translating the denominator coordinates by one is an
algebra automorphism, so the actual affine-coordinate cubic is irreducible in
all fourteen variables, including the eight unused chart coordinates.
-/

namespace HeadComplexity.PureCubicIrreducible

noncomputable section

open MvPolynomial

def homogeneous : MvPolynomial (Fin 14) ℝ :=
  X 0 * X 4 * X 5 + X 1 * X 3 * X 5 + X 2 * X 3 * X 4

def remainder : MvPolynomial (Fin 14) ℝ :=
  X 1 * X 3 * X 5 + X 2 * X 3 * X 4

theorem first_not_dvd_remainder : ¬(X 4 : MvPolynomial (Fin 14) ℝ) ∣ remainder := by
  intro h
  let z : Fin 14 → ℝ := fun i ↦ if i = 1 ∨ i = 3 ∨ i = 5 then 1 else 0
  have hh := map_dvd (eval z) h
  norm_num [z, remainder, Fin.ext_iff] at hh

theorem second_not_dvd_remainder : ¬(X 5 : MvPolynomial (Fin 14) ℝ) ∣ remainder := by
  intro h
  let z : Fin 14 → ℝ := fun i ↦ if i = 2 ∨ i = 3 ∨ i = 4 then 1 else 0
  have hh := map_dvd (eval z) h
  norm_num [z, remainder, Fin.ext_iff] at hh

theorem coefficient_relPrime :
    IsRelPrime (X 4 * X 5 : MvPolynomial (Fin 14) ℝ) remainder := by
  have h₄ : IsRelPrime (X 4 : MvPolynomial (Fin 14) ℝ) remainder :=
    (MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd).mpr first_not_dvd_remainder
  have h₅ : IsRelPrime (X 5 : MvPolynomial (Fin 14) ℝ) remainder :=
    (MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd).mpr second_not_dvd_remainder
  exact h₄.mul_left h₅

private theorem variable_not_mem_product {α : Type*}
    (i : α) (p q : MvPolynomial α ℝ) (hp : i ∉ p.vars) (hq : i ∉ q.vars) :
    i ∉ (p * q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_mul p q h)).elim hp hq

private theorem variable_not_mem_sum {α : Type*}
    (i : α) (p q : MvPolynomial α ℝ) (hp : i ∉ p.vars) (hq : i ∉ q.vars) :
    i ∉ (p + q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_add_subset p q h)).elim hp hq

theorem homogeneous_irreducible : Irreducible homogeneous := by
  have h₄ : (0 : Fin 14) ∉ (X 4 : MvPolynomial (Fin 14) ℝ).vars := by simp
  have h₅ : (0 : Fin 14) ∉ (X 5 : MvPolynomial (Fin 14) ℝ).vars := by simp
  have h₁ : (0 : Fin 14) ∉ (X 1 : MvPolynomial (Fin 14) ℝ).vars := by simp
  have h₂ : (0 : Fin 14) ∉ (X 2 : MvPolynomial (Fin 14) ℝ).vars := by simp
  have h₃ : (0 : Fin 14) ∉ (X 3 : MvPolynomial (Fin 14) ℝ).vars := by simp
  have hf := variable_not_mem_product 0 (X 4) (X 5) h₄ h₅
  have hg : (0 : Fin 14) ∉ remainder.vars :=
    variable_not_mem_sum 0 _ _
      (variable_not_mem_product 0 _ _ (variable_not_mem_product 0 _ _ h₁ h₃) h₅)
      (variable_not_mem_product 0 _ _ (variable_not_mem_product 0 _ _ h₂ h₃) h₄)
  have hi := irreducible_mul_X_add (X 4 * X 5 : MvPolynomial (Fin 14) ℝ) remainder 0
    (mul_ne_zero (X_ne_zero 4) (X_ne_zero 5)) hf hg coefficient_relPrime
  have he : (X 4 * X 5 : MvPolynomial (Fin 14) ℝ) * X 0 + remainder = homogeneous := by
    simp only [remainder, homogeneous]
    ring
  rwa [he] at hi

def translate {α : Type*} (a : α → ℝ) :
    MvPolynomial α ℝ ≃ₐ[ℝ] MvPolynomial α ℝ :=
  AlgEquiv.ofAlgHom (aeval (fun i ↦ X i + C (a i)))
    (aeval (fun i ↦ X i - C (a i)))
    (by ext i; simp)
    (by ext i; simp)

theorem translate_X {α : Type*} (a : α → ℝ) (i : α) :
    translate a (X i) = X i + C (a i) := by
  change aeval (fun j ↦ X j + C (a j)) (X i) = _
  simp

def shift (i : Fin 14) : ℝ := if 3 ≤ i.val ∧ i.val < 6 then 1 else 0

def coordinatePolynomial : MvPolynomial (Fin 14) ℝ :=
  X 0 * (1 + X 4) * (1 + X 5) + X 1 * (1 + X 3) * (1 + X 5) +
    X 2 * (1 + X 3) * (1 + X 4)

theorem translate_homogeneous : translate shift homogeneous = coordinatePolynomial := by
  simp only [homogeneous, map_add, map_mul, translate_X, coordinatePolynomial]
  norm_num [shift]
  ring

/-- The exact fourteen-variable coordinate cubic in the rational zero chart is irreducible. -/
theorem coordinatePolynomial_irreducible : Irreducible coordinatePolynomial := by
  rw [← translate_homogeneous]
  exact homogeneous_irreducible.map (translate shift)

theorem coordinatePolynomial_prime : Prime coordinatePolynomial :=
  irreducible_iff_prime.mp coordinatePolynomial_irreducible


theorem coordinatePolynomial_top_coefficient : coordinatePolynomial.coeff
    (Finsupp.single 0 1 + Finsupp.single 4 1 + Finsupp.single 5 1) = 1 := by
  have hz (d e : Fin 14 →₀ ℕ) (hd : d 0 = 0) (he : e 0 = 1) : d ≠ e := by
    intro h
    have hh := congrArg (fun v : Fin 14 →₀ ℕ ↦ v 0) h
    omega
  have hf (d e : Fin 14 →₀ ℕ) (hd : d 4 = 0) (he : e 4 = 1) : d ≠ e := by
    intro h
    have hh := congrArg (fun v : Fin 14 →₀ ℕ ↦ v 4) h
    omega
  norm_num [coordinatePolynomial, add_mul, mul_add, X, monomial_mul, coeff_monomial,
    hz, hf, Finsupp.single_apply, Fin.ext_iff]

theorem coordinatePolynomial_degree : coordinatePolynomial.totalDegree = 3 := by
  have hlinear (i : Fin 14) : (1 + X i : MvPolynomial (Fin 14) ℝ).totalDegree ≤ 1 := by
    simpa using totalDegree_add (1 : MvPolynomial (Fin 14) ℝ) (X i)
  have hterm (i j k : Fin 14) :
      (X i * (1 + X j) * (1 + X k) : MvPolynomial (Fin 14) ℝ).totalDegree ≤ 3 := by
    have h₁ := totalDegree_mul (X i : MvPolynomial (Fin 14) ℝ) (1 + X j)
    have h₂ := totalDegree_mul (X i * (1 + X j) : MvPolynomial (Fin 14) ℝ) (1 + X k)
    have hj := hlinear j
    have hk := hlinear k
    simp only [totalDegree_X] at h₁
    omega
  have hu : coordinatePolynomial.totalDegree ≤ 3 := by
    have h₁ := totalDegree_add (X 0 * (1 + X 4) * (1 + X 5) : MvPolynomial (Fin 14) ℝ)
      (X 1 * (1 + X 3) * (1 + X 5))
    have h₂ := totalDegree_add
      (X 0 * (1 + X 4) * (1 + X 5) + X 1 * (1 + X 3) * (1 + X 5) :
        MvPolynomial (Fin 14) ℝ) (X 2 * (1 + X 3) * (1 + X 4))
    have ha := hterm 0 4 5
    have hb := hterm 1 3 5
    have hc := hterm 2 3 4
    unfold coordinatePolynomial
    omega
  have hl : 3 ≤ coordinatePolynomial.totalDegree := by
    have hh := le_totalDegree (MvPolynomial.mem_support_iff.mpr
      (show coordinatePolynomial.coeff
        (Finsupp.single 0 1 + Finsupp.single 4 1 + Finsupp.single 5 1) ≠ 0 by
          rw [coordinatePolynomial_top_coefficient]; norm_num))
    simp only [Finsupp.sum_add_index' (h := fun (_ : Fin 14) (e : ℕ) ↦ e)
      (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
      Finsupp.sum_single_index (h := fun (_ : Fin 14) (e : ℕ) ↦ e) (by rfl)] at hh
    norm_num at hh
    exact hh
  omega

/-- Once graph vanishing gives divisibility, the degree bound forces a scalar multiple. -/
theorem eq_scalar_mul_of_dvd (Q : MvPolynomial (Fin 14) ℝ)
    (hQ : Q.totalDegree ≤ 3) (hdiv : coordinatePolynomial ∣ Q) :
    ∃ c : ℝ, Q = C c * coordinatePolynomial := by
  obtain ⟨T, rfl⟩ := hdiv
  by_cases ht : T = 0
  · exact ⟨0, by simp [ht]⟩
  · have hdeg := totalDegree_mul_of_isDomain coordinatePolynomial_prime.ne_zero ht
    rw [coordinatePolynomial_degree] at hdeg
    have htdeg : T.totalDegree = 0 := by omega
    have he := totalDegree_eq_zero_iff_eq_C.mp htdeg
    exact ⟨T.coeff 0, by conv_lhs => rw [he]; rw [mul_comm]⟩

end

end HeadComplexity.PureCubicIrreducible
