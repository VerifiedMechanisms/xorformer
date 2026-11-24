import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity.ThreeHeadCubicObstruction

noncomputable section
open MvPolynomial
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 3) ℝ

def linear (a : Fin 3 → ℝ) : Poly := ∑ i, C (a i) * X i

theorem linear_coefficient (a : Fin 3 → ℝ) (i : Fin 3) :
    coeff (Finsupp.single i 1) (linear a) = a i := by
  simp [linear, coeff_sum, coeff_C_mul, coeff_X,
    Finsupp.single_left_inj (by norm_num : (1 : ℕ) ≠ 0)]

theorem linear_constant (a : Fin 3 → ℝ) : constantCoeff (linear a) = 0 := by
  simp [linear]

theorem linear_degree_le (a : Fin 3 → ℝ) : (linear a).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_mul _ _).trans (by simp)

theorem linear_irreducible (a : Fin 3 → ℝ) (ha : linear a ≠ 0) :
    Irreducible (linear a) := by
  apply irreducible_of_totalDegree_eq_one
  · apply le_antisymm (linear_degree_le a)
    by_contra h
    have hd : (linear a).totalDegree = 0 := by omega
    have he := (totalDegree_eq_zero_iff_eq_C (p := linear a)).mp hd
    have hc := linear_constant a
    have hz : coeff 0 (linear a) = 0 := hc
    simp only [hz, map_zero] at he
    exact ha he
  · intro r hr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    subst r
    apply ha
    ext m
    simpa using hr m

theorem linear_divisor (a : Fin 3 → ℝ) (ha : linear a ≠ 0)
    (hd : linear a ∣ X 0 * X 1 * X 2) :
    ∃ i : Fin 3, ∃ c : ℝ, c ≠ 0 ∧ linear a = C c * X i := by
  have hp := (linear_irreducible a ha).prime
  have hi : ∃ i : Fin 3, linear a ∣ X i := by
    rcases hp.dvd_mul.mp hd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  obtain ⟨i, hi⟩ := hi
  have hass : Associated (X i : Poly) (linear a) :=
    ((MvPolynomial.X_prime.irreducible.dvd_iff).mp hi).resolve_left
      (linear_irreducible a ha).not_isUnit
  obtain ⟨u, hu⟩ := hass
  have hu0 : (u : Poly) ≠ 0 := Units.ne_zero u
  have hdeg : (u : Poly).totalDegree = 0 := by
    have hh := congrArg totalDegree hu
    rw [totalDegree_mul_of_isDomain (X_ne_zero i) hu0] at hh
    have hh' := linear_degree_le a
    simp only [totalDegree_X] at hh
    omega
  have hc := (totalDegree_eq_zero_iff_eq_C (p := (u : Poly))).mp hdeg
  refine ⟨i, coeff 0 (u : Poly), ?_, ?_⟩
  · intro hz
    rw [hc, hz, map_zero] at hu0
    exact hu0 rfl
  · rw [hc] at hu
    simpa [mul_comm] using hu.symm


def xyz : Poly := X 0 * X 1 * X 2

theorem xyz_ne_zero : xyz ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)) (X_ne_zero 2)

theorem square_not_dvd_xyz (i : Fin 3) : ¬ (X i : Poly)^2 ∣ xyz := by
  have he : xyz = monomial (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) 1 := by
    simp only [xyz, X, monomial_mul, one_mul]
  rw [X_pow_eq_monomial, he, monomial_one_dvd_monomial_one]
  intro h
  have hh := h i
  have hs : (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) i = 1 := by
    fin_cases i <;> norm_num [Finsupp.single_apply, Fin.ext_iff]
  rw [Finsupp.single_eq_same, hs] at hh
  omega

theorem distinct_factor_indices (a b : Fin 3 → ℝ) (i j : Fin 3) (r s : ℝ)
    (ha : linear a = C r * X i) (hb : linear b = C s * X j)
    (h : linear a * linear b ∣ xyz) : i ≠ j := by
  intro hij
  subst j
  apply square_not_dvd_xyz i
  obtain ⟨q, hq⟩ := h
  refine ⟨C r * C s * q, ?_⟩
  rw [hq, ha, hb]
  ring

/-- Three pairwise products of nonzero homogeneous linear forms cannot all
 divide the squarefree monomial if the three forms have a nontrivial triangle relation. -/
theorem triangle_factor_obstruction (a b c : Fin 3 → ℝ)
    (hab : linear a * linear b ∣ xyz)
    (hac : linear a * linear c ∣ xyz)
    (hbc : linear b * linear c ∣ xyz)
    (hrel : linear a + linear b = linear c) : False := by
  have ha : linear a ≠ 0 := by
    intro h; simp [h, xyz_ne_zero] at hab
  have hb : linear b ≠ 0 := by
    intro h; simp [h, xyz_ne_zero] at hab
  have hc : linear c ≠ 0 := by
    intro h; simp [h, xyz_ne_zero] at hac
  obtain ⟨i, r, hr, hi⟩ := linear_divisor a ha (dvd_trans (dvd_mul_right _ _) hab)
  obtain ⟨j, s, hs, hj⟩ := linear_divisor b hb (dvd_trans (dvd_mul_left _ _) hab)
  obtain ⟨k, t, ht, hk⟩ := linear_divisor c hc (dvd_trans (dvd_mul_left _ _) hac)
  have hij := distinct_factor_indices a b i j r s hi hj hab
  have hik := distinct_factor_indices a c i k r t hi hk hac
  have hjk := distinct_factor_indices b c j k s t hj hk hbc
  rw [hi, hj, hk] at hrel
  have hcoef := congrArg (coeff (Finsupp.single i 1)) hrel
  have hc0 : r = 0 := by
    simpa [coeff_add, coeff_C_mul, coeff_X,
      Finsupp.single_left_inj (by norm_num : (1 : ℕ) ≠ 0), Ne.symm hij, Ne.symm hik] using hcoef
  exact hr hc0

/-- Exact cubic obstruction at a common nonvanishing direction. The common
 coefficient of the extra variable has been normalized to one. Numerators may
 even be arbitrary polynomial-valued functions of that variable. -/
theorem no_three_denominator_identity (b : Fin 3 → Fin 3 → ℝ)
    (n : Fin 3 → Poly → Poly)
    (h : ∀ t : Poly,
      n 0 t * (t + linear (b 1)) * (t + linear (b 2)) +
      n 1 t * (t + linear (b 0)) * (t + linear (b 2)) +
      n 2 t * (t + linear (b 0)) * (t + linear (b 1)) = xyz) : False := by
  let a : Fin 3 → ℝ := fun i ↦ b 1 i - b 0 i
  let c : Fin 3 → ℝ := fun i ↦ b 2 i - b 1 i
  let d : Fin 3 → ℝ := fun i ↦ b 2 i - b 0 i
  have ha : linear a = linear (b 1) - linear (b 0) := by
    simp [a, linear, sub_mul, Finset.sum_sub_distrib]
  have hc : linear c = linear (b 2) - linear (b 1) := by
    simp [c, linear, sub_mul, Finset.sum_sub_distrib]
  have hd : linear d = linear (b 2) - linear (b 0) := by
    simp [d, linear, sub_mul, Finset.sum_sub_distrib]
  have h0 := h (-linear (b 0))
  have h1 := h (-linear (b 1))
  have h2 := h (-linear (b 2))
  simp only [neg_add_cancel, mul_zero, zero_mul, zero_add, add_zero] at h0 h1 h2
  apply triangle_factor_obstruction a c d
  · refine ⟨-n 1 (-linear (b 1)), ?_⟩
    rw [← h1, ha, hc]
    ring
  · refine ⟨n 0 (-linear (b 0)), ?_⟩
    rw [← h0, ha, hd]
    ring
  · refine ⟨n 2 (-linear (b 2)), ?_⟩
    rw [← h2, hc, hd]
    ring
  · rw [ha, hc, hd]
    ring

end
end HeadComplexity.ThreeHeadCubicObstruction
