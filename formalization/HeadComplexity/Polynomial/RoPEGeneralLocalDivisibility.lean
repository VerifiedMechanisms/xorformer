import HeadComplexity.Polynomial.RoPEGeneralIrreducible
import HeadComplexity.Polynomial.LinearSourceDivisibility

set_option linter.style.header false

/-!
# Local sign rigidity of the general-head source

For every positive head count, weak sign agreement near a regular zero of the
source forces polynomial divisibility. A degree bound then forces a scalar
multiple, or excludes a nonzero representative of smaller degree.
-/

namespace HeadComplexity.RoPEGeneralPolynomial

open MvPolynomial
open scoped Topology

theorem core_dvd_of_weak_sign_on_open {H K : ℕ} (hH : 0 < H) (i : Fin H)
    (Q : Poly H K) (Ω : Set (Var H K → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y (core H K) → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y (core H K) < 0 → eval y Q ≤ 0)
    (x : Var H K → ℝ) (hx : x ∈ Ω)
    (hzero : eval x (core H K) = 0) (hslope : eval x (omittedProduct H K i) ≠ 0) :
    core H K ∣ Q := by
  have hc : LinearSourceDivisibility.source (numeratorIndex i)
      (omittedProduct H K i) (remainder H K i) = core H K := (core_split H K i).symm
  have hp : Prime (core H K) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (core_irreducible H K hH)
  have hd := LinearSourceDivisibility.source_dvd_of_weak_sign_on_open
    (numeratorIndex i) (omittedProduct H K i) (remainder H K i) Q
    (numerator_not_mem_omittedProduct_vars H K i i)
    (numerator_not_mem_remainder_vars H K i)
    (by simpa only [hc] using hp)
    (by simpa only [hc] using core_not_dvd_omittedProduct H K i)
    Ω hΩ (by simpa only [hc] using hpos) (by simpa only [hc] using hneg)
    x hx (by simpa only [hc] using hzero) hslope
  simpa only [hc] using hd

theorem scalar_multiple_of_weak_sign_on_open {H K : ℕ} (hH : 0 < H) (i : Fin H)
    (Q : Poly H K) (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ H)
    (Ω : Set (Var H K → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y (core H K) → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y (core H K) < 0 → eval y Q ≤ 0)
    (x : Var H K → ℝ) (hx : x ∈ Ω)
    (hzero : eval x (core H K) = 0) (hslope : eval x (omittedProduct H K i) ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ Q = C c * core H K :=
  scalar_multiple_of_core_dvd hH Q hQ hdeg
    (core_dvd_of_weak_sign_on_open hH i Q Ω hΩ hpos hneg x hx hzero hslope)

theorem positive_scalar_multiple_of_weak_sign_on_open {H K : ℕ}
    (hH : 0 < H) (i : Fin H) (Q : Poly H K) (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ H)
    (Ω : Set (Var H K → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y (core H K) → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y (core H K) < 0 → eval y Q ≤ 0)
    (x : Var H K → ℝ) (hx : x ∈ Ω)
    (hzero : eval x (core H K) = 0) (hslope : eval x (omittedProduct H K i) ≠ 0)
    (y : Var H K → ℝ) (hy : y ∈ Ω) (hPy : 0 < eval y (core H K)) :
    ∃ c : ℝ, 0 < c ∧ Q = C c * core H K := by
  apply SignLimitProportionality.positive_scalar_multiple_of_dvd_of_totalDegree_le
    (core H K) Q (core_irreducible H K hH).ne_zero hQ
  · simpa only [core_totalDegree H K hH] using hdeg
  · exact core_dvd_of_weak_sign_on_open hH i Q Ω hΩ hpos hneg x hx hzero hslope
  · exact hPy
  · exact hpos y hy hPy

theorem no_lower_degree_weak_sign_on_open {H K : ℕ} (hH : 0 < H) (i : Fin H)
    (Q : Poly H K) (hQ : Q ≠ 0) (hdeg : Q.totalDegree < H)
    (Ω : Set (Var H K → ℝ)) (hΩ : IsOpen Ω)
    (hpos : ∀ y ∈ Ω, 0 < eval y (core H K) → 0 ≤ eval y Q)
    (hneg : ∀ y ∈ Ω, eval y (core H K) < 0 → eval y Q ≤ 0)
    (x : Var H K → ℝ) (hx : x ∈ Ω)
    (hzero : eval x (core H K) = 0) (hslope : eval x (omittedProduct H K i) ≠ 0) : False := by
  obtain ⟨R, hR⟩ := core_dvd_of_weak_sign_on_open hH i Q Ω hΩ hpos hneg x hx hzero hslope
  have hRne : R ≠ 0 := by intro he; rw [he, mul_zero] at hR; exact hQ hR
  rw [hR, totalDegree_mul_of_isDomain (core_irreducible H K hH).ne_zero hRne,
    core_totalDegree H K hH] at hdeg
  omega

end HeadComplexity.RoPEGeneralPolynomial
