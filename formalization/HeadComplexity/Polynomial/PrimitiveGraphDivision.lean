import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing

set_option linter.style.header false

/-!
# Primitive linear graph equations divide every polynomial vanishing on the graph

This is the exact algebraic division step used after zero-chart interpolation.
The graph value lies in the fraction field of the coefficient ring. Primitivity
ensures that the quotient descends to the polynomial ring itself.
-/

namespace HeadComplexity.PrimitiveGraphDivision

noncomputable section

open Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Nonempty (NormalizedGCDMonoid R)]

theorem primitive_dvd_of_map_dvd {p q : Polynomial R} (hp : p.IsPrimitive)
    (h : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  obtain ⟨g, hg⟩ := h
  have hm : p.map (algebraMap R K) * g ∈ Polynomial.lifts (algebraMap R K) := by
    rw [← hg]
    exact ⟨q, rfl⟩
  obtain ⟨g', hg'⟩ := (Polynomial.mem_lifts g).mp (hp.map_mul_mem_lifts_iff.mp hm)
  refine ⟨g', ?_⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [Polynomial.map_mul, hg']
  exact hg

omit [IsDomain R] [Nonempty (NormalizedGCDMonoid R)] in
theorem linear_primitive {a b : R} (hab : IsRelPrime a b) :
    (C a * X + C b : Polynomial R).IsPrimitive := by
  intro r hr
  have hc := (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr
  exact hab (by simpa using hc 1) (by simpa using hc 0)

/-- Vanishing identically on a primitive rational linear graph implies divisibility. -/
theorem primitive_linear_dvd_of_graph_zero {a b : R} (ha : a ≠ 0)
    (hp : (C a * X + C b : Polynomial R).IsPrimitive)
    (q : Polynomial R)
    (hq : (q.map (algebraMap R K)).eval
      (-(algebraMap R K b) / algebraMap R K a) = 0) :
    (C a * X + C b : Polynomial R) ∣ q := by
  let A : K := algebraMap R K a
  let B : K := algebraMap R K b
  have hA : A ≠ 0 := fun h ↦ ha ((IsFractionRing.injective R K) (by simpa [A] using h))
  have hroot : (X - C (-B / A) : Polynomial K) ∣ q.map (algebraMap R K) :=
    Polynomial.dvd_iff_isRoot.mpr hq
  have hunit : IsUnit (C A : Polynomial K) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hA)
  have hfactor : (C a * X + C b : Polynomial R).map (algebraMap R K) =
      C A * (X - C (-B / A)) := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change C A * X + C B = C A * (X - C (-B / A))
    rw [mul_sub, ← C_mul]
    have he : A * (-B / A) = -B := by field_simp
    rw [he, C_neg]
    ring
  apply primitive_dvd_of_map_dvd (K := K) hp
  rw [hfactor]
  exact hunit.mul_left_dvd.mpr hroot


theorem linear_dvd_of_graph_zero {a b : R} (ha : a ≠ 0) (hab : IsRelPrime a b)
    (q : Polynomial R)
    (hq : (q.map (algebraMap R K)).eval
      (-(algebraMap R K b) / algebraMap R K a) = 0) :
    (C a * X + C b : Polynomial R) ∣ q :=
  primitive_linear_dvd_of_graph_zero ha (linear_primitive hab) q hq

end

end HeadComplexity.PrimitiveGraphDivision
