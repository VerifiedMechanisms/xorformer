import HeadComplexity.Results.AffineZeroSetInterpolation

set_option linter.style.header false

/-! # Open cube-neighborhood covers compile to fixed-denominator interpolation -/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- Flip exactly one coordinate of a Boolean cube point. -/
def cubeFlip (v : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update v i (!(v i))

@[simp] theorem cubeFlip_cubeFlip (v : Fin n → Bool) (i : Fin n) :
    cubeFlip (cubeFlip v i) i = v := by
  classical
  funext j
  by_cases hji : j = i <;> simp [cubeFlip, hji]

theorem cubeFlip_injective (v : Fin n → Bool) : Function.Injective (cubeFlip v) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij i
  simp [cubeFlip, hne] at h

/-- A cover by open radius-one neighborhoods. -/
structure OpenNeighborhoodCover (n H : ℕ) where
  center : Fin H → (Fin n → Bool)
  covers : ∀ x, ∃ h i, x = cubeFlip (center h) i

/-- The coordinate literal detecting disagreement with a center. -/
def disagreementCoefficient (v : Fin n → Bool) (i j : Fin n) : ℝ :=
  if j = i then if v i then -1 else 1 else 0

theorem disagreement_affineValue (v : Fin n → Bool) (i : Fin n) (y : Fin n → Bool) :
    affineValue (boolToReal (v i)) (disagreementCoefficient v i) y =
      if y i ≠ v i then 1 else 0 := by
  classical
  simp only [affineValue, disagreementCoefficient, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_eq_left]
  cases v i <;> cases y i <;> simp [boolToReal]

/-- The affine denominator whose zero set is exactly the open neighborhood. -/
def neighborhoodConst (v : Fin n → Bool) : ℝ :=
  (∑ i, boolToReal (v i)) - 1

def neighborhoodCoefficient (v : Fin n → Bool) (i : Fin n) : ℝ :=
  if v i then -1 else 1

theorem neighborhood_eval (v y : Fin n → Bool) :
    affineValue (neighborhoodConst v) (neighborhoodCoefficient v) y =
      (((Finset.univ : Finset (Fin n)).filter fun i ↦ y i ≠ v i).card : ℝ) - 1 := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  have hterm (i : Fin n) :
      boolToReal (v i) + neighborhoodCoefficient v i * boolToReal (y i) =
        ((if y i ≠ v i then 1 else 0 : ℕ) : ℝ) := by
    cases hv : v i <;> cases y i <;> simp [boolToReal, neighborhoodCoefficient, hv]
  simp only [affineValue, neighborhoodConst]
  rw [show (∑ i, boolToReal (v i)) - 1 +
      ∑ i, neighborhoodCoefficient v i * boolToReal (y i) =
      (∑ i, (boolToReal (v i) + neighborhoodCoefficient v i * boolToReal (y i))) - 1 by
    rw [Finset.sum_add_distrib]; ring]
  simp_rw [hterm]

theorem neighborhood_zero_iff (v y : Fin n → Bool) :
    affineValue (neighborhoodConst v) (neighborhoodCoefficient v) y = 0 ↔
      ∃ i, y = cubeFlip v i := by
  classical
  rw [neighborhood_eval, sub_eq_zero]
  constructor
  · intro hcard
    have hc : ((Finset.univ : Finset (Fin n)).filter fun i ↦ y i ≠ v i).card = 1 := by
      exact_mod_cast hcard
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, ?_⟩
    funext j
    have hj : y j ≠ v j ↔ j = i := by
      have := congrArg (fun S : Finset (Fin n) ↦ j ∈ S) hi
      simpa using this
    by_cases hji : j = i
    · subst j
      have hne := hj.mpr rfl
      cases hy : y i <;> cases hv : v i <;> simp_all [cubeFlip]
    · simp [cubeFlip, hji, not_not.mp (by simpa [hji] using hj)]
  · rintro ⟨i, rfl⟩
    have hs : ((Finset.univ : Finset (Fin n)).filter fun j ↦ cubeFlip v i j ≠ v j) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases hji : j = i
      · subst j; simp [cubeFlip]
      · simp [cubeFlip, hji]
    simp [hs]

namespace OpenNeighborhoodCover

theorem nonempty_interpolation (C : OpenNeighborhoodCover n H) :
    Nonempty (AffineZeroSetInterpolation n H) := by
  classical
  choose head coordinate hflip using C.covers
  refine ⟨{
    denConst := fun h ↦ neighborhoodConst (C.center h)
    denCoeff := fun h ↦ neighborhoodCoefficient (C.center h)
    head := head
    numConst := fun x ↦ boolToReal (C.center (head x) (coordinate x))
    numCoeff := fun x ↦ disagreementCoefficient (C.center (head x)) (coordinate x)
    isolates := ?_ }⟩
  intro y x
  by_cases hz : affineValue (neighborhoodConst (C.center (head x)))
      (neighborhoodCoefficient (C.center (head x))) y = 0
  · obtain ⟨j, rfl⟩ := (neighborhood_zero_iff _ _).mp hz
    rw [ite_eq_left hz, disagreement_affineValue]
    have heq : cubeFlip (C.center (head x)) j = x ↔ j = coordinate x := by
      constructor
      · intro h
        exact cubeFlip_injective _ (h.trans (hflip x))
      · intro h
        subst j
        exact (hflip x).symm
    simp only [heq]
    by_cases hj : j = coordinate x
    · subst j
      simp [cubeFlip]
    · simp [cubeFlip, Ne.symm hj, hj]
  · rw [ite_eq_right hz]
    have hyx : y ≠ x := by
      intro heq
      subst y
      exact hz ((neighborhood_zero_iff _ _).mpr ⟨coordinate x, hflip x⟩)
    simp [hyx]

/-- Fixed positive denominators interpolate every real cube function. -/
noncomputable def toClearedSpanCertificate (C : OpenNeighborhoodCover n H) :
    ClearedSpanCertificate n H :=
  (Classical.choice C.nonempty_interpolation).toClearedSpanCertificate

theorem nonempty_clearedSpanCertificate (C : OpenNeighborhoodCover n H) :
    Nonempty (ClearedSpanCertificate n H) := ⟨C.toClearedSpanCertificate⟩

theorem HStar_le (C : OpenNeighborhoodCover n H) (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ H := C.toClearedSpanCertificate.HStar_le f

end OpenNeighborhoodCover

end HeadComplexity
