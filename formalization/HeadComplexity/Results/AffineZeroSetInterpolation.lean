import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Instances.Matrix

import HeadComplexity.Results.DeterminantSpan

set_option linter.style.header false

/-!
# Affine zero-set interpolation

Affine numerator columns which isolate all cube vertices on affine denominator
zero sets give a full interpolation space. The temporary denominators can have
mixed signs: polynomial extensionality on a positive box transfers a nonzero
minor to strictly positive coefficients before compiling actual attention heads.
-/

namespace HeadComplexity

open Finset Filter MvPolynomial
open scoped BigOperators Topology

variable {n H : ℕ}

/-- One affine numerator column per cube vertex, assigned to a denominator
whose zero set isolates that vertex. -/
structure AffineZeroSetInterpolation (n H : ℕ) where
  denConst : Fin H → ℝ
  denCoeff : Fin H → Fin n → ℝ
  head : (Fin n → Bool) → Fin H
  numConst : (Fin n → Bool) → ℝ
  numCoeff : (Fin n → Bool) → Fin n → ℝ
  isolates : ∀ y x,
    (if affineValue (denConst (head x)) (denCoeff (head x)) y = 0
      then affineValue (numConst x) (numCoeff x) y else 0) = if y = x then 1 else 0

namespace AffineZeroSetInterpolation

noncomputable def matrix (C : AffineZeroSetInterpolation n H)
    (a : Fin H → ℝ) (b : Fin H → Fin n → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  Matrix.of fun y x ↦ affineValue (C.numConst x) (C.numCoeff x) y *
    ∏ h ∈ Finset.univ.erase (C.head x), affineValue (a h) (b h) y

/-- Resolve each zero-set pole continuously at zero. -/
noncomputable def resolvedMatrix (C : AffineZeroSetInterpolation n H) (t : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  Matrix.of fun y x ↦
    if affineValue (C.denConst (C.head x)) (C.denCoeff (C.head x)) y = 0
    then affineValue (C.numConst x) (C.numCoeff x) y
    else t * affineValue (C.numConst x) (C.numCoeff x) y /
      (affineValue (C.denConst (C.head x)) (C.denCoeff (C.head x)) y + t)

theorem resolvedMatrix_zero (C : AffineZeroSetInterpolation n H) :
    C.resolvedMatrix 0 = 1 := by
  classical
  ext y x
  simpa [resolvedMatrix, Matrix.one_apply] using C.isolates y x

theorem resolvedMatrix_continuousAt (C : AffineZeroSetInterpolation n H) :
    ContinuousAt C.resolvedMatrix 0 := by
  classical
  apply continuousAt_pi.mpr
  intro y
  apply continuousAt_pi.mpr
  intro x
  dsimp [resolvedMatrix]
  split
  · exact continuousAt_const
  · exact (continuousAt_id.mul continuousAt_const).div
      (continuousAt_const.add continuousAt_id) (by simpa)

theorem exists_matrix_det_ne_zero (C : AffineZeroSetInterpolation n H) :
    ∃ a b, (C.matrix a b).det ≠ 0 := by
  classical
  have hcontinuous : ContinuousAt (fun t ↦ (C.resolvedMatrix t).det) 0 :=
    continuous_id.matrix_det.continuousAt.comp C.resolvedMatrix_continuousAt
  have hdet : ∀ᶠ t in 𝓝[≠] (0 : ℝ), (C.resolvedMatrix t).det ≠ 0 :=
    (hcontinuous.eventually_ne (by rw [C.resolvedMatrix_zero]; simp)).filter_mono
      nhdsWithin_le_nhds
  have hden : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ h y,
      affineValue (C.denConst h) (C.denCoeff h) y + t ≠ 0 := by
    rw [Filter.eventually_all]
    intro h
    rw [Filter.eventually_all]
    intro y
    by_cases hz : affineValue (C.denConst h) (C.denCoeff h) y = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [hz] using ht
    · exact ((continuousAt_const.add continuousAt_id).eventually_ne
        (by simpa using hz)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, hd, htnz⟩ :=
    (hdet.and (hden.and (show ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 from
      self_mem_nhdsWithin))).exists
  let a : Fin H → ℝ := fun h ↦ C.denConst h + t
  let D : Fin H → (Fin n → Bool) → ℝ :=
    fun h y ↦ affineValue (C.denConst h) (C.denCoeff h) y + t
  have hD : ∀ h y, D h y ≠ 0 := hd
  have hprod (y : Fin n → Bool) : (∏ h, D h y) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun h _ ↦ hD h y
  have hentry (y x : Fin n → Bool) :
      C.resolvedMatrix t y x =
        t * affineValue (C.numConst x) (C.numCoeff x) y / D (C.head x) y := by
    dsimp [resolvedMatrix, D]
    split
    · rename_i hz
      rw [hz, zero_add]
      field_simp
    · rfl
  have hmatrix : C.matrix a C.denCoeff = Matrix.of fun y x ↦
      ((∏ h, D h y) / t) * C.resolvedMatrix t y x := by
    ext y x
    simp only [matrix, Matrix.of_apply]
    rw [hentry]
    have hp := Finset.mul_prod_erase Finset.univ (fun h ↦ D h y)
      (Finset.mem_univ (C.head x))
    have hshift (h : Fin H) : affineValue (a h) (C.denCoeff h) y = D h y := by
      dsimp [a, D, affineValue]
      ring
    simp only [hshift]
    rw [← hp]
    field_simp [htnz, hD (C.head x) y]
  refine ⟨a, C.denCoeff, ?_⟩
  rw [hmatrix, Matrix.det_mul_column]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun y _ ↦ div_ne_zero (hprod y) htnz) ht

/-- Independent affine denominator parameters, including their constants. -/
abbrev Parameter (n H : ℕ) := Fin H × Option (Fin n)

noncomputable def denominatorPoly (h : Fin H) (y : Fin n → Bool) :
    MvPolynomial (Parameter n H) ℝ :=
  X (h, none) + ∑ i, C (boolToReal (y i)) * X (h, some i)

theorem eval_denominatorPoly (p : Parameter n H → ℝ) (h : Fin H) (y : Fin n → Bool) :
    eval p (denominatorPoly h y) = affineValue (p (h, none)) (fun i ↦ p (h, some i)) y := by
  simp [denominatorPoly, affineValue, mul_comm]

noncomputable def determinantPoly (C : AffineZeroSetInterpolation n H) :
    MvPolynomial (Parameter n H) ℝ :=
  Matrix.det (Matrix.of fun (y x : Fin n → Bool) ↦
    MvPolynomial.C (affineValue (C.numConst x) (C.numCoeff x) y) *
      ∏ h ∈ Finset.univ.erase (C.head x), denominatorPoly h y)

theorem eval_determinantPoly (C : AffineZeroSetInterpolation n H)
    (p : Parameter n H → ℝ) :
    eval p C.determinantPoly =
      (C.matrix (fun h ↦ p (h, none)) (fun h i ↦ p (h, some i))).det := by
  rw [determinantPoly, (eval p).map_det]
  congr 1
  ext y x
  simp [matrix, eval_denominatorPoly]

/-- The positive coefficient cone contains a nonsingular interpolation matrix. -/
theorem exists_positive_matrix_det_ne_zero (C : AffineZeroSetInterpolation n H) :
    ∃ (a : Fin H → ℝ) (b : Fin H → Fin n → ℝ),
      (∀ h, 0 < a h) ∧ (∀ h i, 0 < b h i) ∧ (C.matrix a b).det ≠ 0 := by
  classical
  obtain ⟨a, b, hdet⟩ := C.exists_matrix_det_ne_zero
  have hp : C.determinantPoly ≠ 0 := by
    intro hz
    let p : Parameter n H → ℝ := fun hi ↦ hi.2.elim (a hi.1) (b hi.1)
    have he := C.eval_determinantPoly p
    simp only [hz, map_zero] at he
    exact hdet (by simpa [p] using he.symm)
  have hex : ∃ p : Parameter n H → ℝ,
      (∀ i, 0 < p i) ∧ eval p C.determinantPoly ≠ 0 := by
    by_contra! hn
    apply hp
    apply MvPolynomial.funext_set (fun _ ↦ Set.Ioi (0 : ℝ))
      (fun _ ↦ Set.Ioi_infinite 0)
    intro p hmem
    simpa using hn p (fun i ↦ hmem i (Set.mem_univ i))
  obtain ⟨p, hpos, hne⟩ := hex
  exact ⟨fun h ↦ p (h, none), fun h i ↦ p (h, some i),
    fun h ↦ hpos _, fun h i ↦ hpos _, by rwa [← C.eval_determinantPoly]⟩

/-- Transfer the full interpolation matrix to the existing cleared-span compiler. -/
theorem nonempty_clearedSpanCertificate (C : AffineZeroSetInterpolation n H) :
    Nonempty (ClearedSpanCertificate n H) := by
  classical
  obtain ⟨a, b, ha, hb, hdet⟩ := C.exists_positive_matrix_det_ne_zero
  refine ⟨⟨a, b, ha, hb, ?_⟩⟩
  intro target
  have hsurj : Function.Surjective (C.matrix a b).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨v, hv⟩ := hsurj target
  refine ⟨0,
    fun h ↦ ∑ x, if C.head x = h then v x * C.numConst x else 0,
    fun h i ↦ ∑ x, if C.head x = h then v x * C.numCoeff x i else 0, fun y ↦ ?_⟩
  have hsum (h : Fin H) :
      affineValue (∑ x, if C.head x = h then v x * C.numConst x else 0)
        (fun i ↦ ∑ x, if C.head x = h then v x * C.numCoeff x i else 0) y =
      ∑ x, if C.head x = h then v x * affineValue (C.numConst x) (C.numCoeff x) y else 0 := by
    simp only [affineValue, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : C.head x = h
    · simp only [hx, ↓reduceIte]
      rw [mul_add, Finset.mul_sum]
      simp [mul_assoc]
    · simp [hx]
  simp only [zero_mul, zero_add, hsum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hrow := congrFun hv y
  simpa [Matrix.mulVec, dotProduct, matrix, mul_comm, mul_left_comm, mul_assoc] using hrow.symm

/-- Choose the positive interpolation certificate proved above. -/
noncomputable def toClearedSpanCertificate (C : AffineZeroSetInterpolation n H) :
    ClearedSpanCertificate n H := Classical.choice C.nonempty_clearedSpanCertificate

theorem HStar_le (C : AffineZeroSetInterpolation n H) (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ H := C.toClearedSpanCertificate.HStar_le f

end AffineZeroSetInterpolation

end HeadComplexity
