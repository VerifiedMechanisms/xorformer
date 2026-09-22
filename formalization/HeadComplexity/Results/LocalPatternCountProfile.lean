import HeadComplexity.Atoms.SignPolynomial
import HeadComplexity.Results.RawCalibratedVote
import HeadComplexity.Results.StructuralInvariances
import HeadComplexity.Results.SymmetricComplexity

set_option linter.style.header false

/-!
# Local-pattern count profiles

This file formalizes the exact finite-support schema of theorem note 53.  A
two-bit predicate is evaluated independently on `m` coordinate pairs.  The
target depends only on the number of successful local predicates.

The upper bound records the actual monomials in the canonical multilinear
expansions of all nonempty products of at most `C` local predicates.  Thus it
does not replace the local expansion cost by a generic degree bound.  The
lower bound restricts either an identity or a complemented one-bit slice to a
symmetric Hamming-weight profile.
-/

namespace HeadComplexity

open Finset Polynomial MvPolynomial
open scoped BigOperators

namespace LocalPatternCountProfile

variable {m : ℕ}

/-- The left bit in the `i`th coordinate pair. -/
def leftBit (bits : Fin (m + m) → Bool) (i : Fin m) : Bool :=
  bits (Fin.castAdd m i)

/-- The right bit in the `i`th coordinate pair. -/
def rightBit (bits : Fin (m + m) → Bool) (i : Fin m) : Bool :=
  bits (Fin.natAdd m i)

/-- The vector of local predicate values. -/
def patternBits (p : Bool → Bool → Bool) (bits : Fin (m + m) → Bool) :
    Fin m → Bool :=
  fun i ↦ p (leftBit bits i) (rightBit bits i)

/-- Number of coordinate pairs on which `p` is true. -/
def patternCount (p : Bool → Bool → Bool) (bits : Fin (m + m) → Bool) : ℕ :=
  hammingWeight (patternBits p bits)

/-- A Boolean profile of the local-pattern count. -/
def target (p : Bool → Bool → Bool) (F : ℕ → Bool)
    (bits : Fin (m + m) → Bool) : Bool :=
  F (patternCount p bits)

/-- Product of the local predicates indexed by `S`, as a Boolean feature. -/
def productFeature (p : Bool → Bool → Bool) (S : Finset (Fin m))
    (bits : Fin (m + m) → Bool) : Bool :=
  decide (∀ i ∈ S, patternBits p bits i = true)

/-- The constant-one squarefree polynomial.  It is used for the empty local
product so that its nonconstant coefficients are definitionally zero. -/
def constantOnePolynomial : SquarefreePolynomial (m + m) :=
  ⟨fun A ↦ if A = ∅ then 1 else 0⟩

/-- Canonical multilinear expansion of a local-predicate product. -/
noncomputable def productPolynomial (p : Bool → Bool → Bool)
    (S : Finset (Fin m)) : SquarefreePolynomial (m + m) :=
  if S = ∅ then constantOnePolynomial
  else exactBooleanSquarefreePolynomial (productFeature p S)

@[simp] theorem productFeature_empty (p : Bool → Bool → Bool)
    (bits : Fin (m + m) → Bool) :
    productFeature p ∅ bits = true := by
  simp [productFeature]

private theorem squarefreeMonomial_patternBits
    (p : Bool → Bool → Bool) (S : Finset (Fin m))
    (bits : Fin (m + m) → Bool) :
    squarefreeMonomial S (patternBits p bits) =
      boolToReal (productFeature p S bits) := by
  by_cases hall : ∀ i ∈ S, patternBits p bits i = true
  · have hprod : squarefreeMonomial S (patternBits p bits) = 1 := by
      unfold squarefreeMonomial
      apply Finset.prod_eq_one
      intro i hi
      simp [boolToReal, hall i hi]
    have hfeature : productFeature p S bits = true := by
      exact decide_eq_true_eq.mpr hall
    rw [hprod, hfeature]
    rfl
  · push Not at hall
    obtain ⟨i, hi, hfalse⟩ := hall
    have hbit : patternBits p bits i = false := by
      cases h : patternBits p bits i with
      | false => rfl
      | true => exact (hfalse h).elim
    have hprod : squarefreeMonomial S (patternBits p bits) = 0 := by
      unfold squarefreeMonomial
      apply Finset.prod_eq_zero hi
      simp [boolToReal, hbit]
    have hfeature : productFeature p S bits = false := by
      apply decide_eq_false_iff_not.mpr
      intro h
      exact Bool.false_ne_true (h i hi ▸ hbit.symm)
    rw [hprod, hfeature]
    rfl

/-- The product polynomial evaluates to the product of the selected local
predicate indicators. -/
theorem productPolynomial_eval (p : Bool → Bool → Bool)
    (S : Finset (Fin m)) (bits : Fin (m + m) → Bool) :
    (productPolynomial p S).eval bits =
      squarefreeMonomial S (patternBits p bits) := by
  by_cases hS : S = ∅
  · subst S
    simp [productPolynomial, constantOnePolynomial,
      SquarefreePolynomial.eval, SquarefreePolynomial.nonlinearSupport,
      affineValue, squarefreeMonomial]
  · rw [productPolynomial, if_neg hS,
      exactBooleanSquarefreePolynomial_eval,
      squarefreeMonomial_patternBits]

theorem productPolynomial_empty_coeff_of_nonempty
    (p : Bool → Bool → Bool) {A : Finset (Fin (m + m))}
    (hA : A.Nonempty) :
    (productPolynomial p ∅).coeff A = 0 := by
  simp [productPolynomial, constantOnePolynomial, hA.ne_empty]

/-- Nonempty local products of size at most `C`. -/
def eligibleProducts (m C : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter fun S ↦ S.Nonempty ∧ S.card ≤ C

/-- Degree-at-least-two monomials occurring in at least one eligible local
product expansion. -/
noncomputable def nonlinearExpansionSupport
    (p : Bool → Bool → Bool) (C : ℕ) : Finset (Finset (Fin (m + m))) :=
  (eligibleProducts m C).biUnion fun S ↦ (productPolynomial p S).nonlinearSupport

/-- Whether an eligible local product has a nonzero linear monomial. -/
def HasLinearExpansion (p : Bool → Bool → Bool) (C : ℕ) : Prop :=
  ∃ S ∈ eligibleProducts m C, (productPolynomial p S).HasLinearPart

/-- The exact local expansion cost from theorem note 53. -/
noncomputable def expansionCost (p : Bool → Bool → Bool) (C : ℕ) : ℕ := by
  classical
  exact (if HasLinearExpansion (m := m) p C then 1 else 0) +
    (nonlinearExpansionSupport (m := m) p C).card

/-- The empty index range has zero local expansion cost. -/
@[simp] theorem expansionCost_zero (p : Bool → Bool → Bool) :
    expansionCost (m := m) p 0 = 0 := by
  classical
  have hempty : eligibleProducts m 0 = ∅ := by
    ext S
    constructor
    · intro h
      have hdata := (Finset.mem_filter.mp h).2
      have hpos := Finset.card_pos.mpr hdata.1
      omega
    · intro h
      exact (Finset.notMem_empty S h).elim
  simp [expansionCost, HasLinearExpansion, nonlinearExpansionSupport, hempty]

/-! ## Expanding a univariate polynomial in Boolean local features -/

/-- Substitute the sum of `m` formal Boolean variables into `R`. -/
noncomputable def countMvPolynomial (R : ℝ[X]) : MvPolynomial (Fin m) ℝ :=
  R.eval₂ C (∑ i, X i)

private theorem sumVariables_totalDegree_le :
    (∑ i : Fin m, (X i : MvPolynomial (Fin m) ℝ)).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i hi
  simp

theorem countMvPolynomial_totalDegree_le (R : ℝ[X]) :
    (countMvPolynomial (m := m) R).totalDegree ≤ R.natDegree := by
  rw [countMvPolynomial, Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc
    (MvPolynomial.C (R.coeff i) *
        (∑ j : Fin m, (X j : MvPolynomial (Fin m) ℝ)) ^ i).totalDegree ≤
        (MvPolynomial.C (R.coeff i)).totalDegree +
          ((∑ j : Fin m, (X j : MvPolynomial (Fin m) ℝ)) ^ i).totalDegree :=
      totalDegree_mul _ _
    _ ≤ 0 + i * (∑ j : Fin m,
          (X j : MvPolynomial (Fin m) ℝ)).totalDegree := by
      rw [totalDegree_C]
      exact Nat.add_le_add_left (totalDegree_pow _ i) 0
    _ ≤ R.natDegree := by
      simp only [zero_add]
      calc
        i * (∑ j : Fin m,
            (X j : MvPolynomial (Fin m) ℝ)).totalDegree ≤ i * 1 :=
          Nat.mul_le_mul_left i sumVariables_totalDegree_le
        _ ≤ R.natDegree := by simpa using Nat.le_of_lt_succ hi

/-- Canonical squarefree reduction of `R` evaluated on a Boolean count. -/
noncomputable def countPolynomial (R : ℝ[X]) : SquarefreePolynomial m :=
  SquarefreePolynomial.ofMvPolynomial (countMvPolynomial R)

theorem countPolynomial_degreeLE (R : ℝ[X]) :
    (countPolynomial (m := m) R).DegreeLE R.natDegree :=
  SquarefreePolynomial.ofMvPolynomial_degreeLE _
    (countMvPolynomial_totalDegree_le R)

theorem countPolynomial_eval (R : ℝ[X]) (z : Fin m → Bool) :
    (countPolynomial R).eval z = R.eval (hammingWeight z : ℝ) := by
  rw [countPolynomial, SquarefreePolynomial.ofMvPolynomial_eval,
    countMvPolynomial, Polynomial.hom_eval₂]
  have hcomp : (MvPolynomial.eval (cubePoint z)).comp MvPolynomial.C =
      RingHom.id ℝ := by
    ext x
    simp
  rw [hcomp]
  simp only [map_sum, MvPolynomial.eval_X]
  change Polynomial.eval₂ (RingHom.id ℝ)
      (∑ i, boolToReal (z i)) R = _
  rw [← hammingWeight_eq_sum]
  exact Polynomial.eval₂_at_apply (RingHom.id ℝ) _

/-- Expand `R` in the canonical products of local predicates. -/
noncomputable def expandedPolynomial (p : Bool → Bool → Bool) (R : ℝ[X]) :
    SquarefreePolynomial (m + m) :=
  ⟨fun A ↦ ∑ S : Finset (Fin m),
    (countPolynomial R).coeff S * (productPolynomial p S).coeff A⟩

/-- The local expansion has exactly the same value as `R` applied to the
local-pattern count. -/
theorem expandedPolynomial_eval (p : Bool → Bool → Bool) (R : ℝ[X])
    (bits : Fin (m + m) → Bool) :
    (expandedPolynomial p R).eval bits =
      R.eval (patternCount p bits : ℝ) := by
  classical
  rw [← SquarefreePolynomial.fullSum_eq_eval]
  simp only [expandedPolynomial, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ S : Finset (Fin m),
      (∑ A : Finset (Fin (m + m)),
          (productPolynomial p S).coeff A * squarefreeMonomial A bits) =
        squarefreeMonomial S (patternBits p bits) := by
    intro S
    rw [SquarefreePolynomial.fullSum_eq_eval,
      productPolynomial_eval]
  simp_rw [mul_assoc, ← Finset.mul_sum, hinner]
  rw [SquarefreePolynomial.fullSum_eq_eval, countPolynomial_eval]
  rfl

private theorem expanded_nonlinearSupport_subset
    (p : Bool → Bool → Bool) (R : ℝ[X]) {C : ℕ}
    (hdeg : R.natDegree ≤ C) :
    (expandedPolynomial p R).nonlinearSupport ⊆
      nonlinearExpansionSupport (m := m) p C := by
  classical
  intro A hA
  simp only [SquarefreePolynomial.nonlinearSupport, Finset.mem_filter,
    Finset.mem_univ, true_and] at hA
  rw [nonlinearExpansionSupport, Finset.mem_biUnion]
  by_contra hnone
  push Not at hnone
  apply hA.2
  change (∑ S : Finset (Fin m),
    (countPolynomial R).coeff S * (productPolynomial p S).coeff A) = 0
  apply Finset.sum_eq_zero
  intro S hSuniv
  by_cases hS : S = ∅
  · subst S
    simp [productPolynomial_empty_coeff_of_nonempty p
      (Finset.card_pos.mp (by omega : 0 < A.card))]
  · by_cases hcard : S.card ≤ C
    · have helig : S ∈ eligibleProducts m C := by
        simp [eligibleProducts, Finset.nonempty_iff_ne_empty.mpr hS, hcard]
      have hnotmem := hnone S helig
      have hcoeff : (productPolynomial p S).coeff A = 0 := by
        by_contra hne
        exact hnotmem (by
          simp [SquarefreePolynomial.nonlinearSupport, hA.1, hne])
      simp [hcoeff]
    · have hzero : (countPolynomial R).coeff S = 0 := by
        by_contra hne
        have hle := countPolynomial_degreeLE R S hne
        omega
      simp [hzero]

private theorem expanded_hasLinearPart
    (p : Bool → Bool → Bool) (R : ℝ[X]) {C : ℕ}
    (hdeg : R.natDegree ≤ C)
    (hlin : (expandedPolynomial (m := m) p R).HasLinearPart) :
    HasLinearExpansion (m := m) p C := by
  classical
  obtain ⟨i, hi⟩ := hlin
  by_contra hnone
  apply hi
  change (∑ S : Finset (Fin m),
    (countPolynomial R).coeff S * (productPolynomial p S).coeff {i}) = 0
  apply Finset.sum_eq_zero
  intro S hSuniv
  by_cases hS : S = ∅
  · subst S
    simp [productPolynomial_empty_coeff_of_nonempty p
      (Finset.singleton_nonempty i)]
  · by_cases hcard : S.card ≤ C
    · have helig : S ∈ eligibleProducts m C := by
        simp [eligibleProducts, Finset.nonempty_iff_ne_empty.mpr hS, hcard]
      have hnotlin : ¬(productPolynomial p S).HasLinearPart := by
        intro h
        exact hnone ⟨S, helig, h⟩
      have hcoeff : (productPolynomial p S).coeff {i} = 0 := by
        by_contra hne
        exact hnotlin ⟨i, hne⟩
      simp [hcoeff]
    · have hzero : (countPolynomial R).coeff S = 0 := by
        by_contra hne
        have hle := countPolynomial_degreeLE R S hne
        omega
      simp [hzero]

/-- The affine-free support of the expanded sign polynomial is bounded by the
exact union-of-local-products cost. -/
theorem expandedPolynomial_affineFreeSupportCost_le
    (p : Bool → Bool → Bool) (R : ℝ[X]) {C : ℕ}
    (hdeg : R.natDegree ≤ C) :
    (expandedPolynomial (m := m) p R).affineFreeSupportCost ≤
      expansionCost (m := m) p C := by
  classical
  have hsupport := Finset.card_le_card
    (expanded_nonlinearSupport_subset (m := m) p R hdeg)
  unfold SquarefreePolynomial.affineFreeSupportCost expansionCost
  by_cases hlin : (expandedPolynomial (m := m) p R).HasLinearPart
  · rw [if_pos hlin, if_pos (expanded_hasLinearPart p R hdeg hlin)]
    omega
  · rw [if_neg hlin]
    split <;> omega

/-! ## Upper bound -/

/-- The exact local expansion cost upper-bounds the head complexity of every
local-pattern count profile. -/
theorem HStar_le_expansionCost (p : Bool → Bool → Bool) (F : ℕ → Bool) :
    HStar (m + m) (target (m := m) p F) ≤
      expansionCost (m := m) p (signChanges m F) := by
  classical
  obtain ⟨R, hRdeg, hRsign⟩ := exists_sign_poly F m
  let P := expandedPolynomial (m := m) p R
  have hcount : ∀ bits : Fin (m + m) → Bool, patternCount p bits ≤ m := by
    intro bits
    exact hammingWeight_le m (patternBits p bits)
  have hP : P.SignRepresents (target (m := m) p F) := by
    intro bits
    rw [show P.eval bits = R.eval (patternCount p bits : ℝ) by
      exact expandedPolynomial_eval p R bits]
    exact hRsign (patternCount p bits) (hcount bits)
  obtain ⟨Q, hQ, hQcost, _⟩ :=
    P.exists_strictification (target (m := m) p F) hP
  calc
    HStar (m + m) (target (m := m) p F) ≤ Q.affineFreeSupportCost :=
      Q.HStar_le_affineFreeSupportCost (target (m := m) p F) hQ
    _ = P.affineFreeSupportCost := hQcost
    _ ≤ expansionCost p (signChanges m F) :=
      expandedPolynomial_affineFreeSupportCost_le (m := m) p R hRdeg

/-! ## Symmetric-slice lower bound -/

/-- The left coordinate in every pair is free; the right coordinate is fixed. -/
def leftFreeFace (fixed : Bool) : CoordFace m (m + m) where
  free := Fin.castAddEmb m
  base := fun _ ↦ fixed

/-- The right coordinate in every pair is free; the left coordinate is fixed. -/
def rightFreeFace (fixed : Bool) : CoordFace m (m + m) where
  free := Fin.natAddEmb m
  base := fun _ ↦ fixed

@[simp] theorem leftFreeFace_left (fixed : Bool) (z : Fin m → Bool) (i : Fin m) :
    leftBit ((leftFreeFace fixed).apply z) i = z i := by
  change (leftFreeFace fixed).apply z ((leftFreeFace fixed).free i) = z i
  exact CoordFace.apply_free _ _ _

@[simp] theorem leftFreeFace_right (fixed : Bool) (z : Fin m → Bool) (i : Fin m) :
    rightBit ((leftFreeFace fixed).apply z) i = fixed := by
  rw [rightBit, CoordFace.apply]
  simp only [leftFreeFace]
  rw [dif_neg]
  rintro ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  simp at hval
  omega

@[simp] theorem rightFreeFace_left (fixed : Bool) (z : Fin m → Bool) (i : Fin m) :
    leftBit ((rightFreeFace fixed).apply z) i = fixed := by
  rw [leftBit, CoordFace.apply]
  simp only [rightFreeFace]
  rw [dif_neg]
  rintro ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  simp at hval
  omega

@[simp] theorem rightFreeFace_right (fixed : Bool) (z : Fin m → Bool) (i : Fin m) :
    rightBit ((rightFreeFace fixed).apply z) i = z i := by
  change (rightFreeFace fixed).apply z ((rightFreeFace fixed).free i) = z i
  exact CoordFace.apply_free _ _ _

/-- Fixing one input of `p` exposes the identity one-bit function. -/
def HasIdentitySlice (p : Bool → Bool → Bool) : Prop :=
  (∃ fixed, ∀ z, p z fixed = z) ∨
    (∃ fixed, ∀ z, p fixed z = z)

/-- Fixing one input of `p` exposes the complemented one-bit function. -/
def HasComplementSlice (p : Bool → Bool → Bool) : Prop :=
  (∃ fixed, ∀ z, p z fixed = !z) ∨
    (∃ fixed, ∀ z, p fixed z = !z)

/-- The one-bit slice assumption of theorem note 53. -/
def HasSymmetricOneBitSlice (p : Bool → Bool → Bool) : Prop :=
  HasIdentitySlice p ∨ HasComplementSlice p

private theorem patternBits_left_identity
    (p : Bool → Bool → Bool) (fixed : Bool)
    (hp : ∀ z, p z fixed = z) (z : Fin m → Bool) :
    patternBits p ((leftFreeFace fixed).apply z) = z := by
  funext i
  simp [patternBits, hp]

private theorem patternBits_right_identity
    (p : Bool → Bool → Bool) (fixed : Bool)
    (hp : ∀ z, p fixed z = z) (z : Fin m → Bool) :
    patternBits p ((rightFreeFace fixed).apply z) = z := by
  funext i
  simp [patternBits, hp]

private theorem patternBits_left_complement
    (p : Bool → Bool → Bool) (fixed : Bool)
    (hp : ∀ z, p z fixed = !z) (z : Fin m → Bool) :
    patternBits p ((leftFreeFace fixed).apply z) = flipBits z := by
  funext i
  simp [patternBits, flipBits, hp]

private theorem patternBits_right_complement
    (p : Bool → Bool → Bool) (fixed : Bool)
    (hp : ∀ z, p fixed z = !z) (z : Fin m → Bool) :
    patternBits p ((rightFreeFace fixed).apply z) = flipBits z := by
  funext i
  simp [patternBits, flipBits, hp]

private theorem lower_of_identity_left
    (p : Bool → Bool → Bool) (F : ℕ → Bool) (fixed : Bool)
    (hp : ∀ z, p z fixed = z) :
    signChanges m F ≤ HStar (m + m) (target (m := m) p F) := by
  have hrestrict := HStar_restrict_le (m := m) (n := m + m)
    (leftFreeFace fixed) (target (m := m) p F)
  have hfun : (fun z ↦ target (m := m) p F ((leftFreeFace fixed).apply z)) =
      symmetricFn F := by
    funext z
    simp only [target, patternCount, symmetricFn]
    rw [patternBits_left_identity p fixed hp z]
  rw [hfun, HStar_symmetricFn] at hrestrict
  exact hrestrict

private theorem lower_of_identity_right
    (p : Bool → Bool → Bool) (F : ℕ → Bool) (fixed : Bool)
    (hp : ∀ z, p fixed z = z) :
    signChanges m F ≤ HStar (m + m) (target (m := m) p F) := by
  have hrestrict := HStar_restrict_le (m := m) (n := m + m)
    (rightFreeFace fixed) (target (m := m) p F)
  have hfun : (fun z ↦ target (m := m) p F ((rightFreeFace fixed).apply z)) =
      symmetricFn F := by
    funext z
    simp only [target, patternCount, symmetricFn]
    rw [patternBits_right_identity p fixed hp z]
  rw [hfun, HStar_symmetricFn] at hrestrict
  exact hrestrict

private theorem lower_of_complement_left
    (p : Bool → Bool → Bool) (F : ℕ → Bool) (fixed : Bool)
    (hp : ∀ z, p z fixed = !z) :
    signChanges m F ≤ HStar (m + m) (target (m := m) p F) := by
  have hrestrict := HStar_restrict_le (m := m) (n := m + m)
    (leftFreeFace fixed) (target (m := m) p F)
  have hfun : (fun z ↦ target (m := m) p F ((leftFreeFace fixed).apply z)) =
      fun z ↦ symmetricFn F (flipBits z) := by
    funext z
    simp only [target, patternCount, symmetricFn]
    rw [patternBits_left_complement p fixed hp z]
  rw [hfun, HStar_flip, HStar_symmetricFn] at hrestrict
  exact hrestrict

private theorem lower_of_complement_right
    (p : Bool → Bool → Bool) (F : ℕ → Bool) (fixed : Bool)
    (hp : ∀ z, p fixed z = !z) :
    signChanges m F ≤ HStar (m + m) (target (m := m) p F) := by
  have hrestrict := HStar_restrict_le (m := m) (n := m + m)
    (rightFreeFace fixed) (target (m := m) p F)
  have hfun : (fun z ↦ target (m := m) p F ((rightFreeFace fixed).apply z)) =
      fun z ↦ symmetricFn F (flipBits z) := by
    funext z
    simp only [target, patternCount, symmetricFn]
    rw [patternBits_right_complement p fixed hp z]
  rw [hfun, HStar_flip, HStar_symmetricFn] at hrestrict
  exact hrestrict

/-- An identity or complemented one-bit slice forces the profile's exact
sign-change lower bound. -/
theorem signChanges_le_HStar (p : Bool → Bool → Bool) (F : ℕ → Bool)
    (hslice : HasSymmetricOneBitSlice p) :
    signChanges m F ≤ HStar (m + m) (target (m := m) p F) := by
  rcases hslice with ((⟨fixed, hp⟩ | ⟨fixed, hp⟩) |
      (⟨fixed, hp⟩ | ⟨fixed, hp⟩))
  · exact lower_of_identity_left p F fixed hp
  · exact lower_of_identity_right p F fixed hp
  · exact lower_of_complement_left p F fixed hp
  · exact lower_of_complement_right p F fixed hp

/-- **Local-pattern count profile schema.**  The lower bound comes from the
one-bit slice and the upper bound is the exact finite local expansion cost. -/
theorem signChanges_le_HStar_le_expansionCost
    (p : Bool → Bool → Bool) (F : ℕ → Bool)
    (hslice : HasSymmetricOneBitSlice p) :
    signChanges m F ≤ HStar (m + m) (target (m := m) p F) ∧
      HStar (m + m) (target (m := m) p F) ≤
        expansionCost (m := m) p (signChanges m F) :=
  ⟨signChanges_le_HStar (m := m) p F hslice,
    HStar_le_expansionCost (m := m) p F⟩

end LocalPatternCountProfile

end HeadComplexity
