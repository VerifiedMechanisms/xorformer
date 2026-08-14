import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Atoms.AffineHead
import HeadComplexity.Atoms.PositiveWeightedSignDegree
import HeadComplexity.Results.ExactFamilies
import HeadComplexity.Results.SymmetricFaceLowerBound
import HeadComplexity.Results.ThresholdDegree

set_option linter.style.header false

/-!
# Certificate forms and instances of positive-projection exactness

A low-degree polynomial in a positive weighted statistic supplies the upper
certificate in the existing positive-projection theorem. Matching it with
either a symmetric-face certificate or the ordinary threshold-degree lower
bound gives an equality for functions that need not be symmetric.

The final example is the three-bit function
`not x₂ and (x₀ xor x₁)`.  It has an XOR face and is globally
nonsymmetric.  The positive weighted statistic `x₀ + x₁ + 3 x₂` and a
quadratic interval polynomial give a matching two-head upper bound. The family
and example are checked instances of the earlier exactness result.
-/

namespace HeadComplexity

open Polynomial

variable {n k : ℕ}

namespace PositiveWeightedSignDegLE

/-- A positive weighted sign-degree certificate upper-bounds `HStar`. -/
theorem HStar_le {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f k) : HStar n f ≤ k :=
  HStar_le_of_computableWithHeadsN h.computable

/-- A positive weighted sign-degree certificate factors through the exact cleared-atom
normal form, so it can be consumed by atom-level results as well. -/
theorem clearedAtomRep {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f k) : ClearedAtomRep n k f :=
  (computableWithHeadsN_iff_clearedAtomRep f).mp h.computable

end PositiveWeightedSignDegLE

/-! ## Exact sandwich theorems -/

/-- A numerical lower bound and a matching construction form the generic exact
sandwich used by the more structured corollaries below. -/
theorem HStar_eq_of_lower_bound_of_computableWithHeadsN
    {f : (Fin n → Bool) → Bool}
    (hlower : k ≤ HStar n f)
    (hupper : computableWithHeadsN n k f) :
    HStar n f = k :=
  Nat.le_antisymm (HStar_le_of_computableWithHeadsN hupper) hlower

/-- Any symmetric-face lower certificate becomes exact when accompanied by a
matching explicit head construction. -/
theorem HStar_eq_of_symmetricFace_and_computable
    {f : (Fin n → Bool) → Bool}
    (hlower : HasSymmetricFaceBound f k)
    (hupper : computableWithHeadsN n k f) :
    HStar n f = k :=
  HStar_eq_of_lower_bound_of_computableWithHeadsN hlower.le_HStar hupper

/-- Atom-normal-form version of the exact symmetric-face sandwich. -/
theorem HStar_eq_of_symmetricFace_and_clearedAtomRep
    {f : (Fin n → Bool) → Bool}
    (hlower : HasSymmetricFaceBound f k)
    (hupper : ClearedAtomRep n k f) :
    HStar n f = k :=
  HStar_eq_of_symmetricFace_and_computable hlower
    ((computableWithHeadsN_iff_clearedAtomRep f).mpr hupper)

/-- **Exact weighted-face theorem.** A symmetric face with at least `k` sign
changes and a global degree-`k` weighted-polynomial certificate force
`HStar = k`.  The ambient function need not be symmetric. -/
theorem HStar_eq_of_symmetricFace_and_weightedPolynomial
    {f : (Fin n → Bool) → Bool}
    (hlower : HasSymmetricFaceBound f k)
    (hupper : PositiveWeightedSignDegLE f k) :
    HStar n f = k :=
  HStar_eq_of_symmetricFace_and_computable hlower hupper.computable

/-- Threshold degree can replace the symmetric face as the lower certificate.
This applies even when the function has no useful symmetric face. -/
theorem HStar_eq_of_thresholdDeg_le_and_weightedPolynomial
    {f : (Fin n → Bool) → Bool}
    (hlower : k ≤ thresholdDeg f)
    (hupper : PositiveWeightedSignDegLE f k) :
    HStar n f = k :=
  HStar_eq_of_lower_bound_of_computableWithHeadsN
    (hlower.trans (thresholdDeg_le_HStar f)) hupper.computable

/-- In particular, a weighted univariate polynomial attaining the ordinary
threshold degree also attains exact head complexity. -/
theorem HStar_eq_thresholdDeg_of_weightedPolynomial
    {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f (thresholdDeg f)) :
    HStar n f = thresholdDeg f :=
  HStar_eq_of_thresholdDeg_le_and_weightedPolynomial (Nat.le_refl _) h

/-! ## Positive weighted open bands -/

/-- The Boolean predicate selecting an open interval of a weighted statistic. -/
noncomputable def weightedOpenBand (lam : Fin n → ℝ) (lo hi : ℝ)
    (bits : Fin n → Bool) : Bool :=
  decide (lo < wT lam bits ∧ wT lam bits < hi)

/-- The quadratic polynomial that is positive precisely inside `(lo, hi)`. -/
noncomputable def openBandPolynomial (lo hi : ℝ) : Polynomial ℝ :=
  (X - C lo) * (C hi - X)

theorem openBandPolynomial_natDegree (lo hi : ℝ) :
    (openBandPolynomial lo hi).natDegree ≤ 2 := by
  unfold openBandPolynomial
  refine Polynomial.natDegree_mul_le.trans ?_
  refine (Nat.add_le_add (Polynomial.natDegree_sub_le _ _)
    (Polynomial.natDegree_sub_le _ _)).trans ?_
  simp

theorem openBandPolynomial_sign {lo hi t : ℝ} (hlohi : lo < hi) :
    0 < (openBandPolynomial lo hi).eval t ↔ lo < t ∧ t < hi := by
  simp only [openBandPolynomial, eval_mul, eval_sub, eval_X, eval_C]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with hpos | hneg
    · constructor <;> linarith
    · exfalso
      linarith
  · rintro ⟨hlt, hth⟩
    exact mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hth)

/-- Every open band in a positive weighted statistic has a uniform quadratic
weighted-polynomial upper certificate. -/
theorem weightedOpenBand_upperBound (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (lo hi : ℝ) (hlohi : lo < hi) :
    PositiveWeightedSignDegLE (weightedOpenBand lam lo hi) 2 := by
  refine ⟨lam, hlam, openBandPolynomial lo hi,
    openBandPolynomial_natDegree lo hi, ?_⟩
  intro bits
  rw [openBandPolynomial_sign hlohi]
  simp [weightedOpenBand]

/-- **Exact weighted-band family.** Any positive weighted open band containing
a two-change symmetric face has head complexity exactly two. -/
theorem HStar_weightedOpenBand_eq_two (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (lo hi : ℝ) (hlohi : lo < hi)
    (hlower : HasSymmetricFaceBound (weightedOpenBand lam lo hi) 2) :
    HStar n (weightedOpenBand lam lo hi) = 2 :=
  HStar_eq_of_symmetricFace_and_weightedPolynomial hlower
    (weightedOpenBand_upperBound lam hlam lo hi hlohi)

/-! ## A globally nonsymmetric member of the family -/

/-- Positive weights `(1, 1, 3)` on three bits. -/
def isolatedXorWeights : Fin 3 → ℝ := ![1, 1, 3]

/-- XOR on the first two bits, gated off by the third bit. -/
def isolatedXor3 (bits : Fin 3 → Bool) : Bool :=
  !bits 2 && xor (bits 0) (bits 1)

theorem isolatedXorWeights_pos (i : Fin 3) : 0 < isolatedXorWeights i := by
  fin_cases i <;> norm_num [isolatedXorWeights]

theorem wT_isolatedXorWeights (bits : Fin 3 → Bool) :
    wT isolatedXorWeights bits =
      (if bits 0 then 1 else 0) + (if bits 1 then 1 else 0) +
        (if bits 2 then 3 else 0) := by
  simp [wT, isolatedXorWeights, Fin.sum_univ_succ]
  ring_nf

/-- `isolatedXor3` is the open band `(1/2, 3/2)` of the weighted statistic
`x₀ + x₁ + 3 x₂`. -/
theorem isolatedXor3_eq_weightedOpenBand :
    isolatedXor3 = weightedOpenBand isolatedXorWeights (1 / 2) (3 / 2) := by
  funext bits
  unfold weightedOpenBand
  rw [wT_isolatedXorWeights]
  cases h0 : bits 0 <;> cases h1 : bits 1 <;> cases h2 : bits 2 <;>
    simp [isolatedXor3, h0, h1, h2] <;> norm_num

/-- The global quadratic upper certificate, inherited from the open-band
family. -/
theorem isolatedXor3_weightedPolynomialUpperBound :
    PositiveWeightedSignDegLE isolatedXor3 2 := by
  rw [isolatedXor3_eq_weightedOpenBand]
  exact weightedOpenBand_upperBound isolatedXorWeights isolatedXorWeights_pos
    (1 / 2) (3 / 2) (by norm_num)

/-- The face where the first two coordinates are free and the third is false. -/
def isolatedXorFace : CoordFace 2 3 where
  free := Fin.castSuccEmb
  base := fun _ ↦ false

@[simp] theorem isolatedXorFace_apply_zero (x : Fin 2 → Bool) :
    isolatedXorFace.apply x 0 = x 0 := by
  simpa [isolatedXorFace] using isolatedXorFace.apply_free x 0

@[simp] theorem isolatedXorFace_apply_one (x : Fin 2 → Bool) :
    isolatedXorFace.apply x 1 = x 1 := by
  simpa [isolatedXorFace] using isolatedXorFace.apply_free x 1

@[simp] theorem isolatedXorFace_apply_two (x : Fin 2 → Bool) :
    isolatedXorFace.apply x 2 = false := by
  apply isolatedXorFace.apply_fixed
  simp [CoordFace.fixedSet, CoordFace.freeSet, isolatedXorFace]

private theorem hammingWeight_fin_two (x : Fin 2 → Bool) :
    hammingWeight x = (if x 0 then 1 else 0) + (if x 1 then 1 else 0) := by
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> decide

theorem isolatedXor3_face (x : Fin 2 → Bool) :
    isolatedXor3 (isolatedXorFace.apply x) =
      symmetricFn (fun j ↦ decide (j = 1)) x := by
  rw [symmetricFn_apply, hammingWeight_fin_two]
  simp only [isolatedXor3, isolatedXorFace_apply_two, Bool.not_false,
    Bool.true_and, isolatedXorFace_apply_zero, isolatedXorFace_apply_one]
  cases x 0 <;> cases x 1 <;> decide

/-- The `x₂ = false` face is the two-bit exact-one profile, hence has two
sign changes. -/
theorem isolatedXor3_hasSymmetricFaceBound :
    HasSymmetricFaceBound isolatedXor3 2 := by
  refine ⟨2, isolatedXorFace, (fun j ↦ decide (j = 1)), ?_, isolatedXor3_face⟩
  rw [signChanges_exact (n := 2) 1 (by decide) (by decide)]

/-- The example is genuinely nonsymmetric: inputs of Hamming weight one can
receive different values. -/
theorem isolatedXor3_not_symmetric :
    ¬ ∃ F : ℕ → Bool, isolatedXor3 = symmetricFn F := by
  rintro ⟨F, hF⟩
  have heval100 : isolatedXor3 ![true, false, false] = true := by decide
  have heval001 : isolatedXor3 ![false, false, true] = false := by decide
  have hweight100 : hammingWeight ![true, false, false] = 1 := by decide
  have hweight001 : hammingWeight ![false, false, true] = 1 := by decide
  have h100 : true = F 1 := by
    have hs : isolatedXor3 ![true, false, false] = F 1 := by
      simpa only [symmetricFn_apply, hweight100] using
        congrFun hF ![true, false, false]
    exact heval100.symm.trans hs
  have h001 : false = F 1 := by
    have hs : isolatedXor3 ![false, false, true] = F 1 := by
      simpa only [symmetricFn_apply, hweight001] using
        congrFun hF ![false, false, true]
    exact heval001.symm.trans hs
  exact Bool.false_ne_true (h001.trans h100.symm)

/-- A concrete nonsymmetric equality obtained by the exact weighted-face
sandwich. -/
theorem HStar_isolatedXor3 : HStar 3 isolatedXor3 = 2 :=
  HStar_eq_of_symmetricFace_and_weightedPolynomial
    isolatedXor3_hasSymmetricFaceBound isolatedXor3_weightedPolynomialUpperBound

/-- The new polynomial invariant is also exactly two on the nonsymmetric
example. -/
theorem positiveWeightedSignDeg_isolatedXor3 :
    positiveWeightedSignDeg isolatedXor3 = 2 := by
  apply Nat.le_antisymm
  · exact positiveWeightedSignDeg_le isolatedXor3_weightedPolynomialUpperBound
  · have hupper := HStar_le_of_computableWithHeadsN
      (positiveWeightedSignDeg_computable isolatedXor3)
    rwa [HStar_isolatedXor3] at hupper

end HeadComplexity
