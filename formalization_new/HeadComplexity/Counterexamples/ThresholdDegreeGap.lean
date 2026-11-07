module

public import HeadComplexity.Attention.Complexity.OneHead
public import HeadComplexity.Attention.ThresholdDegree
public import HeadComplexity.BooleanFunction.AffineProducts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A ten-bit gap between threshold degree and head complexity

An explicit quadratic on two blocks of five signed bits has threshold degree two.
Its antipodal slices rule out computation with two heads.
-/

@[expose] public section

open scoped BigOperators

namespace HeadComplexity.Counterexamples

open MvPolynomial
open BooleanFunction (HasAntipodalSlices bitAntipode not_signRepresents_twoAffineProducts)

private def quadratic {R : Type*} [CommRing R] (x y : Fin 5 → R) : R :=
  (∑ i, x i) * (∑ i, y i) - 3 * ∑ i, x i * y i

/-- A ring homomorphism commutes with the quadratic expression on the two blocks. -/
private theorem map_quadratic {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (x y : Fin 5 → R) :
    φ (quadratic x y) = quadratic (φ ∘ x) (φ ∘ y) := by
  simp [quadratic, map_ofNat]

/-- The quadratic score of the ten-bit example, over a commutative ring. -/
@[no_expose]
def f10Score (R : Type*) [CommRing R] (z : Fin 10 → Bool) : R :=
  quadratic (fun i ↦ Bool.spin R (z (Fin.castAdd 5 i)))
    (fun i ↦ Bool.spin R (z (Fin.natAdd 5 i)))

/-- The score is the product of the signed block sums minus three times their dot product. -/
theorem f10Score_apply (R : Type*) [CommRing R] (z : Fin 10 → Bool) :
    f10Score R z =
      (∑ i : Fin 5, Bool.spin R (z (Fin.castAdd 5 i))) *
        (∑ i : Fin 5, Bool.spin R (z (Fin.natAdd 5 i))) -
      3 * ∑ i : Fin 5, Bool.spin R (z (Fin.castAdd 5 i)) * Bool.spin R (z (Fin.natAdd 5 i)) := by
  rw [f10Score, quadratic]

/-- A ring homomorphism takes the ten-bit score over one ring to the same score over the target
ring. -/
theorem map_f10Score {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (z : Fin 10 → Bool) : φ (f10Score R z) = f10Score S z := by
  rw [f10Score, f10Score, map_quadratic]
  congr 1 <;> funext i <;> simp [Bool.spin_eq_one_sub, map_ofNat]

/-- The Boolean function defined by the positive set of the ten-bit quadratic. -/
noncomputable def f10 (z : Fin 10 → Bool) : Bool :=
  if 0 < f10Score ℝ z then true else false

/-- The ten-bit function is true exactly where its real quadratic score is positive. -/
@[simp] theorem f10_eq_true (z : Fin 10 → Bool) : f10 z = true ↔ 0 < f10Score ℝ z := by
  simp [f10]

/-- Substituting one minus twice each integer coordinate into the quadratic gives ten plus four
times an integer expression in the coordinates. -/
private theorem quadratic_one_sub_two_mul (x y : Fin 5 → ℤ) :
    quadratic (fun i ↦ 1 - 2 * x i) (fun i ↦ 1 - 2 * y i) =
      10 + 4 * ((∑ i, x i) * (∑ i, y i) - (∑ i, x i) - (∑ i, y i) -
        3 * ∑ i, x i * y i) := by
  have hxy :
      (∑ i, (1 - 2 * x i) * (1 - 2 * y i)) =
        ∑ i, (1 - 2 * x i - 2 * y i + 4 * (x i * y i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [quadratic, hxy]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  norm_num
  ring

/-- The integer score is always two modulo four. -/
theorem f10Score_mod_four (z : Fin 10 → Bool) : f10Score ℤ z % 4 = 2 := by
  unfold f10Score
  simp_rw [Bool.spin_eq_one_sub]
  rw [quadratic_one_sub_two_mul, Int.add_mul_emod_self_left]
  rfl

/-- The real quadratic is nonzero at every Boolean vertex. -/
theorem f10Score_ne_zero (z : Fin 10 → Bool) : f10Score ℝ z ≠ 0 := by
  intro h
  suffices f10Score ℤ z = 0 by simpa [this] using f10Score_mod_four z
  exact Int.cast_eq_zero.mp ((map_f10Score (Int.castRingHom ℝ) z).trans h)

private noncomputable def spinPolynomial (j : Fin 10) : MvPolynomial (Fin 10) ℝ :=
  C 1 - C 2 * X j

/-- The one-coordinate polynomial evaluates to the signed encoding of that input bit. -/
private theorem eval_spinPolynomial (z : Fin 10 → Bool) (j : Fin 10) :
    eval (Bool.cubePoint ℝ z) (spinPolynomial j) = Bool.spin ℝ (z j) := by
  simp [spinPolynomial, Bool.spin_eq_one_sub]

/-- The polynomial for a signed bit has total degree at most one. -/
private theorem totalDegree_spinPolynomial_le (j : Fin 10) :
    (spinPolynomial j).totalDegree ≤ 1 := by
  refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
  exact (totalDegree_mul _ _).trans (by simp)

private noncomputable def f10Polynomial : MvPolynomial (Fin 10) ℝ :=
  quadratic (fun i ↦ spinPolynomial (Fin.castAdd 5 i))
    (fun i ↦ spinPolynomial (Fin.natAdd 5 i))

/-- On the Boolean cube, the multivariate polynomial evaluates to the ten-bit quadratic score. -/
private theorem eval_f10Polynomial (z : Fin 10 → Bool) :
    eval (Bool.cubePoint ℝ z) f10Polynomial = f10Score ℝ z := by
  rw [f10Polynomial, f10Score, map_quadratic]
  congr 1 <;> funext i <;> exact eval_spinPolynomial z _

/-- The polynomial for the ten-bit score has total degree at most two. -/
private theorem totalDegree_f10Polynomial_le : f10Polynomial.totalDegree ≤ 2 := by
  unfold f10Polynomial quadratic
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add
      (totalDegree_finsetSum_le fun i _ ↦ totalDegree_spinPolynomial_le _)
      (totalDegree_finsetSum_le fun i _ ↦ totalDegree_spinPolynomial_le _))
  · refine (totalDegree_mul _ _).trans ?_
    change (C (3 : ℝ)).totalDegree + _ ≤ _
    rw [totalDegree_C, zero_add]
    exact totalDegree_finsetSum_le fun i _ ↦
      (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_spinPolynomial_le _)
        (totalDegree_spinPolynomial_le _))

/-- The explicit quadratic gives a degree-two sign representation of the ten-bit function. -/
theorem f10_thresholdDegreeLE_two : ThresholdDegreeLE f10 2 := by
  refine ⟨f10Polynomial, totalDegree_f10Polynomial_le, fun z ↦ ?_⟩
  change 0 < eval (Bool.cubePoint ℝ z) f10Polynomial ↔ f10 z = true
  rw [eval_f10Polynomial]
  exact (f10_eq_true z).symm

private def join (x y : Fin 5 → Bool) : Fin 10 → Bool :=
  Sum.elim x y ∘ (finSumFinEquiv (m := 5) (n := 5)).symm

/-- Evaluating the score on a joined input is the same as applying the quadratic to the signed
encodings of its two blocks. -/
private theorem f10Score_join {R : Type*} [CommRing R] (x y : Fin 5 → Bool) :
    f10Score R (join x y) = quadratic (Bool.spin R ∘ x) (Bool.spin R ∘ y) := by
  simp only [f10Score, join, Function.comp_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr]
  rfl

private def checkerBase : Fin 10 → Bool :=
  ![false, false, false, true, true, false, false, true, false, true]

/-- Updating the chosen face coordinates varies the first bit in each block. -/
private theorem checkerBase_face (a b : Bool) :
    Bool.face checkerBase 0 5 a b =
      join ![a, false, false, true, true] ![b, false, true, false, true] := by
  funext i
  fin_cases i <;> rfl

/-- On the chosen two-coordinate face, the ten-bit function is XOR of the two free bits. -/
private theorem f10_checkerboard (a b : Bool) :
    f10 (Bool.face checkerBase 0 5 a b) = true ↔ xor a b = true := by
  rw [checkerBase_face, f10_eq_true, f10Score_join]
  cases a <;> cases b <;> norm_num [quadratic, Fin.sum_univ_succ, xor]

/-- The XOR face excludes any sign representation of the ten-bit function by a polynomial of
degree at most one. -/
private theorem f10_not_thresholdDegreeLE_one : ¬ThresholdDegreeLE f10 1 := by
  rintro ⟨p, hp, hs⟩
  obtain ⟨a, rfl⟩ := p.exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one hp
  refine not_computableWithHeads_one_of_checkerboard checkerBase
    (show (0 : Fin 10) ≠ 5 by norm_num [Fin.ext_iff]) true f10_checkerboard ?_
  exact computableWithHeads_one_iff.mpr ⟨a, fun z ↦ by
    simpa only [AffineMap.eval_toMvPolynomial, Function.comp_apply] using hs z⟩

/-- The ten-bit counterexample has threshold degree two. -/
theorem thresholdDegree_f10 : thresholdDegree f10 = 2 := by
  refine le_antisymm f10_thresholdDegreeLE_two.thresholdDegree_le ?_
  exact Nat.succ_le_of_lt (lt_of_not_ge fun h ↦
    f10_not_thresholdDegreeLE_one (thresholdDegree_le_iff.mp h))

/-- Flipping all the bits in the left block negates the score. -/
private theorem f10Score_join_not_left (x y : Fin 5 → Bool) :
    f10Score ℝ (join (bitAntipode x) y) = -f10Score ℝ (join x y) := by
  simp only [f10Score_join, quadratic, Function.comp_apply, BooleanFunction.bitAntipode_apply,
    Bool.spin_not,
    Finset.sum_neg_distrib, neg_mul]
  ring

/-- Flipping all the bits in the right block negates the score. -/
private theorem f10Score_join_not_right (x y : Fin 5 → Bool) :
    f10Score ℝ (join x (bitAntipode y)) = -f10Score ℝ (join x y) := by
  simp only [f10Score_join, quadratic, Function.comp_apply, BooleanFunction.bitAntipode_apply,
    Bool.spin_not,
    Finset.sum_neg_distrib, mul_neg]
  ring

private def slice (j i : Fin 5) : Bool := if i = j then true else false

/-- The signed slice vector is one everywhere except at the selected coordinate, where it is
negative one. -/
private theorem spin_slice (j i : Fin 5) :
    Bool.spin ℝ (slice j i) = 1 - if i = j then 2 else 0 := by
  by_cases h : i = j <;> norm_num [slice, h]

/-- On the selected right-block slice, the score is six times the signed bit at the matching
left coordinate. -/
private theorem f10Score_slice (x : Fin 5 → Bool) (j : Fin 5) :
    f10Score ℝ (join x (slice j)) = 6 * Bool.spin ℝ (x j) := by
  simp only [f10Score_join, quadratic, Function.comp_apply, spin_slice, mul_sub, mul_ite,
    mul_one, mul_zero, Finset.sum_sub_distrib]
  simp
  ring

/-- The five concrete slices and their block flips have the signs required by the
antipodal-slice obstruction. -/
private theorem f10_hasAntipodalSlices :
    HasAntipodalSlices (fun x y ↦ f10 (join x y)) slice := by
  intro x j
  cases hx : x j <;>
    norm_num [f10, f10Score_join_not_left, f10Score_join_not_right,
      f10Score_slice, hx]

/-- The ten-bit function has no sign representation by a sum of two products of affine
polynomials. -/
theorem f10_no_cleared_affine (L₁ R₁ L₂ R₂ : MvPolynomial (Fin 10) ℝ)
    (hL₁ : L₁.totalDegree ≤ 1) (hR₁ : R₁.totalDegree ≤ 1)
    (hL₂ : L₂.totalDegree ≤ 1) (hR₂ : R₂.totalDegree ≤ 1) :
    ¬ Function.SignRepresents (fun z ↦ eval (Bool.cubePoint ℝ z) (L₁ * R₁ + L₂ * R₂)) f10 := by
  obtain ⟨l₁, rfl⟩ := L₁.exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one hL₁
  obtain ⟨r₁, rfl⟩ := R₁.exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one hR₁
  obtain ⟨l₂, rfl⟩ := L₂.exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one hL₂
  obtain ⟨r₂, rfl⟩ := R₂.exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one hR₂
  intro h
  apply not_signRepresents_twoAffineProducts (finSumFinEquiv (m := 5) (n := 5)) f10 slice
    (by simp) f10_hasAntipodalSlices l₁ r₁ l₂ r₂
  intro z
  simpa only [map_add, map_mul, AffineMap.eval_toMvPolynomial] using h z

/-- No two-head model computes the ten-bit function. -/
theorem f10_not_computableWithHeads_two : ¬ComputableWithHeads f10 2 := by
  intro h
  obtain ⟨L₁, R₁, L₂, R₂, hL₁, hR₁, hL₂, hR₂, hp⟩ := h.exists_signRepresents_twoAffineProducts
  exact f10_no_cleared_affine L₁ R₁ L₂ R₂ hL₁ hR₁ hL₂ hR₂ hp

/-- The ten-bit function requires at least three heads. -/
theorem three_le_headComplexity_f10 : 3 ≤ headComplexity f10 :=
  Nat.succ_le_of_lt (lt_headComplexity_iff_not_computableWithHeads.mpr
    f10_not_computableWithHeads_two)

/-- Threshold degree can be strictly smaller than head complexity. -/
theorem thresholdDegree_f10_lt_headComplexity : thresholdDegree f10 < headComplexity f10 := by
  rw [thresholdDegree_f10]
  exact three_le_headComplexity_f10

end HeadComplexity.Counterexamples
