module

public import HeadComplexity.Attention.Complexity.Basic
import HeadComplexity.Attention.Face
public import HeadComplexity.Attention.ThresholdDegree

/-!
# The zero-head and one-head levels

Zero heads compute the constant Boolean functions. One head computes the functions
with affine sign representations on the cube.
-/

@[expose] public section

open scoped BigOperators

namespace Function

/-- A Boolean function is an affine threshold if its true inputs are exactly the
Boolean vertices where some affine map is positive. -/
def IsAffineThreshold {ι : Type*} (f : (ι → Bool) → Bool) : Prop :=
  ∃ a : (ι → ℝ) →ᵃ[ℝ] ℝ, SignRepresents (a ∘ Bool.cubePoint ℝ) f

end Function

namespace HeadComplexity

variable {n : ℕ} {f : (Fin n → Bool) → Bool}

/-- A Boolean function is computable with zero heads exactly when it is constant. -/
theorem computableWithHeads_zero_iff : ComputableWithHeads f 0 ↔ ∀ x y, f x = f y := by
  constructor
  · rintro ⟨s, hs, hf⟩ x y
    obtain ⟨c, rfl⟩ := hasHeadScore_zero_iff.mp hs
    exact Bool.eq_iff_iff.mpr ((hf x).symm.trans (hf y))
  · intro hf
    let x₀ : Fin n → Bool := fun _ ↦ false
    let c : ℝ := if f x₀ then 1 else -1
    refine ⟨Function.const _ c, hasHeadScore_zero_iff.mpr ⟨c, rfl⟩, fun x ↦ ?_⟩
    change 0 < (if f x₀ then (1 : ℝ) else -1) ↔ f x = true
    rw [hf x x₀]
    cases f x₀ <;> simp

/-- A Boolean function has threshold degree at most one exactly when an affine map represents
its signs on the cube. -/
theorem thresholdDegreeLE_one_iff_isAffineThreshold :
    ThresholdDegreeLE f 1 ↔ Function.IsAffineThreshold f := by
  constructor
  · rintro ⟨p, hp, hs⟩
    obtain ⟨a, rfl⟩ := p.exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one hp
    exact ⟨a, fun x ↦ by simpa only [AffineMap.eval_toMvPolynomial, Function.comp_apply] using hs x⟩
  · rintro ⟨a, ha⟩
    exact ⟨a.toMvPolynomial, a.totalDegree_toMvPolynomial_le_one, fun x ↦ by
      simpa only [AffineMap.eval_toMvPolynomial, Function.comp_apply] using ha x⟩

/-- A Boolean function is computable with one head exactly when it is an affine threshold on the
cube. -/
theorem computableWithHeads_one_iff : ComputableWithHeads f 1 ↔ Function.IsAffineThreshold f := by
  constructor
  · exact fun h ↦ thresholdDegreeLE_one_iff_isAffineThreshold.mp h.thresholdDegreeLE
  · rintro ⟨a, ha⟩
    let d := (AffineMap.constCoeffEquiv ℝ (Fin n)).symm (1, fun _ ↦ 1)
    have hd (x : Fin n → Bool) : 0 < d (Bool.cubePoint ℝ x) := by
      change 0 < (AffineMap.constCoeffEquiv ℝ (Fin n)).symm _ (Bool.cubePoint ℝ x)
      rw [AffineMap.constCoeffEquiv_symm_apply]
      simp only [dotProduct, one_mul]
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
    let r : Attention.AffineFraction n := ⟨a, d⟩
    refine computableWithHeads_iff_exists_affineFractions.mpr
      ⟨0, fun _ ↦ r, fun _ ↦ ⟨hd, Or.inl fun i ↦ by simp [r, d]⟩, fun x ↦ ?_⟩
    simp only [Fin.sum_univ_one, zero_add]
    change 0 < a (Bool.cubePoint ℝ x) / d (Bool.cubePoint ℝ x) ↔ f x = true
    rw [lt_div_iff₀ (hd x), zero_mul]
    exact ha x

/-- The functions with minimum head count zero are exactly the constant functions. -/
theorem headComplexity_eq_zero_iff : headComplexity f = 0 ↔ ∀ x y, f x = f y := by
  rw [← Nat.le_zero, headComplexity_le_iff_computableWithHeads, computableWithHeads_zero_iff]

/-- The functions with minimum head count one are exactly the nonconstant affine thresholds. -/
theorem headComplexity_eq_one_iff :
    headComplexity f = 1 ↔ Function.IsAffineThreshold f ∧ ¬(∀ x y, f x = f y) := by
  rw [headComplexity_eq_succ_iff (H := 0), Nat.zero_add,
    computableWithHeads_one_iff, computableWithHeads_zero_iff]

/-- An affine map has equal sums of values on the two pairs of opposite corners of a Boolean
face. -/
private theorem affine_face_antipode (a : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) :
    a (Bool.cubePoint ℝ (Bool.face x i j false false)) +
        a (Bool.cubePoint ℝ (Bool.face x i j true true)) =
      a (Bool.cubePoint ℝ (Bool.face x i j false true)) +
        a (Bool.cubePoint ℝ (Bool.face x i j true false)) := by
  let p u v := Bool.cubePoint ℝ (Bool.face x i j u v)
  change a (p false false) + a (p true true) = a (p false true) + a (p true false)
  rw [a.apply_eq_add_dotProduct (p false false), a.apply_eq_add_dotProduct (p true true),
    a.apply_eq_add_dotProduct (p false true), a.apply_eq_add_dotProduct (p true false)]
  exact Bool.add_diag_eq_add_antidiag_of_exists_additive_split
    (Bool.exists_additive_split_face (fun k b ↦ a.coeff k * (b.toNat : ℝ)) (a 0) x hij)

/-- The two diagonal pairs of a checkerboard face exclude one-head computation. -/
theorem not_computableWithHeads_one_of_checkerboard (x : Fin n → Bool) {i j : Fin n}
    (hij : i ≠ j) (b : Bool) (hf : ∀ u v, f (Bool.face x i j u v) = true ↔ xor u v = b) :
    ¬ComputableWithHeads f 1 := by
  intro hc
  obtain ⟨a, ha⟩ := computableWithHeads_one_iff.mp hc
  let s (u v : Bool) := a (Bool.cubePoint ℝ (Bool.face x i j u v))
  suffices s false false + s true true = s false true + s true false by
    simpa only [← sub_add_eq_sub_sub, this, sub_self, mul_zero, lt_self_iff_false] using
      Function.SignRepresents.checkerboard s b (fun u v ↦ (ha _).trans (hf u v))
  exact affine_face_antipode a x hij

/-- A checkerboard on any two-coordinate face forces the function to have head complexity at
least two. -/
theorem two_le_headComplexity_of_checkerboard (x : Fin n → Bool) {i j : Fin n}
    (hij : i ≠ j) (b : Bool) (hf : ∀ u v, f (Bool.face x i j u v) = true ↔ xor u v = b) :
    2 ≤ headComplexity f :=
  Nat.succ_le_of_lt (lt_headComplexity_iff_not_computableWithHeads.mpr
    (not_computableWithHeads_one_of_checkerboard x hij b hf))

end HeadComplexity
