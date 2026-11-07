module

public import HeadComplexity.BooleanFunction.SignRepresentation
public import HeadComplexity.Data.Bool.Cube
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import HeadComplexity.LinearAlgebra.AffineSpace.Coordinates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Ring

/-!
# An obstruction to sums of two products of affine forms

Antipodal slices give a matrix of mixed differences. For a sum of two products of affine
forms this matrix has rank at most four. The prescribed sign pattern on the slices
forces strict column diagonal dominance and hence full rank.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace HeadComplexity.BooleanFunction

variable {ι κ σ : Type*}

/-- The opposite vertex of the Boolean cube. -/
def bitAntipode (x : ι → Bool) : ι → Bool := fun i ↦ !(x i)

/-- The antipode flips the bit at every coordinate. -/
@[simp]
theorem bitAntipode_apply (x : ι → Bool) (i : ι) : bitAntipode x i = !(x i) :=
  rfl

/-- On each pair of antipodal slices the label reads one coordinate, with the
polarity reversed upon taking either antipode. -/
def HasAntipodalSlices (f : (ι → Bool) → (κ → Bool) → Bool) (slice : ι → κ → Bool) : Prop :=
  ∀ x j,
    f x (slice j) = !x j ∧
    f x (bitAntipode (slice j)) = x j ∧
    f (bitAntipode x) (slice j) = x j ∧
    f (bitAntipode x) (bitAntipode (slice j)) = !x j

private def mixedDifference (g : (ι → Bool) → (κ → Bool) → ℝ)
    (x : ι → Bool) (y : κ → Bool) : ℝ :=
  g x y + g (bitAntipode x) (bitAntipode y) - g x (bitAntipode y) - g (bitAntipode x) y

/-- The mixed difference of a sum is the sum of the mixed differences. -/
private theorem mixedDifference_add (g h : (ι → Bool) → (κ → Bool) → ℝ)
    (x : ι → Bool) (y : κ → Bool) :
    mixedDifference (fun x y ↦ g x y + h x y) x y =
      mixedDifference g x y + mixedDifference h x y := by
  simp only [mixedDifference]
  ring

/-- On a prescribed antipodal slice, the mixed score difference is nonzero and has the sign of
the corresponding signed input bit. -/
private theorem mixedDifference_pos_of_hasAntipodalSlices
    {f : (ι → Bool) → (κ → Bool) → Bool} {slice : ι → κ → Bool}
    {g : (ι → Bool) → (κ → Bool) → ℝ} (hf : HasAntipodalSlices f slice)
    (hg : ∀ x y, 0 < g x y ↔ f x y = true) (x : ι → Bool) (j : ι) :
    0 < Bool.spin ℝ (x j) * mixedDifference g x (slice j) := by
  let y := slice j
  let s (u v : Bool) := g (if u then bitAntipode x else x) (if v then bitAntipode y else y)
  have hs (u v : Bool) : 0 < s u v ↔ xor u v = x j := by
    change 0 < g _ _ ↔ _
    rw [hg]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hf x j
    cases u <;> cases v <;> simp [y, xor, h₁, h₂, h₃, h₄]
  simpa [Bool.spin, mixedDifference, s] using Function.SignRepresents.checkerboard s (x j) hs

section Affine

variable [Fintype ι] [Fintype σ] [DecidableEq σ]

variable (e : ι ⊕ κ ≃ σ)

private def leftPart (L : (σ → ℝ) →ᵃ[ℝ] ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, L.coeff (e (.inl i)) * Bool.cubePoint ℝ x i

private def leftSpin (L : (σ → ℝ) →ᵃ[ℝ] ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, Bool.spin ℝ (x i) * L.coeff (e (.inl i))

/-- Flipping the left input adds the coefficient dot product with the signed bits. -/
private theorem leftPart_antipode (L : (σ → ℝ) →ᵃ[ℝ] ℝ) (x : ι → Bool) :
    leftPart e L (bitAntipode x) = leftPart e L x + leftSpin e L x := by
  simp only [leftPart, leftSpin, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by cases h : x i <;> simp [h]

variable [Fintype κ]

private def rightPart (L : (σ → ℝ) →ᵃ[ℝ] ℝ) (y : κ → Bool) : ℝ :=
  ∑ j, L.coeff (e (.inr j)) * Bool.cubePoint ℝ y j

/-- On a joined input, an affine map is its constant plus independent contributions from the two
coordinate blocks. -/
private theorem affine_apply_join (L : (σ → ℝ) →ᵃ[ℝ] ℝ) (x : ι → Bool) (y : κ → Bool) :
    L (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm)) = L 0 + leftPart e L x + rightPart e L y := by
  rw [L.apply_eq_add_dotProduct, dotProduct, ← e.sum_comp, Fintype.sum_sum_type]
  simp [leftPart, rightPart, Function.comp_apply, add_assoc]

private def rightDiff (L : (σ → ℝ) →ᵃ[ℝ] ℝ) (y : κ → Bool) : ℝ :=
  rightPart e L (bitAntipode y) - rightPart e L y

/-- For a product of two affine maps, the mixed difference consists of the two terms coupling a
change in the left block to a change in the right block. -/
private theorem mixedDifference_affine_mul (L R : (σ → ℝ) →ᵃ[ℝ] ℝ) (x : ι → Bool) (y : κ → Bool) :
    mixedDifference
      (fun x y ↦ L (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm)) *
        R (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm))) x y =
      leftSpin e L x * rightDiff e R y + leftSpin e R x * rightDiff e L y := by
  simp only [mixedDifference, affine_apply_join, leftPart_antipode, rightDiff]
  ring

end Affine

/-- For a sum of two affine products, one matrix of rank at most four gives all slice
differences by multiplication with the signed input vector. -/
private theorem exists_rank_le_four [Fintype ι] [Finite κ] (e : ι ⊕ κ ≃ σ)
    (slice : ι → κ → Bool) (L₁ R₁ L₂ R₂ : (σ → ℝ) →ᵃ[ℝ] ℝ) :
    ∃ M : Matrix ι ι ℝ, M.rank ≤ 4 ∧ ∀ x j,
      mixedDifference (fun x y ↦
        L₁ (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm)) *
          R₁ (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm)) +
        L₂ (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm)) *
          R₂ (Bool.cubePoint ℝ (Sum.elim x y ∘ e.symm))) x (slice j) =
      ((fun i ↦ Bool.spin ℝ (x i)) ᵥ* M) j := by
  classical
  let := Fintype.ofFinite κ
  let := Fintype.ofEquiv (ι ⊕ κ) e
  let U : Matrix ι (Fin 4) ℝ := Matrix.of fun i ↦
    ![L₁.coeff (e (.inl i)), R₁.coeff (e (.inl i)), L₂.coeff (e (.inl i)), R₂.coeff (e (.inl i))]
  let V : Matrix (Fin 4) ι ℝ := Matrix.of fun k j ↦
    ![rightDiff e R₁ (slice j), rightDiff e L₁ (slice j), rightDiff e R₂ (slice j),
      rightDiff e L₂ (slice j)] k
  refine ⟨U * V, (Matrix.rank_mul_le_left U V).trans (by simpa using U.rank_le_card_width),
    fun x j ↦ ?_⟩
  rw [mixedDifference_add, mixedDifference_affine_mul, mixedDifference_affine_mul,
    ← Matrix.vecMul_vecMul]
  simp [U, V, Matrix.vecMul, dotProduct, Fin.sum_univ_four, leftSpin, add_assoc]

/-- If multiplication by a square matrix preserves every input sign in its matching output
coordinate, the matrix has full rank. -/
private theorem card_le_rank_of_forcedSigns [Fintype ι] (M : Matrix ι ι ℝ)
    (hforce : ∀ (x : ι → Bool) j, 0 < Bool.spin ℝ (x j) * ((fun i ↦ Bool.spin ℝ (x i)) ᵥ* M) j) :
    Fintype.card ι ≤ M.rank := by
  classical
  suffices ∀ j, ∑ i ∈ Finset.univ.erase j, ‖M i j‖ < ‖M j j‖ by
    exact (Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2
      (isUnit_iff_ne_zero.2 (det_ne_zero_of_sum_col_lt_diag this)))).symm.le
  intro j
  let x (i : ι) := if i = j then false else if 0 ≤ M i j then true else false
  suffices ∑ i ∈ Finset.univ.erase j, ‖M i j‖ < M j j by
    exact this.trans_le (by simpa only [Real.norm_eq_abs] using le_abs_self (M j j))
  apply sub_pos.mp
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  suffices ∀ i ∈ Finset.univ.erase j, Bool.spin ℝ (x i) * M i j = -‖M i j‖ by
    have hxj : x j = false := by simp [x]
    have hmin := hforce x j
    simp only [hxj, Bool.spin_false, one_mul, Matrix.vecMul, dotProduct] at hmin
    rw [← Finset.add_sum_erase Finset.univ (fun i ↦ Bool.spin ℝ (x i) * M i j)
      (Finset.mem_univ j)] at hmin
    simpa only [Finset.sum_congr rfl this, hxj, Bool.spin_false, one_mul] using hmin
  intro i hi
  by_cases h : 0 ≤ M i j
  · simp [x, Finset.ne_of_mem_erase hi, h, Real.norm_eq_abs, abs_of_nonneg h]
  · simp [x, Finset.ne_of_mem_erase hi, h, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h)]

/-- An antipodal-slice pattern on more than four left coordinates rules out a sign
representation by a sum of two products of affine forms. -/
theorem not_signRepresents_twoAffineProducts [Fintype ι] [Finite κ]
    (e : ι ⊕ κ ≃ σ) (f : (σ → Bool) → Bool) (slice : ι → κ → Bool)
    (hcard : 4 < Fintype.card ι)
    (hslice : HasAntipodalSlices (fun x y ↦ f (Sum.elim x y ∘ e.symm)) slice)
    (L₁ R₁ L₂ R₂ : (σ → ℝ) →ᵃ[ℝ] ℝ) :
    ¬ Function.SignRepresents (fun z ↦
      L₁ (Bool.cubePoint ℝ z) * R₁ (Bool.cubePoint ℝ z) +
        L₂ (Bool.cubePoint ℝ z) * R₂ (Bool.cubePoint ℝ z)) f := by
  classical
  intro hsign
  obtain ⟨M, hrank, hM⟩ := exists_rank_le_four e slice L₁ R₁ L₂ R₂
  refine hcard.not_ge ((card_le_rank_of_forcedSigns M fun x j ↦ ?_).trans hrank)
  rw [← hM]
  exact mixedDifference_pos_of_hasAntipodalSlices hslice
    (fun u v ↦ hsign (Sum.elim u v ∘ e.symm)) x j

end HeadComplexity.BooleanFunction
