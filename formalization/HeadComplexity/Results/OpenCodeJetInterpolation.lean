import HeadComplexity.Atoms.OpenCodePartition
import HeadComplexity.Results.PositivePairCover
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

set_option linter.style.header false

/-! The explicit open-code construction gives a nonsingular square selection
of reciprocal-cube degree-two numerator columns at positive affine forms.
This auxiliary theorem makes no assertion about the number of actual heads. -/
namespace HeadComplexity.OpenCodeJetInterpolation

open OpenCodePartition Finset
open scoped BigOperators symmDiff

abbrev Index (r : ℕ) := Address r ⊕ Address r
abbrev Centers (r : ℕ) := Code r × Code r

noncomputable def wordLeft {r : ℕ} (x : Finset (Index r)) : Word r :=
  fun g ↦ if Sum.inl g ∈ x then 1 else 0

noncomputable def wordRight {r : ℕ} (x : Finset (Index r)) : Word r :=
  fun g ↦ if Sum.inr g ∈ x then 1 else 0

noncomputable def owner {r : ℕ} (x : Finset (Index r)) : Centers r :=
  (repair (wordLeft x), repair (wordRight x))

noncomputable def center {r : ℕ} (v : Centers r) : Finset (Index r) :=
  Finset.univ.filter (fun i ↦ Sum.elim v.1.val v.2.val i = 1)

noncomputable def pair {r : ℕ} (x : Finset (Index r)) : Finset (Index r) :=
  {Sum.inl (syndrome (wordLeft x)), Sum.inr (syndrome (wordRight x))}

theorem pair_card {r : ℕ} (x : Finset (Index r)) : (pair x).card = 2 := by
  classical
  simp [pair]

theorem target_pair {r : ℕ} (x : Finset (Index r)) :
    x ∆ center (owner x) = pair x := by
  classical
  ext i
  rcases i with g | g
  · by_cases hg : g = syndrome (wordLeft x) <;> by_cases hx : Sum.inl g ∈ x
    all_goals
      simp_all [Finset.mem_symmDiff, center, owner, repair, OpenCodePartition.flip,
        wordLeft, pair, eq_comm]
  · by_cases hg : g = syndrome (wordRight x) <;> by_cases hx : Sum.inr g ∈ x
    all_goals
      simp_all [Finset.mem_symmDiff, center, owner, repair, OpenCodePartition.flip,
        wordRight, pair, eq_comm]

noncomputable def selectedNumerator {r : ℕ} (x y : Finset (Index r)) : ℝ :=
  PositivePairCover.numerator center owner pair x y

theorem selectedNumerator_product {r : ℕ} (x y : Finset (Index r)) :
    selectedNumerator x y =
      (if Sum.inl (syndrome (wordLeft y)) ∈ x ∆ center (owner y) then (1 : ℝ) else 0) *
      (if Sum.inr (syndrome (wordRight y)) ∈ x ∆ center (owner y) then (1 : ℝ) else 0) := by
  classical
  exact FiniteFlipIsolation.numerator_pair_product _ _ _ _

/-- An end-to-end positive-coefficient, full-rank finite-matrix theorem for
every pair of power-of-two blocks. The numerators are products of two literals. -/
theorem exists_positive_full_rank (r : ℕ) :
    ∃ b₀ : Centers r → ℝ, ∃ b : Centers r → Index r → ℝ,
      (∀ v, 0 < b₀ v) ∧ (∀ v i, 0 < b v i) ∧
      (Matrix.of (fun x y : Finset (Index r) ↦ selectedNumerator x y /
        (b₀ (owner y) + ∑ i : Index r, b (owner y) i *
          (if i ∈ x then (1 : ℝ) else 0)) ^ 3)).det ≠ 0 := by
  classical
  exact PositivePairCover.exists_positive_affine_pair_matrix center owner pair pair_card target_pair

/-- The selected columns interpolate every real table on the Boolean cube. -/
theorem exists_positive_interpolation (r : ℕ) :
    ∃ b₀ : Centers r → ℝ, ∃ b : Centers r → Index r → ℝ,
      (∀ v, 0 < b₀ v) ∧ (∀ v i, 0 < b v i) ∧
      ∀ F : Finset (Index r) → ℝ, ∃ weights : Finset (Index r) → ℝ,
        ∀ x, F x = ∑ y, weights y * selectedNumerator x y /
          (b₀ (owner y) + ∑ i : Index r, b (owner y) i *
            (if i ∈ x then (1 : ℝ) else 0)) ^ 3 := by
  classical
  obtain ⟨b₀, b, hb₀, hb, hdet⟩ := exists_positive_full_rank r
  refine ⟨b₀, b, hb₀, hb, ?_⟩
  intro F
  let M : Matrix (Finset (Index r)) (Finset (Index r)) ℝ :=
    fun x y ↦ selectedNumerator x y /
      (b₀ (owner y) + ∑ i : Index r, b (owner y) i *
        (if i ∈ x then (1 : ℝ) else 0)) ^ 3
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
      ⟨M⁻¹, Matrix.mul_nonsing_inv M hunit⟩
  obtain ⟨weights, hweights⟩ := hsurj F
  refine ⟨weights, fun x ↦ ?_⟩
  have heq := congrFun hweights x
  rw [← heq]
  simp only [Matrix.mulVec, dotProduct, M]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem card_index (r : ℕ) : Fintype.card (Index r) = 2 * 2 ^ r := by
  simp [Index, Address, Fintype.card_sum, ZMod.card, two_mul]

/-- The number of centers is exactly four times cube size divided by the
square of the coordinate count, written without division. -/
theorem center_budget (r : ℕ) :
    Fintype.card (Centers r) * (Fintype.card (Index r)) ^ 2 =
      4 * Fintype.card (Finset (Index r)) := by
  classical
  rw [Fintype.card_finset, card_index]
  have hc := OpenCodePartition.card_product_code_mul r
  change Fintype.card (Centers r) * (2 ^ r) ^ 2 = 2 ^ (2 * 2 ^ r) at hc
  calc
    _ = 4 * (Fintype.card (Centers r) * (2 ^ r) ^ 2) := by ring
    _ = _ := by rw [hc]

end HeadComplexity.OpenCodeJetInterpolation
