module

public import HeadComplexity.Attention.Basic
public import HeadComplexity.Data.Bool.Cube
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Basic

/-!
# Attention on a two-coordinate face

At the fixed query position, the contribution of an input position depends only on the bit
at that position. Thus both the vector numerator and the scalar denominator split additively
on a two-coordinate face.
-/

@[expose] public section

open scoped BigOperators

/-- Two intersecting segments cannot lie on opposite sides of a linear threshold. -/
theorem LinearMap.not_separates_of_segment_inter_nonempty {E : Type*}
    [AddCommGroup E] [Module ℝ E] (L : E →ₗ[ℝ] ℝ) {a b c d : E} {τ : ℝ}
    (h : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ¬ (L a ≤ τ ∧ L b ≤ τ ∧ τ < L c ∧ τ < L d) := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rintro ⟨ha, hb, hc, hd⟩
  exact (show L z ≤ τ from (convex_halfSpace_le L.isLinear τ).segment_subset ha hb hz₁).not_gt
    ((convex_halfSpace_gt L.isLinear τ).segment_subset hc hd hz₂)

namespace Bool

/-- A sum of position-local terms on a two-coordinate face splits into one term for each free
bit and a constant. -/
theorem exists_additive_split_face {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A] (g : ι → Bool → A) (c : A)
    (x : ι → Bool) {i j : ι} (hij : i ≠ j) :
    ∃ (a₀ b₀ : Bool → A) (c₀ : A), ∀ a b : Bool,
      c + (∑ k, g k (Bool.face x i j a b k)) = a₀ a + b₀ b + c₀ := by
  refine ⟨g i, g j, c + ∑ k ∈ (Finset.univ.erase j).erase i, g k (x k), ?_⟩
  intro a b
  rw [Bool.face, Finset.sum_apply_update_of_mem (Finset.mem_univ j),
    Finset.sum_apply_update_of_mem (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)]
  ac_rfl

/-- For a function that splits additively by bit, the values on opposite corners have equal sums
on both diagonals. -/
theorem add_diag_eq_add_antidiag_of_exists_additive_split {A : Type*} [AddCommMonoid A]
    {g : Bool → Bool → A} (h : ∃ (a₀ b₀ : Bool → A) (c : A), ∀ a b,
      g a b = a₀ a + b₀ b + c) :
    g false false + g true true = g false true + g true false := by
  obtain ⟨a₀, b₀, c, h⟩ := h
  simp only [h]
  ac_rfl

end Bool

namespace HeadComplexity.Attention

/-- Combining two numerators and dividing by the sum of their positive denominators gives a
point in the open segment between the separate normalized values. -/
private theorem inv_smul_add_mem_openSegment {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u v : E) :
    (a + b)⁻¹ • (u + v) ∈ openSegment ℝ (a⁻¹ • u) (b⁻¹ • v) := by
  refine mem_openSegment_iff_div.mpr ⟨a, b, ha, hb, ?_⟩
  simp only [div_eq_inv_mul, mul_smul, smul_inv_smul₀ ha.ne', smul_inv_smul₀ hb.ne', smul_add]

namespace Model

variable {n H d m : ℕ} (M : Model n H d m)

/-- The softmax denominator splits into a fixed query weight and one term for each input
position, depending only on that position's bit. -/
theorem denominator_apply (h : Fin H) (x : Fin n → Bool) :
    M.denominator h x = M.weight h (fun _ ↦ false) none +
      ∑ i, M.weight h (fun _ ↦ x i) (some i) := by
  simp only [denominator, Fintype.sum_option, weight, logit, embed_none, embed_some]

/-- The softmax numerator splits into a fixed query contribution and one weighted value for each
input position, depending only on that position's bit. -/
theorem numerator_apply (h : Fin H) (x : Fin n → Bool) :
    M.numerator h x = M.weight h (fun _ ↦ false) none • M.value h (M.embed (fun _ ↦ false) none) +
      ∑ i, M.weight h (fun _ ↦ x i) (some i) • M.value h (M.embed (fun _ ↦ x i) (some i)) := by
  simp only [numerator, Fintype.sum_option, weight, logit, embed_none, embed_some]

/-- On a two-coordinate face, the denominator is the sum of a term for each free bit and a
constant. -/
theorem denominator_additive_split (h : Fin H) (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ (a₀ b₀ : Bool → ℝ) (c : ℝ), ∀ a b,
      M.denominator h (Bool.face x i j a b) = a₀ a + b₀ b + c := by
  simpa only [M.denominator_apply h] using
    Bool.exists_additive_split_face (fun i b ↦ M.weight h (fun _ ↦ b) (some i))
      (M.weight h (fun _ ↦ false) none) x hij

/-- On a two-coordinate face, the vector numerator is the sum of a term for each free bit and a
constant. -/
theorem numerator_additive_split (h : Fin H) (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ (a₀ b₀ : Bool → EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin m)), ∀ a b,
      M.numerator h (Bool.face x i j a b) = a₀ a + b₀ b + c := by
  simpa only [M.numerator_apply h] using
    Bool.exists_additive_split_face
      (fun i b ↦ M.weight h (fun _ ↦ b) (some i) • M.value h (M.embed (fun _ ↦ b) (some i)))
      (M.weight h (fun _ ↦ false) none • M.value h (M.embed (fun _ ↦ false) none)) x hij

/-- The denominators on one diagonal of a Boolean face sum to the same value as those on the
other diagonal. -/
theorem restricted_denominator_antipode (h : Fin H) (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) :
    M.denominator h (Bool.face x i j false false) + M.denominator h (Bool.face x i j true true) =
      M.denominator h (Bool.face x i j false true) + M.denominator h (Bool.face x i j true false) :=
  Bool.add_diag_eq_add_antidiag_of_exists_additive_split (M.denominator_additive_split h x hij)

/-- The numerators on one diagonal of a Boolean face sum to the same vector as those on the
other diagonal. -/
theorem restricted_numerator_antipode (h : Fin H) (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) :
    M.numerator h (Bool.face x i j false false) + M.numerator h (Bool.face x i j true true) =
      M.numerator h (Bool.face x i j false true) + M.numerator h (Bool.face x i j true false) :=
  Bool.add_diag_eq_add_antidiag_of_exists_additive_split (M.numerator_additive_split h x hij)

/-- On a two-coordinate face, the two open segments joining opposite head outputs intersect. -/
theorem openSegment_headOutput_inter_nonempty (h : Fin H) (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) :
    (openSegment ℝ (M.headOutput h (Bool.face x i j false false))
        (M.headOutput h (Bool.face x i j true true)) ∩
      openSegment ℝ (M.headOutput h (Bool.face x i j false true))
        (M.headOutput h (Bool.face x i j true false))).Nonempty := by
  let D a b := M.denominator h (Bool.face x i j a b)
  let N a b := M.out h (M.numerator h (Bool.face x i j a b))
  have hmem (a b c e : Bool) : (D a b + D c e)⁻¹ • (N a b + N c e) ∈
      openSegment ℝ (M.headOutput h (Bool.face x i j a b))
        (M.headOutput h (Bool.face x i j c e)) := by
    simpa only [headOutput, map_smul] using
      inv_smul_add_mem_openSegment (M.denominator_pos h (Bool.face x i j a b))
        (M.denominator_pos h (Bool.face x i j c e)) (N a b) (N c e)
  refine ⟨_, hmem false false true true, ?_⟩
  dsimp only [D, N]
  rw [M.restricted_denominator_antipode h x hij, ← map_add,
    M.restricted_numerator_antipode h x hij, map_add]
  exact hmem false true true false

/-- A linear readout cannot put the diagonal of a single head below its threshold
and the antidiagonal strictly above it. -/
theorem not_separates_headOutput_face (h : Fin H) (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j)
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ) (τ : ℝ) :
    ¬ (L (M.headOutput h (Bool.face x i j false false)) ≤ τ ∧
      L (M.headOutput h (Bool.face x i j true true)) ≤ τ ∧
      τ < L (M.headOutput h (Bool.face x i j false true)) ∧
      τ < L (M.headOutput h (Bool.face x i j true false))) := by
  apply L.not_separates_of_segment_inter_nonempty
  obtain ⟨z, hz₁, hz₂⟩ := M.openSegment_headOutput_inter_nonempty h x hij
  exact ⟨z, openSegment_subset_segment ℝ _ _ hz₁, openSegment_subset_segment ℝ _ _ hz₂⟩

end Model
end HeadComplexity.Attention
