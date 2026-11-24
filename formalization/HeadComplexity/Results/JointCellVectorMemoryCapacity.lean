import HeadComplexity.Results.FixedDenominatorSignBarrier

set_option linter.style.header false

/-! A nonlinear memory does not bypass a fixed linear readout span.
The memory space and its feature functions are completely unrestricted.
This does not cover bit-dependent kernels or bit-dependent pole shifts. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- Every strict bit word requires at least as many fixed readout features
as bits, even if the memory and its feature map are nonlinear. -/
theorem jointCell_vector_memory_feature_capacity
    {X B I : Type*} [Fintype B] [Fintype I]
    (feature : X → I → ℝ) (coefficient : B → I → ℝ)
    (huniv : ∀ word : B → Bool, ∃ x : X, ∀ b,
      if word b then 0 < ∑ i, coefficient b i * feature x i
      else (∑ i, coefficient b i * feature x i) < 0) :
    Fintype.card B ≤ Fintype.card I := by
  classical
  let L : (I → ℝ) →ₗ[ℝ] (B → ℝ) :=
    Fintype.linearCombination ℝ (fun i b ↦ coefficient b i)
  have hL : HeadComplexity.MeetsEveryStrictOrthant L.range := by
    intro word
    obtain ⟨x, hx⟩ := huniv word
    refine ⟨L (feature x), ⟨feature x, rfl⟩, ?_⟩
    intro b
    simpa [L, Fintype.linearCombination_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm] using hx b
  simpa using HeadComplexity.card_le_finrank_of_range_meetsEveryStrictOrthant L hL

/-- An additive readout over `c` blocks with `q` features per block cannot
provide more than `c*q` independent strict output bits. -/
theorem jointCell_additive_vector_memory_capacity
    {X : Type*} {a c q : ℕ}
    (feature : X → Fin c → Fin q → ℝ)
    (coefficient : Fin a → Fin c → Fin q → ℝ)
    (huniv : ∀ word : Fin a → Bool, ∃ x : X, ∀ b,
      if word b then 0 < ∑ l, ∑ z, coefficient b l z * feature x l z
      else (∑ l, ∑ z, coefficient b l z * feature x l z) < 0) :
    a ≤ c * q := by
  have h := jointCell_vector_memory_feature_capacity
    (fun x (i : Fin c × Fin q) ↦ feature x i.1 i.2)
    (fun b i ↦ coefficient b i.1 i.2)
    (by simpa [Fintype.sum_prod_type] using huniv)
  simpa using h

/-- If only one row block contains the query bit, the other row blocks
contribute only one common readout function. Their number does not enlarge
the bit-dependent readout span. -/
theorem jointCell_one_bit_block_vector_memory_capacity
    {X : Type*} {a q : ℕ}
    (feature : X → Fin q → ℝ) (coefficient : Fin a → Fin q → ℝ)
    (common : X → ℝ)
    (huniv : ∀ word : Fin a → Bool, ∃ x : X, ∀ b,
      if word b then 0 < (∑ z, coefficient b z * feature x z) + common x
      else (∑ z, coefficient b z * feature x z) + common x < 0) :
    a ≤ q + 1 := by
  have h := jointCell_vector_memory_feature_capacity
    (fun x ↦ Fin.addCases (feature x) (fun _ : Fin 1 ↦ common x))
    (fun b ↦ Fin.addCases (coefficient b) (fun _ : Fin 1 ↦ 1))
    (by simpa [Fin.sum_univ_add] using huniv)
  simpa using h

end HeadComplexity.AxisZeroGluing
