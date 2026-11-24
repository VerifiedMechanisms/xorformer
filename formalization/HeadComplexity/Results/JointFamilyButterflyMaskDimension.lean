import HeadComplexity.Results.JointFamilyIncidenceObstruction

set_option linter.style.header false

/-! Exact affine masks for many butterfly stages require exponentially
many common features. This is a restriction on literal selector
implementations, not a lower bound for the original head model. -/

open scoped BigOperators
namespace HeadComplexity.AxisZeroGluing

/-- An identity submatrix of exact selectors forces at least one feature
per selector, even when addresses and features are chosen adaptively. -/
theorem jointFamily_partition_selector_feature_dimension
    {X I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (representative : I → X) (feature : X → Fin d → ℝ)
    (coefficient : I → Fin d → ℝ)
    (hselector : ∀ i j, (∑ k, coefficient i k * feature (representative j) k) =
      if i = j then 1 else 0) :
    Fintype.card I ≤ d := by
  have hind : LinearIndependent ℝ coefficient := by
    rw [Fintype.linearIndependent_iff]
    intro z hz i
    have he : (∑ j, z j * ∑ k, coefficient j k * feature (representative i) k) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hzero (k : Fin d) : ∑ j, z j * coefficient j k = 0 := by
        have h := congrFun hz k
        simpa using h
      simp_rw [← mul_assoc, ← Finset.sum_mul, hzero, zero_mul]
      simp
    simpa only [hselector, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using he
  simpa using hind.fintype_card_le_finrank

/-- Arbitrary real embeddings do not compress a complete partition into
fewer than its number of cells minus one affine coordinates. -/
theorem jointFamily_partition_selector_affine_dimension
    {X I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (representative : I → X) (address : X → Fin n → ℝ)
    (bias : I → ℝ) (slope : I → Fin n → ℝ)
    (hselector : ∀ i j, bias i + (∑ k, slope i k * address (representative j) k) =
      if i = j then 1 else 0) :
    Fintype.card I ≤ n + 1 := by
  apply jointFamily_partition_selector_feature_dimension representative
    (fun x ↦ Fin.addCases (address x) (fun _ : Fin 1 ↦ 1))
    (fun i ↦ Fin.addCases (slope i) (fun _ : Fin 1 ↦ bias i))
  intro i j
  simpa [Fin.sum_univ_add, add_comm] using hselector i j

/-- A partition indexed by all words of length `r` requires `2^r`
affine features, including the constant feature. -/
theorem jointFamily_binary_partition_affine_dimension
    {X : Type*} {r n : ℕ}
    (representative : (Fin r → Bool) → X) (address : X → Fin n → ℝ)
    (bias : (Fin r → Bool) → ℝ) (slope : (Fin r → Bool) → Fin n → ℝ)
    (hselector : ∀ i j, bias i + (∑ k, slope i k * address (representative j) k) =
      if i = j then 1 else 0) :
    2 ^ r ≤ n + 1 := by
  simpa using jointFamily_partition_selector_affine_dimension
    representative address bias slope hselector

/-- For `L` consecutive butterfly stages on `2^a` wires, the largest
source and target partition depths sum to `a + (L - 2)`. If each
partition is affine in `n` common coordinates, this necessary bound
follows. The premise explicitly records the stage-depth calculation. -/
theorem jointFamily_butterfly_affine_stage_count
    {a L u v n : ℕ} (hdepth : u + v = a + (L - 2))
    (hsource : 2 ^ u ≤ n + 1) (htarget : 2 ^ v ≤ n + 1) :
    2 ^ a * 2 ^ (L - 2) ≤ (n + 1)^2 := by
  rw [← Nat.pow_add, ← hdepth, Nat.pow_add, pow_two]
  exact Nat.mul_le_mul hsource htarget

end HeadComplexity.AxisZeroGluing
