import HeadComplexity.Results.ExteriorCauchyInterpolation
import HeadComplexity.Results.LargeDomainCauchySharedPool

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

open scoped BigOperators Topology
open Filter

/-- A degree-seven numerator with seven prescribed compact real roots. -/
noncomputable def binaryTensorRootProduct (ε t : ℝ) : ℝ :=
  ∏ j : Fin 7, (t - ((j : ℝ) + 1) * ε)

/-- Barycentric residues, multiplied by 7!, at the eight additive binary
poles `10 + v₀ + 2 v₁ + 4 v₂`. -/
noncomputable def binaryTensorResidue (ε : ℝ) : Fin 8 → ℝ :=
  ![-binaryTensorRootProduct ε 10,
    7 * binaryTensorRootProduct ε 11,
    -21 * binaryTensorRootProduct ε 12,
    35 * binaryTensorRootProduct ε 13,
    -35 * binaryTensorRootProduct ε 14,
    21 * binaryTensorRootProduct ε 15,
    -7 * binaryTensorRootProduct ε 16,
    binaryTensorRootProduct ε 17]

noncomputable def binaryTensorSliceDet (ε : ℝ) : ℝ :=
  binaryTensorResidue ε 0 * binaryTensorResidue ε 3 -
    binaryTensorResidue ε 2 * binaryTensorResidue ε 1

noncomputable def binaryTensorOtherSliceDet (ε : ℝ) : ℝ :=
  binaryTensorResidue ε 4 * binaryTensorResidue ε 7 -
    binaryTensorResidue ε 6 * binaryTensorResidue ε 5

noncomputable def binaryTensorPencilTrace (ε : ℝ) : ℝ :=
  binaryTensorResidue ε 4 * binaryTensorResidue ε 3 +
    binaryTensorResidue ε 0 * binaryTensorResidue ε 7 -
    binaryTensorResidue ε 6 * binaryTensorResidue ε 1 -
    binaryTensorResidue ε 2 * binaryTensorResidue ε 5

/-- The Cayley hyperdeterminant, equivalently the discriminant of the
matrix pencil formed by the two binary slices. -/
noncomputable def binaryTensorPencilDiscriminant (ε : ℝ) : ℝ :=
  binaryTensorPencilTrace ε ^ 2 -
    4 * binaryTensorSliceDet ε * binaryTensorOtherSliceDet ε

lemma binaryTensor_slice_zero_ne : binaryTensorSliceDet 0 ≠ 0 := by
  norm_num [binaryTensorSliceDet, binaryTensorResidue, binaryTensorRootProduct,
    Fin.prod_univ_succ]

lemma binaryTensor_discriminant_zero_pos : 0 < binaryTensorPencilDiscriminant 0 := by
  norm_num [binaryTensorPencilDiscriminant, binaryTensorPencilTrace,
    binaryTensorSliceDet, binaryTensorOtherSliceDet, binaryTensorResidue,
    binaryTensorRootProduct, Fin.prod_univ_succ]

/-- The real matrix-pencil certificate persists as the seven token roots
coalesce. It is therefore a compact-width resource, rather than a fit at one
fixed numerical width. The conversion from this certificate to a real CP-two
decomposition is stated and proved in the accompanying written note. -/
theorem binaryTensor_pencil_eventually :
    ∀ᶠ ε : ℝ in 𝓝 0,
      binaryTensorSliceDet ε ≠ 0 ∧ 0 < binaryTensorPencilDiscriminant ε := by
  have hc₁ : Continuous binaryTensorSliceDet := by
    unfold binaryTensorSliceDet binaryTensorResidue binaryTensorRootProduct
    fun_prop
  have hc₂ : Continuous binaryTensorPencilDiscriminant := by
    unfold binaryTensorPencilDiscriminant binaryTensorPencilTrace
      binaryTensorSliceDet binaryTensorOtherSliceDet binaryTensorResidue
      binaryTensorRootProduct
    fun_prop
  exact (hc₁.continuousAt.eventually_ne binaryTensor_slice_zero_ne).and
    (continuousAt_const.eventually_lt hc₂.continuousAt binaryTensor_discriminant_zero_pos)

lemma binaryTensor_root_zero (ε : ℝ) (j : Fin 7) :
    binaryTensorRootProduct ε (((j : ℝ) + 1) * ε) = 0 := by
  unfold binaryTensorRootProduct
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)

/-- The poles are exterior to every token in `(0,1)`. -/
lemma binaryTensor_denominator_pos (v : Fin 8) {t : ℝ} (ht : t < 1) :
    0 < (10 + (v : ℝ)) - t := by
  have hv : (0 : ℝ) ≤ v := by positivity
  linarith

lemma binaryTensor_residue_barycentric (ε : ℝ) (i : Fin 8) :
    binaryTensorResidue ε i =
      5040 * binaryTensorRootProduct ε (10 + (i : ℝ)) *
        Lagrange.nodalWeight Finset.univ (fun j : Fin 8 ↦ (10 : ℝ) + j) i := by
  fin_cases i <;>
    norm_num [binaryTensorResidue, Lagrange.nodalWeight, Fin.univ_succ,
      Finset.erase_insert_of_ne] <;> ring

/-- The checked partial-fraction identity. Its seven numerator roots are
actual zeros of the compact exterior Cauchy sum. -/
theorem binaryTensor_cauchy_identity (ε t : ℝ)
    (ht : ∀ i : Fin 8, t ≠ 10 + (i : ℝ)) :
    (∑ i : Fin 8, binaryTensorResidue ε i / (10 + (i : ℝ) - t)) =
      -5040 * binaryTensorRootProduct ε t /
        (∏ i : Fin 8, (t - (10 + (i : ℝ)))) := by
  let P : Polynomial ℝ := ∏ j : Fin 7,
    (Polynomial.X - Polynomial.C (((j : ℝ) + 1) * ε))
  have hp : Function.Injective (fun i : Fin 8 ↦ (10 : ℝ) + i) := by
    intro i j hij
    have hcast : (i : ℝ) = j := by linarith
    exact Fin.ext (by exact_mod_cast hcast)
  have hPnat : P.natDegree ≤ 7 := by
    calc
      P.natDegree ≤ ∑ j : Fin 7,
          (Polynomial.X - Polynomial.C (((j : ℝ) + 1) * ε)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j : Fin 7, 1 := by
        apply Finset.sum_le_sum
        intro j _
        exact Polynomial.natDegree_X_sub_C_le (((j : ℝ) + 1) * ε)
      _ = 7 := by simp
  have hP : P.degree < (8 : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hPnat) (by norm_num)
  have heval (x : ℝ) : P.eval x = binaryTensorRootProduct ε x := by
    simp only [P, binaryTensorRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  have h := HeadComplexity.AxisZeroGluing.exterior_cauchy_barycentric
    (fun i : Fin 8 ↦ (10 : ℝ) + i) hp P hP t ht
  have hsum : (∑ i : Fin 8, binaryTensorResidue ε i / (10 + (i : ℝ) - t)) =
      -5040 * ∑ i : Fin 8,
        P.eval (10 + (i : ℝ)) *
          Lagrange.nodalWeight Finset.univ (fun j : Fin 8 ↦ (10 : ℝ) + j) i /
          (t - (10 + (i : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [binaryTensor_residue_barycentric, heval]
    rw [show 10 + (i : ℝ) - t = -(t - (10 + (i : ℝ))) by ring, div_neg]
    ring
  rw [hsum, h, heval, Lagrange.eval_nodal]
  ring

/-- Each prescribed numerator root is a genuine zero of the exterior
reciprocal sum. The restriction keeps all seven roots in `(0,1)`. -/
theorem binaryTensor_cauchy_root {ε : ℝ} (hε : ε < 1 / 7) (j : Fin 7) :
    (∑ i : Fin 8, binaryTensorResidue ε i /
      (10 + (i : ℝ) - ((j : ℝ) + 1) * ε)) = 0 := by
  have hj : (j : ℝ) + 1 ≤ 7 := by
    have := j.isLt
    exact_mod_cast (show j.val + 1 ≤ 7 by omega)
  have hjp : 0 < (j : ℝ) + 1 := by positivity
  have ht : ((j : ℝ) + 1) * ε < 1 := by
    calc
      ((j : ℝ) + 1) * ε < ((j : ℝ) + 1) * (1 / 7) :=
        mul_lt_mul_of_pos_left hε hjp
      _ ≤ 1 := by linarith
  rw [binaryTensor_cauchy_identity ε _ (fun i ↦ by
    have hp := binaryTensor_denominator_pos i ht
    linarith), binaryTensor_root_zero]
  simp

end HeadComplexity.LargeDomain
