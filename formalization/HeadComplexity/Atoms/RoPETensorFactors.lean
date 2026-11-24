import HeadComplexity.Atoms.RoPETensorLimit
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Three-head tensor factors and low-rank kernel frames

The denominator kernel of any three-by-six matrix contains an orthonormal
three-frame. An oriented nonzero denominator row supplies a simplex normal.
-/

namespace HeadComplexity.RoPEThreeTensor

open scoped BigOperators

theorem exists_orthonormal_kernel_frame (D : Matrix (Fin 3) (Fin 6) ℝ) :
    ∃ w : Fin 3 → Fin 6 → ℝ,
      (∀ a, D.mulVec (w a) = 0) ∧
      (∀ a b, (∑ j, w a j * w b j) = if a = b then 1 else 0) := by
  let L : EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] (Fin 3 → ℝ) :=
    D.mulVecLin.comp (EuclideanSpace.equiv (Fin 6) ℝ).toLinearMap
  have hdim : 3 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have he := L.finrank_range_add_finrank_ker
    have hr := Submodule.finrank_le (LinearMap.range L)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      finrank_euclideanSpace_fin] at he hr
    omega
  let b := stdOrthonormalBasis ℝ (LinearMap.ker L)
  let w : Fin 3 → Fin 6 → ℝ := fun a j ↦ (b (Fin.castLE hdim a)).val j
  refine ⟨w, ?_, ?_⟩
  · intro a
    exact (b (Fin.castLE hdim a)).property
  · intro a c
    have hb := b.inner_eq_ite (Fin.castLE hdim a) (Fin.castLE hdim c)
    change inner ℝ ((b (Fin.castLE hdim a)).val) ((b (Fin.castLE hdim c)).val) = _ at hb
    rw [PiLp.inner_apply] at hb
    simp only [Real.inner_apply] at hb
    simpa only [w, Fin.castLE_inj] using hb

theorem cross_linear_combination {ι : Type*} [Fintype ι]
    (d : ι → Fin 3 → ℝ) (w : ι → ℝ) :
    cross (fun h ↦ ∑ i, w i * d i h) = ∑ i, w i • cross (d i) := by
  ext j k
  fin_cases j <;> fin_cases k <;> simp [cross, Matrix.sum_apply]

noncomputable def factorTensor
    (D₁ N₁ D₂ N₂ D₃ N₃ : Matrix (Fin 3) (Fin 6) ℝ) :
    Fin 6 → Matrix (Fin 6) (Fin 6) ℝ := fun i ↦
  crossContraction D₂ N₂ D₃ N₃ (fun h ↦ D₁ h i) (fun h ↦ N₁ h i)

theorem factorTensor_contraction
    (D₁ N₁ D₂ N₂ D₃ N₃ : Matrix (Fin 3) (Fin 6) ℝ) (w : Fin 6 → ℝ) :
    tensorContraction (factorTensor D₁ N₁ D₂ N₂ D₃ N₃) w =
      crossContraction D₂ N₂ D₃ N₃ (D₁.mulVec w) (N₁.mulVec w) := by
  have hD : cross (D₁.mulVec w) = ∑ i, w i • cross (fun h ↦ D₁ h i) := by
    change cross (fun h ↦ ∑ i, D₁ h i * w i) = _
    simpa only [mul_comm] using
      cross_linear_combination (fun i h ↦ D₁ h i) w
  have hN : cross (N₁.mulVec w) = ∑ i, w i • cross (fun h ↦ N₁ h i) := by
    change cross (fun h ↦ ∑ i, N₁ h i * w i) = _
    simpa only [mul_comm] using
      cross_linear_combination (fun i h ↦ N₁ h i) w
  simp only [tensorContraction, factorTensor, crossContraction, hD, hN,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, Finset.sum_add_distrib]

theorem factorTensor_kernel_rank_le_three
    (D₁ N₁ D₂ N₂ D₃ N₃ : Matrix (Fin 3) (Fin 6) ℝ) (w : Fin 6 → ℝ)
    (hw : D₁.mulVec w = 0) :
    (tensorContraction (factorTensor D₁ N₁ D₂ N₂ D₃ N₃) w).rank ≤ 3 := by
  rw [factorTensor_contraction, hw]
  exact crossContraction_rank_le_three _ _ _ _ _

theorem factorTensor_change_last_modes
    (D₁ N₁ D₂ N₂ D₃ N₃ : Matrix (Fin 3) (Fin 6) ℝ)
    (L R : Matrix (Fin 6) (Fin 6) ℝ) :
    factorTensor D₁ N₁ (D₂ * L) (N₂ * L) (D₃ * R) (N₃ * R) =
      fun i ↦ L.transpose * factorTensor D₁ N₁ D₂ N₂ D₃ N₃ i * R := by
  ext i j k
  simp [factorTensor, crossContraction, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_add, Matrix.add_mul]

theorem cross_smul (a : ℝ) (d : Fin 3 → ℝ) : cross (a • d) = a • cross d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cross]

theorem factorTensor_smul_numerators
    (a : ℝ) (D₁ N₁ D₂ N₂ D₃ N₃ : Matrix (Fin 3) (Fin 6) ℝ) :
    factorTensor D₁ (a • N₁) D₂ (a • N₂) D₃ (a • N₃) =
      a • factorTensor D₁ N₁ D₂ N₂ D₃ N₃ := by
  funext i
  simp only [factorTensor, crossContraction, Pi.smul_apply]
  change D₂.transpose * cross (a • fun h ↦ N₁ h i) * D₃ +
    (a • N₂).transpose * cross (fun h ↦ D₁ h i) * D₃ +
    D₂.transpose * cross (fun h ↦ D₁ h i) * (a • N₃) = _
  simp only [cross_smul, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add]

theorem numeratorRows_smul (a δ : ℝ) : numeratorRows (a * δ) = a • numeratorRows δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [numeratorRows] <;> ring

noncomputable def denominatorProjection : Matrix (Fin 3) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0]

noncomputable def numeratorProjection : Matrix (Fin 3) (Fin 6) ℝ :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

theorem denominatorProjection_mul_blockMatrix (ε δ : ℝ) :
    denominatorProjection * blockMatrix ε δ = denominatorRows ε := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [denominatorProjection, blockMatrix, denominatorRows, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem numeratorProjection_mul_blockMatrix (ε δ : ℝ) :
    numeratorProjection * blockMatrix ε δ = numeratorRows δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numeratorProjection, blockMatrix, numeratorRows, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem crossContraction_projections (d u : Fin 3 → ℝ) :
    crossContraction denominatorProjection numeratorProjection
      denominatorProjection numeratorProjection d u = pureContraction d u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossContraction, denominatorProjection, numeratorProjection,
      pureContraction, cross, Matrix.mul_apply, Fin.sum_univ_succ]

theorem source_factorTensor_eq (ε δ : ℝ) :
    factorTensor (denominatorRows ε) (numeratorRows δ)
      (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ) =
      fun i ↦ (blockMatrix ε δ).transpose * sourceTensor ε δ i * blockMatrix ε δ := by
  calc
    _ = factorTensor (denominatorRows ε) (numeratorRows δ)
        (denominatorProjection * blockMatrix ε δ) (numeratorProjection * blockMatrix ε δ)
        (denominatorProjection * blockMatrix ε δ) (numeratorProjection * blockMatrix ε δ) := by
      rw [denominatorProjection_mul_blockMatrix, numeratorProjection_mul_blockMatrix]
    _ = _ := by
      rw [factorTensor_change_last_modes]
      simp only [factorTensor, crossContraction_projections, sourceTensor]

/-- A nonnegative nonzero denominator row yields exactly the compact frame and
simplex data needed by the source-tensor obstruction. -/
theorem factorTensor_has_frame
    (D₁ N₁ D₂ N₂ D₃ N₃ : Matrix (Fin 3) (Fin 6) ℝ)
    (h : Fin 3) (σ : ℝ) (hpos : ∀ j, 0 ≤ σ * D₁ h j)
    (hsum : 0 < ∑ j, σ * D₁ h j) :
    ∃ (w : Fin 3 → Fin 6 → ℝ) (v : Fin 6 → ℝ),
      (∀ a b, (∑ j, w a j * w b j) = if a = b then 1 else 0) ∧
      (∀ j, 0 ≤ v j) ∧ (∑ j, v j = 1) ∧
      (∀ a, ∑ j, w a j * v j = 0) ∧
      (∀ a, (tensorContraction (factorTensor D₁ N₁ D₂ N₂ D₃ N₃) (w a)).rank ≤ 3) := by
  obtain ⟨w, hker, hgram⟩ := exists_orthonormal_kernel_frame D₁
  let v : Fin 6 → ℝ := fun j ↦ (σ * D₁ h j) / ∑ l, σ * D₁ h l
  refine ⟨w, v, hgram, (fun j ↦ div_nonneg (hpos j) hsum.le), ?_, ?_, ?_⟩
  · simp only [v, ← Finset.sum_div]
    exact div_self (ne_of_gt hsum)
  · intro a
    have he := congrFun (hker a) h
    change (∑ j, D₁ h j * w a j) = 0 at he
    simp only [v, ← mul_div_assoc, ← Finset.sum_div]
    have hn : (∑ j, w a j * (σ * D₁ h j)) = 0 := by
      calc
        _ = σ * ∑ j, D₁ h j * w a j := by rw [Finset.mul_sum]; congr 1; ext j; ring
        _ = 0 := by rw [he, mul_zero]
    rw [hn, zero_div]
  · exact fun a ↦ factorTensor_kernel_rank_le_three _ _ _ _ _ _ _ (hker a)

/-- No sequence of three-head factor tensors with an oriented nonzero first-block
denominator row converges to the source tensor in fixed source coordinates. -/
theorem no_tendsto_oriented_factorTensor
    (ε δ : ℝ) (hε : ε ≠ 0)
    (D₁ N₁ D₂ N₂ D₃ N₃ : ℕ → Matrix (Fin 3) (Fin 6) ℝ)
    (horient : ∀ k, ∃ h σ, (∀ j, 0 ≤ σ * D₁ k h j) ∧
      0 < ∑ j, σ * D₁ k h j)
    (hlim : Filter.Tendsto
      (fun k ↦ factorTensor (D₁ k) (N₁ k) (D₂ k) (N₂ k) (D₃ k) (N₃ k))
      Filter.atTop (nhds (sourceTensor ε δ))) : False := by
  apply no_tendsto_source_tensor ε δ hε _ hlim
  intro k
  obtain ⟨h, σ, hp, hs⟩ := horient k
  exact factorTensor_has_frame _ _ _ _ _ _ h σ hp hs

/-- The same obstruction in the original six group coordinates in every block.
The change in the last two tensor modes is fixed and invertible. -/
theorem no_tendsto_physical_source_factorTensor
    (ε δ : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0)
    (D₁ N₁ D₂ N₂ D₃ N₃ : ℕ → Matrix (Fin 3) (Fin 6) ℝ)
    (horient : ∀ k, ∃ h σ, (∀ j, 0 ≤ σ * D₁ k h j) ∧
      0 < ∑ j, σ * D₁ k h j)
    (hlim : Filter.Tendsto
      (fun k ↦ factorTensor (D₁ k) (N₁ k) (D₂ k) (N₂ k) (D₃ k) (N₃ k))
      Filter.atTop (nhds (factorTensor (denominatorRows ε) (numeratorRows δ)
        (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ)))) :
    False := by
  let B := blockMatrix ε δ
  let C := B⁻¹
  have hu : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp (blockMatrix_isUnit ε δ hε hδ)
  have hBC : B * C = 1 := Matrix.mul_nonsing_inv _ hu
  have htranspose : C.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBC, Matrix.transpose_one]
  have hc : Continuous (fun T : Fin 6 → Matrix (Fin 6) (Fin 6) ℝ ↦
      fun i ↦ C.transpose * T i * C) := by fun_prop
  have ht := hc.continuousAt.tendsto.comp hlim
  have he : (fun i ↦ C.transpose *
      factorTensor (denominatorRows ε) (numeratorRows δ)
        (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ) i * C) =
      sourceTensor ε δ := by
    rw [source_factorTensor_eq]
    funext i
    change C.transpose * (B.transpose * sourceTensor ε δ i * B) * C = _
    calc
      _ = (C.transpose * B.transpose) * sourceTensor ε δ i * (B * C) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [htranspose, hBC, Matrix.one_mul, Matrix.mul_one]
  simp only [Function.comp_def, he] at ht
  have htransformed : Filter.Tendsto
      (fun k ↦ factorTensor (D₁ k) (N₁ k) (D₂ k * C) (N₂ k * C) (D₃ k * C) (N₃ k * C))
      Filter.atTop (nhds (sourceTensor ε δ)) := by
    simpa only [factorTensor_change_last_modes] using ht
  exact no_tendsto_oriented_factorTensor ε δ hε D₁ N₁
    (fun k ↦ D₂ k * C) (fun k ↦ N₂ k * C)
    (fun k ↦ D₃ k * C) (fun k ↦ N₃ k * C) horient htransformed

/-- Nonzero rescaling of the limiting source cubic does not remove the cone
obstruction. This is the normalization used in the polynomial compactness step. -/
theorem no_tendsto_scaled_physical_source_factorTensor
    (ε δ aScale : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (haScale : aScale ≠ 0)
    (D₁ N₁ D₂ N₂ D₃ N₃ : ℕ → Matrix (Fin 3) (Fin 6) ℝ)
    (horient : ∀ k, ∃ h σ, (∀ j, 0 ≤ σ * D₁ k h j) ∧
      0 < ∑ j, σ * D₁ k h j)
    (hlim : Filter.Tendsto
      (fun k ↦ factorTensor (D₁ k) (N₁ k) (D₂ k) (N₂ k) (D₃ k) (N₃ k))
      Filter.atTop (nhds (aScale • factorTensor (denominatorRows ε) (numeratorRows δ)
        (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ)))) :
    False := by
  apply no_tendsto_physical_source_factorTensor ε (aScale * δ) hε (mul_ne_zero haScale hδ)
    D₁ N₁ D₂ N₂ D₃ N₃ horient
  simpa only [numeratorRows_smul, factorTensor_smul_numerators] using hlim

end HeadComplexity.RoPEThreeTensor
