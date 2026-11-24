import HeadComplexity.Atoms.RoPEThreeTensor
import Mathlib.Topology.Sequences

set_option linter.style.header false

/-!
# The frame obstruction for limiting three-head tensors

This module isolates the finite-dimensional final step of the grid argument.
The polynomial compactness and Boolean symmetrization steps are not asserted here.
-/

namespace HeadComplexity.RoPEThreeTensor

open scoped BigOperators

/-- Three orthonormal vectors in the paired-coordinate subspace span it. Any
vector orthogonal to all three therefore has coordinate sum zero. -/
theorem sum_zero_of_orthogonal_paired_frame
    (w : Fin 3 → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (hpair : ∀ a, w a 0 = w a 3 ∧ w a 1 = w a 4 ∧ w a 2 = w a 5)
    (hgram : ∀ a b, (∑ j, w a j * w b j) = if a = b then 1 else 0)
    (horth : ∀ a, ∑ j, w a j * v j = 0) :
    (∑ j, v j) = 0 := by
  let B : Matrix (Fin 3) (Fin 3) ℝ := fun a ↦ ![w a 0, w a 1, w a 2]
  let C : Matrix (Fin 3) (Fin 3) ℝ := (2 : ℝ) • B.transpose
  have hBC : B * C = 1 := by
    ext a b
    have hg := hgram a b
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hg
    change w a 0 * w b 0 + (w a 1 * w b 1 + (w a 2 * w b 2 +
      (w a 3 * w b 3 + (w a 4 * w b 4 + w a 5 * w b 5)))) = _ at hg
    rw [← (hpair a).1, ← (hpair a).2.1, ← (hpair a).2.2,
      ← (hpair b).1, ← (hpair b).2.1, ← (hpair b).2.2] at hg
    simp only [Matrix.mul_apply, C, Matrix.smul_apply, Matrix.transpose_apply,
      smul_eq_mul, B, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply]
    linarith only [hg]
  have hBunit : IsUnit B := by
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro y
    refine ⟨C.mulVec y, ?_⟩
    rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
  let z : Fin 3 → ℝ := ![v 0 + v 3, v 1 + v 4, v 2 + v 5]
  have hBz : B.mulVec z = 0 := by
    ext a
    have ho := horth a
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at ho
    change w a 0 * v 0 + (w a 1 * v 1 + (w a 2 * v 2 +
      (w a 3 * v 3 + (w a 4 * v 4 + w a 5 * v 5)))) = 0 at ho
    rw [← (hpair a).1, ← (hpair a).2.1, ← (hpair a).2.2] at ho
    simp [B, z, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linarith only [ho]
  have hz : z = 0 := Matrix.mulVec_injective_iff_isUnit.mpr hBunit
    (hBz.trans (Matrix.mulVec_zero B).symm)
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  have hz2 := congrFun hz 2
  change v 0 + v 3 = 0 at hz0
  change v 1 + v 4 = 0 at hz1
  change v 2 + v 5 = 0 at hz2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change v 0 + (v 1 + (v 2 + (v 3 + (v 4 + v 5)))) = 0
  linarith only [hz0, hz1, hz2]

theorem paired_of_denominatorRows_mulVec_zero (ε : ℝ) (hε : ε ≠ 0)
    (w : Fin 6 → ℝ) (hw : (denominatorRows ε).mulVec w = 0) :
    w 0 = w 3 ∧ w 1 = w 4 ∧ w 2 = w 5 := by
  have h0 := congrFun hw (0 : Fin 3)
  have h1 := congrFun hw (1 : Fin 3)
  have h2 := congrFun hw (2 : Fin 3)
  have e0 : ε * (w 0 - w 3) = 0 := by
    rw [mul_sub]
    simpa [denominatorRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg] using h0
  have e1 : ε * (w 1 - w 4) = 0 := by
    rw [mul_sub]
    simpa [denominatorRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg] using h1
  have e2 : ε * (w 2 - w 5) = 0 := by
    rw [mul_sub]
    simpa [denominatorRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg] using h2
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp e0).resolve_left hε)
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_left hε)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left hε)

/-- A normalized vector cannot annihilate an orthonormal frame in the source
denominator kernel. Nonnegativity is needed only for extracting the limit. -/
theorem no_normalized_orthogonal_kernel_frame
    (ε : ℝ) (hε : ε ≠ 0) (w : Fin 3 → Fin 6 → ℝ) (v : Fin 6 → ℝ)
    (hker : ∀ a, (denominatorRows ε).mulVec (w a) = 0)
    (hgram : ∀ a b, (∑ j, w a j * w b j) = if a = b then 1 else 0)
    (horth : ∀ a, ∑ j, w a j * v j = 0)
    (hnorm : ∑ j, v j = 1) : False := by
  have hz := sum_zero_of_orthogonal_paired_frame w v
    (fun a ↦ paired_of_denominatorRows_mulVec_zero ε hε (w a) (hker a)) hgram horth
  linarith

/-- The final limiting-frame contradiction, with convergence hypotheses stated
explicitly. The low-rank matrices are expressed in the fixed source coordinates. -/
theorem no_convergent_normalized_low_rank_frames
    (ε : ℝ) (hε : ε ≠ 0)
    (w : ℕ → Fin 3 → Fin 6 → ℝ) (W : Fin 3 → Fin 6 → ℝ)
    (v : ℕ → Fin 6 → ℝ) (V : Fin 6 → ℝ)
    (A : ℕ → Fin 3 → Matrix (Fin 6) (Fin 6) ℝ) (u : Fin 3 → Fin 3 → ℝ)
    (hw : Filter.Tendsto w Filter.atTop (nhds W))
    (hv : Filter.Tendsto v Filter.atTop (nhds V))
    (hA : ∀ a, Filter.Tendsto (fun k ↦ A k a) Filter.atTop
      (nhds (pureContraction ((denominatorRows ε).mulVec (W a)) (u a))))
    (hr : ∀ k a, (A k a).rank ≤ 3)
    (hgram : ∀ k a b, (∑ j, w k a j * w k b j) = if a = b then 1 else 0)
    (horth : ∀ k a, ∑ j, w k a j * v k j = 0)
    (hnorm : ∀ k, ∑ j, v k j = 1) : False := by
  have hker (a : Fin 3) : (denominatorRows ε).mulVec (W a) = 0 :=
    denominator_zero_of_tendsto_low_rank (fun k ↦ A k a) _ _ (fun k ↦ hr k a) (hA a)
  have hg (a b : Fin 3) : (∑ j, W a j * W b j) = if a = b then 1 else 0 := by
    have hc : Continuous (fun X : Fin 3 → Fin 6 → ℝ ↦ ∑ j, X a j * X b j) := by fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hw)
    simpa only [Function.comp_def, hgram] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ (if a = b then 1 else 0 : ℝ)) Filter.atTop (nhds _))
  have ho (a : Fin 3) : (∑ j, W a j * V j) = 0 := by
    have hc : Continuous (fun X : (Fin 3 → Fin 6 → ℝ) × (Fin 6 → ℝ) ↦
      ∑ j, X.1 a j * X.2 j) := by fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp (hw.prodMk_nhds hv))
    simpa only [Function.comp_def, horth] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds _))
  have hn : (∑ j, V j) = 1 := by
    have hc : Continuous (fun X : Fin 6 → ℝ ↦ ∑ j, X j) := by fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hv)
    simpa only [Function.comp_def, hnorm] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds _))
  exact no_normalized_orthogonal_kernel_frame ε hε W V hker hg ho hn

noncomputable def tensorContraction
    (T : Fin 6 → Matrix (Fin 6) (Fin 6) ℝ) (w : Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ := ∑ i, w i • T i

noncomputable def sourceTensor (ε δ : ℝ) : Fin 6 → Matrix (Fin 6) (Fin 6) ℝ :=
  fun i ↦ pureContraction (fun h ↦ denominatorRows ε h i) (fun h ↦ numeratorRows δ h i)

set_option maxHeartbeats 800000 in
-- Expanding all 36 entries checks the concrete matrix coordinates independently.
theorem sourceTensor_contraction (ε δ : ℝ) (w : Fin 6 → ℝ) :
    tensorContraction (sourceTensor ε δ) w =
      pureContraction ((denominatorRows ε).mulVec w) ((numeratorRows δ).mulVec w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorContraction, sourceTensor, pureContraction, denominatorRows,
      numeratorRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem continuous_tensorContraction :
    Continuous (fun X : (Fin 6 → Matrix (Fin 6) (Fin 6) ℝ) × (Fin 6 → ℝ) ↦
      tensorContraction X.1 X.2) := by
  unfold tensorContraction
  fun_prop

/-- A three-dimensional low-rank kernel accompanied by a simplex normal cannot
converge to the source tensor. This theorem extracts its own common subsequence;
it does not assume bounded parameters in a tensor factorization. -/
theorem no_tendsto_source_tensor
    (ε δ : ℝ) (hε : ε ≠ 0)
    (T : ℕ → Fin 6 → Matrix (Fin 6) (Fin 6) ℝ)
    (hT : Filter.Tendsto T Filter.atTop (nhds (sourceTensor ε δ)))
    (hframes : ∀ k, ∃ (w : Fin 3 → Fin 6 → ℝ) (v : Fin 6 → ℝ),
      (∀ a b, (∑ j, w a j * w b j) = if a = b then 1 else 0) ∧
      (∀ j, 0 ≤ v j) ∧ (∑ j, v j = 1) ∧
      (∀ a, ∑ j, w a j * v j = 0) ∧
      (∀ a, (tensorContraction (T k) (w a)).rank ≤ 3)) : False := by
  choose w v hgram hvpos hvsum horth hr using hframes
  let X := (Fin 3 → Fin 6 → ℝ) × (Fin 6 → ℝ)
  let lo : X := (fun _ _ ↦ -1, fun _ ↦ 0)
  let hi : X := (fun _ _ ↦ 1, fun _ ↦ 1)
  have hbound (k : ℕ) : (w k, v k) ∈ Set.Icc lo hi := by
    constructor
    · constructor
      · intro a j
        have hs : w k a j * w k a j ≤ 1 := by
          calc
            _ ≤ ∑ l, w k a l * w k a l :=
              Finset.single_le_sum (fun l _ ↦ mul_self_nonneg _) (Finset.mem_univ j)
            _ = 1 := by simpa using hgram k a a
        change -1 ≤ w k a j
        nlinarith [sq_nonneg (w k a j + 1)]
      · exact hvpos k
    · constructor
      · intro a j
        have hs : w k a j * w k a j ≤ 1 := by
          calc
            _ ≤ ∑ l, w k a l * w k a l :=
              Finset.single_le_sum (fun l _ ↦ mul_self_nonneg _) (Finset.mem_univ j)
            _ = 1 := by simpa using hgram k a a
        change w k a j ≤ 1
        nlinarith [sq_nonneg (w k a j - 1)]
      · intro j
        change v k j ≤ 1
        calc
          _ ≤ ∑ l, v k l := Finset.single_le_sum (fun l _ ↦ hvpos k l) (Finset.mem_univ j)
          _ = 1 := hvsum k
  obtain ⟨Z, _, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc lo hi)).tendsto_subseq hbound
  have hw : Filter.Tendsto (fun k ↦ w (φ k)) Filter.atTop (nhds Z.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hv : Filter.Tendsto (fun k ↦ v (φ k)) Filter.atTop (nhds Z.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  have hTs : Filter.Tendsto (fun k ↦ T (φ k)) Filter.atTop (nhds (sourceTensor ε δ)) :=
    hT.comp hφ.tendsto_atTop
  apply no_convergent_normalized_low_rank_frames ε hε
    (fun k ↦ w (φ k)) Z.1 (fun k ↦ v (φ k)) Z.2
    (fun k a ↦ tensorContraction (T (φ k)) (w (φ k) a))
    (fun a ↦ (numeratorRows δ).mulVec (Z.1 a)) hw hv
  · intro a
    have hwa : Filter.Tendsto (fun k ↦ w (φ k) a) Filter.atTop (nhds (Z.1 a)) :=
      (continuous_apply a).continuousAt.tendsto.comp hw
    simpa only [Function.comp_def, sourceTensor_contraction] using
      continuous_tensorContraction.continuousAt.tendsto.comp (hTs.prodMk_nhds hwa)
  · exact fun k a ↦ hr (φ k) a
  · exact fun k a b ↦ hgram (φ k) a b
  · exact fun k a ↦ horth (φ k) a
  · exact fun k ↦ hvsum (φ k)

end HeadComplexity.RoPEThreeTensor
