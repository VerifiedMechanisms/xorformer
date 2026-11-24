import HeadComplexity.Polynomial.PureRoPEThreeHeadCross

set_option linter.style.header false

/-!
# An arbitrary-size positive-factor cross obstruction

This extends the six-direction obstruction of prior run 1899d884da3affbf21a8528bcb74b409c9783876,
`PositiveProductsCrossObstruction`, to arbitrary even matrix size, including
zero denominator directions. It uses the unchanged scalar orientation condition.
-/

namespace HeadComplexity.PositiveHalfRankCross

noncomputable section

open Finset Matrix
open scoped BigOperators

theorem obstruction {m : ℕ} [NeZero m]
    (A V D W : Fin m → Fin (m + m) → ℝ)
    (hV : ∀ h, (∀ i, 0 < V h i) ∨ (∀ i, V h i = 0))
    (hW : ∀ h, (∀ i, 0 < W h i) ∨ (∀ i, W h i = 0))
    (hoff : ∀ i j, i ≠ j → ∑ h, (A h i * W h j + V h i * D h j) ≤ 0)
    (hsum : ∀ j, 0 < ∑ i, ∑ h, (A h i * W h j + V h i * D h j)) : False := by
  letI : NeZero (m + m) := ⟨by have := NeZero.ne m; omega⟩
  let M : Matrix (Fin (m + m)) (Fin (m + m)) ℝ :=
    fun j i ↦ ∑ h, (A h i * W h j + V h i * D h j)
  have hmoff : ∀ i j, i ≠ j → M i j ≤ 0 := fun i j hij ↦ hoff j i (Ne.symm hij)
  have hMinj : Function.Injective M.mulVecLin :=
    PureRoPEThreeHeadCross.mulVec_injective M hmoff hsum
  have hMsur : Function.Surjective M.mulVecLin := LinearMap.injective_iff_surjective.mp hMinj
  let Y : Matrix (Fin (m + m)) (Fin (m + m)) ℝ :=
    fun j ↦ Fin.append (fun h ↦ W h j) (fun h ↦ D h j)
  let coeff (u : Fin (m + m) → ℝ) : Fin (m + m) → ℝ :=
    Fin.append (fun h ↦ ∑ i, A h i * u i) (fun h ↦ ∑ i, V h i * u i)
  have hfactor (u : Fin (m + m) → ℝ) : Y.mulVec (coeff u) = M.mulVec u := by
    funext j
    simp only [Y, coeff, M, Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.mul_sum,
      Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun h i ↦ W h j * (A h i * u i)),
      Finset.sum_comm (f := fun h i ↦ D h j * (V h i * u i))]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro h _ <;> ring
  have hYsur : Function.Surjective Y.mulVecLin := by
    intro v
    obtain ⟨u, hu⟩ := hMsur v
    refine ⟨coeff u, ?_⟩
    change Y.mulVec (coeff u) = v
    rw [hfactor]
    exact hu
  have hYinj : Function.Injective Y.mulVecLin := LinearMap.injective_iff_surjective.mpr hYsur
  have hcoeffsur : Function.Surjective coeff := by
    intro v
    obtain ⟨u, hu⟩ := hMsur (Y.mulVec v)
    refine ⟨u, hYinj ?_⟩
    change Y.mulVec (coeff u) = Y.mulVec v
    rw [hfactor]
    exact hu
  have hVp : ∀ h i, 0 < V h i := by
    intro h
    rcases hV h with hp | hz
    · exact hp
    · obtain ⟨u, hu⟩ := hcoeffsur (fun j ↦ if j = Fin.natAdd m h then 1 else 0)
      have he := congrFun hu (Fin.natAdd m h)
      simp only [coeff, Fin.append_right, hz, zero_mul, Finset.sum_const_zero,
        ite_true] at he
      norm_num at he
  have hWp : ∀ h i, 0 < W h i := by
    intro h
    rcases hW h with hp | hz
    · exact hp
    · have he : Y.mulVec (fun j ↦ if j = h.castAdd m then 1 else 0) = Y.mulVec 0 := by
        funext j
        simp [Y, Matrix.mulVec, dotProduct, hz]
      have he' := congrFun (hYinj he) (h.castAdd m)
      simp at he'
  obtain ⟨u, hu, hMu⟩ := PureRoPEThreeHeadCross.positive_solution M hmoff hsum (W 0) (hWp 0)
  have hcoef : coeff u = (fun j ↦ if j = (0 : Fin m).castAdd m then 1 else 0) := by
    apply hYinj
    change Y.mulVec (coeff u) = Y.mulVec _
    rw [hfactor, hMu]
    funext j
    simp [Y, Matrix.mulVec, dotProduct]
  have hz : (∑ i, V 0 i * u i) = 0 := by
    have hne : Fin.natAdd m (0 : Fin m) ≠ (0 : Fin m).castAdd m := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_zero, Fin.val_castAdd] at hv
      have := NeZero.ne m
      omega
    simpa only [coeff, Fin.append_right, if_neg hne] using
      congrFun hcoef (Fin.natAdd m (0 : Fin m))
  have hp : 0 < ∑ i, V 0 i * u i :=
    Finset.sum_pos (fun i _ ↦ mul_pos (hVp 0 i) (hu i)) Finset.univ_nonempty
  linarith

end

end HeadComplexity.PositiveHalfRankCross
