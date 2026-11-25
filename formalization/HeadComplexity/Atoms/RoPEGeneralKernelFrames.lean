import HeadComplexity.Atoms.RoPEGeneralFrames
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Oriented denominator kernels supply arbitrary-dimensional frames

This is the factor-independent bridge from H denominator rows to the compact
frame obstruction. The low-rank property of contractions remains an explicit
hypothesis on the row kernel.
-/

namespace HeadComplexity.RoPEGeneralFrames

open scoped BigOperators
open RoPEGeneralCoordinates

noncomputable def flatten {H : ℕ} (x : Space H) : Fin H ⊕ Fin H → ℝ :=
  Sum.elim x.1 x.2

theorem exists_orthonormal_kernel_frame {H : ℕ} {ι : Type*} [Fintype ι]
    (hcard : 2 * H ≤ Fintype.card ι) (D : Matrix (Fin H) ι ℝ) :
    ∃ w : Fin H → ι → ℝ,
      (∀ a, D.mulVec (w a) = 0) ∧
      (∀ a b, (∑ j, w a j * w b j) = if a = b then 1 else 0) := by
  let L : EuclideanSpace ℝ ι →ₗ[ℝ] (Fin H → ℝ) :=
    D.mulVecLin.comp (EuclideanSpace.equiv ι ℝ).toLinearMap
  have hdim : H ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have he := L.finrank_range_add_finrank_ker
    have hr := Submodule.finrank_le (LinearMap.range L)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      finrank_euclideanSpace] at he hr
    omega
  let b := stdOrthonormalBasis ℝ (LinearMap.ker L)
  let w : Fin H → ι → ℝ := fun a j ↦ (b (Fin.castLE hdim a)).val j
  refine ⟨w, ?_, ?_⟩
  · intro a
    exact (b (Fin.castLE hdim a)).property
  · intro a c
    have hb := b.inner_eq_ite (Fin.castLE hdim a) (Fin.castLE hdim c)
    change inner ℝ ((b (Fin.castLE hdim a)).val) ((b (Fin.castLE hdim c)).val) = _ at hb
    rw [PiLp.inner_apply] at hb
    simp only [Real.inner_apply] at hb
    simpa only [w, Fin.castLE_inj] using hb

theorem exists_paired_kernel_frame {H : ℕ} (D : Matrix (Fin H) (Fin H ⊕ Fin H) ℝ) :
    ∃ w : Fin H → Space H,
      (∀ a, D.mulVec (flatten (w a)) = 0) ∧
      (∀ a b, dot (w a) (w b) = if a = b then 1 else 0) := by
  obtain ⟨w, hker, hgram⟩ := exists_orthonormal_kernel_frame
    (H := H) (ι := Fin H ⊕ Fin H) (by simp; omega) D
  let W : Fin H → Space H := fun a ↦ (fun i ↦ w a (Sum.inl i), fun i ↦ w a (Sum.inr i))
  have hflat (a : Fin H) : flatten (W a) = w a := by
    funext i
    cases i <;> rfl
  refine ⟨W, ?_, ?_⟩
  · intro a
    rw [hflat]
    exact hker a
  · intro a b
    simpa only [dot, W, Fintype.sum_sum_type] using hgram a b

/-- A single oriented nonzero row gives a simplex normal to an entire kernel frame. -/
theorem exists_oriented_kernel_frame {H : ℕ}
    (D : Matrix (Fin H) (Fin H ⊕ Fin H) ℝ) (h : Fin H) (σ : ℝ)
    (hpos : ∀ i, 0 ≤ σ * D h i) (hsum : 0 < ∑ i, σ * D h i) :
    ∃ (w : Fin H → Space H) (v : Space H),
      (∀ a b, dot (w a) (w b) = if a = b then 1 else 0) ∧
      ((∀ i, 0 ≤ v.1 i) ∧ (∀ i, 0 ≤ v.2 i)) ∧ total v = 1 ∧
      (∀ a, dot (w a) v = 0) ∧ (∀ a, D.mulVec (flatten (w a)) = 0) := by
  obtain ⟨w, hker, hgram⟩ := exists_paired_kernel_frame D
  let V : Fin H ⊕ Fin H → ℝ := fun i ↦ (σ * D h i) / ∑ j, σ * D h j
  let v : Space H := (fun i ↦ V (Sum.inl i), fun i ↦ V (Sum.inr i))
  have hnonneg (i) : 0 ≤ V i := div_nonneg (hpos i) hsum.le
  refine ⟨w, v, hgram, ⟨fun i ↦ hnonneg _, fun i ↦ hnonneg _⟩, ?_, ?_, hker⟩
  · change (∑ i, V (Sum.inl i)) + ∑ i, V (Sum.inr i) = 1
    rw [← Fintype.sum_sum_type]
    simp only [V, ← Finset.sum_div]
    exact div_self (ne_of_gt hsum)
  · intro a
    have he := congrFun (hker a) h
    change (∑ j, D h j * flatten (w a) j) = 0 at he
    have hd : dot (w a) v = ∑ j, flatten (w a) j * V j := by
      simp [dot, v, flatten, Fintype.sum_sum_type]
    rw [hd]
    simp only [V, ← mul_div_assoc, ← Finset.sum_div]
    have hn : (∑ j, flatten (w a) j * (σ * D h j)) = 0 := by
      calc
        _ = σ * ∑ j, D h j * flatten (w a) j := by
          rw [Finset.mul_sum]
          congr 1
          funext j
          ring
        _ = 0 := by rw [he, mul_zero]
    rw [hn, zero_div]

/-- Closed source-kernel rigidity excludes all convergent families with oriented
row kernels. No boundedness of the row matrices is assumed. -/
theorem no_tendsto_of_oriented_kernels {H : ℕ} {T : Type*} [TopologicalSpace T]
    (low : T → Space H → Prop)
    (hlow_closed : IsClosed {p : T × Space H | low p.1 p.2})
    (source : T) (hsource : ∀ v, low source v → v.1 = v.2)
    (t : ℕ → T) (ht : Filter.Tendsto t Filter.atTop (nhds source))
    (D : ℕ → Matrix (Fin H) (Fin H ⊕ Fin H) ℝ)
    (hker : ∀ k v, (D k).mulVec (flatten v) = 0 → low (t k) v)
    (horient : ∀ k, ∃ h σ, (∀ i, 0 ≤ σ * D k h i) ∧ 0 < ∑ i, σ * D k h i) :
    False := by
  apply no_tendsto_of_closed_paired_relation low hlow_closed source hsource t ht
  intro k
  obtain ⟨h, σ, hp, hs⟩ := horient k
  obtain ⟨w, v, hg, hn, hu, ho, hk⟩ := exists_oriented_kernel_frame (D k) h σ hp hs
  exact ⟨w, v, hg, hn, hu, ho, fun a ↦ hker k (w a) (hk a)⟩

end HeadComplexity.RoPEGeneralFrames
