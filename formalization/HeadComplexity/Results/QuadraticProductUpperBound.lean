import HeadComplexity.Atoms.TwoHeadPencil
import HeadComplexity.Results.AffineStatisticUpperBound

set_option linter.style.header false

/-!
# Quadratic product sums with one extra vanilla head

A strict score consisting of a constant plus m products of affine forms has
a realization with m+1 vanilla heads. The construction uses finite parameters
and a single small positive perturbation.
-/

namespace HeadComplexity

open scoped BigOperators Topology

namespace CubeAffine

variable {n m : ℕ}

noncomputable def sum (A : Fin m → CubeAffine n) : CubeAffine n :=
  ⟨∑ j, (A j).const, fun i ↦ ∑ j, (A j).slope i⟩

theorem sum_eval (A : Fin m → CubeAffine n) (x : Fin n → Bool) :
    (sum A).eval x = ∑ j, (A j).eval x := by
  simp only [sum, eval, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A finite sum of m affine products and a constant has an (m+1)-head
vanilla classifier whenever its sign is strict everywhere. -/
theorem computable_of_strict_product_sum (A B : Fin m → CubeAffine n)
    (c : ℝ) (f : (Fin n → Bool) → Bool)
    (hsign : ∀ x, (0 < c + ∑ j, (A j).eval x * (B j).eval x ↔ f x = true))
    (hne : ∀ x, c + ∑ j, (A j).eval x * (B j).eval x ≠ 0) :
    computableWithSharedHeadsN n (m + 1) f := by
  classical
  let F (t : ℝ) : CubeAffine n := ⟨1, fun _ ↦ t⟩
  let G (t : ℝ) (j : Fin m) := combine 1 (F t) (t ^ 2) (B j)
  have hF (t : ℝ) (x : Fin n → Bool) :
      (F t).eval x = 1 + t * ∑ i, boolToReal (x i) := by
    simp [F, eval, Finset.mul_sum]
  have hG (t : ℝ) (j : Fin m) (x : Fin n → Bool) :
      (G t j).eval x = (F t).eval x + t ^ 2 * (B j).eval x := by
    simp [G, combine_eval]
  let S (t : ℝ) (x : Fin n → Bool) :=
    c + ∑ j, (A j).eval x * (B j).eval x /
      ((F t).eval x * (G t j).eval x)
  let I := (Fin n → Bool) ⊕ ((Fin m × Fin n) ⊕ (Fin m × (Fin n → Bool)))
  let U (t : ℝ) : I → ℝ := Sum.elim (S t)
    (Sum.elim (fun ji ↦ 1 + t * (B ji.1).slope ji.2)
      (fun jx ↦ (G t jx.1).eval jx.2))
  have hFc (x : Fin n → Bool) : ContinuousAt (fun t ↦ (F t).eval x) 0 := by
    simp only [hF]
    fun_prop
  have hGc (j : Fin m) (x : Fin n → Bool) :
      ContinuousAt (fun t ↦ (G t j).eval x) 0 := by
    simp only [hG, hF]
    fun_prop
  have hF0 (x : Fin n → Bool) : (F 0).eval x = 1 := by simp [hF]
  have hG0 (j : Fin m) (x : Fin n → Bool) : (G 0 j).eval x = 1 := by
    simp [hG, hF0]
  have hS0 (x : Fin n → Bool) :
      S 0 x = c + ∑ j, (A j).eval x * (B j).eval x := by
    simp [S, hF0, hG0]
  have hUc (i : I) : ContinuousAt (fun t ↦ U t i) 0 := by
    rcases i with x | (⟨j, i⟩ | ⟨j, x⟩)
    · change ContinuousAt (fun t ↦ S t x) 0
      apply continuousAt_const.add
      apply tendsto_finsetSum
      intro j _
      exact continuousAt_const.div ((hFc x).mul (hGc j x)) (by simp [hF0, hG0])
    · change ContinuousAt (fun t ↦ 1 + t * (B j).slope i) 0
      fun_prop
    · exact hGc j x
  have hUne (i : I) : U 0 i ≠ 0 := by
    rcases i with x | (⟨j, i⟩ | ⟨j, x⟩)
    · simpa only [U, Sum.elim_inl, hS0] using hne x
    · simp [U]
    · simp [U, hG0]
  obtain ⟨t, ht, _, hstable⟩ := exists_pos_lt_sign_preserving U hUc hUne 1 (by norm_num)
  have hFp (x : Fin n → Bool) : 0 < (F t).eval x := by
    rw [hF]
    have hb : 0 ≤ ∑ i, boolToReal (x i) := by
      apply Finset.sum_nonneg
      intro i _
      cases x i <;> norm_num [boolToReal]
    positivity
  have hGp (j : Fin m) (x : Fin n → Bool) : 0 < (G t j).eval x := by
    exact (hstable (Sum.inr (Sum.inr (j, x)))).1.mpr (by simp [U, hG0])
  have hGs (j : Fin m) (i : Fin n) : 0 < (G t j).slope i := by
    have hp : 0 < 1 + t * (B j).slope i :=
      (hstable (Sum.inr (Sum.inl (j, i)))).1.mpr (by simp [U])
    have he : (G t j).slope i = t * (1 + t * (B j).slope i) := by
      dsimp [G, F, combine]
      ring
    rw [he]
    exact mul_pos ht hp
  let N₀ := combine (1 / t ^ 2) (sum A) 0 (sum A)
  let N (j : Fin m) := combine (-(1 / t ^ 2)) (A j) 0 (A j)
  let r : Fin (m + 1) → AffineFraction n :=
    Fin.cases (ratio N₀ (F t)) (fun j ↦ ratio (N j) (G t j))
  have hr (h : Fin (m + 1)) : (r h).Admissible := by
    refine Fin.cases ?_ (fun j ↦ ?_) h
    · exact ratio_admissible _ _ hFp (Or.inl fun _ ↦ ht)
    · exact ratio_admissible _ _ (hGp j) (Or.inl (hGs j))
  have hre (x : Fin n → Bool) : c + ∑ h, (r h).eval x = S t x := by
    rw [Fin.sum_univ_succ]
    simp only [r, Fin.cases_zero, Fin.cases_succ, ratio_eval]
    have hN₀ : N₀.eval x = (∑ j, (A j).eval x) / t ^ 2 := by
      simp [N₀, combine_eval, sum_eval, div_eq_mul_inv, mul_comm]
    have hN (j : Fin m) : (N j).eval x = -(A j).eval x / t ^ 2 := by
      simp [N, combine_eval, div_eq_mul_inv, mul_comm]
    rw [hN₀]
    simp only [hN, Finset.sum_div]
    rw [← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht.ne'
    have hfne := (hFp x).ne'
    have hgne := (hGp j x).ne'
    rw [hG] at hgne ⊢
    field_simp [ht2, hfne, hgne]
    ring
  apply (computableWithSharedHeadsN_iff_affineFractionComputable (m + 1) f).mpr
  refine ⟨r, c, hr, fun x ↦ ?_⟩
  rw [hre]
  exact (hstable (Sum.inl x)).1.trans (by simpa only [U, Sum.elim_inl, hS0] using hsign x)

end CubeAffine
end HeadComplexity
