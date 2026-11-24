import HeadComplexity.Polynomial.FourHeadSelectorQuadratic
import HeadComplexity.Polynomial.ThreeHeadCubicFace

set_option linter.style.header false

/-!
# Exact quartic parity extraction from four affine heads

The fourth alternating difference is independent of all affine intercepts.
Its first-coordinate factorization exposes one uniformly oriented denominator
direction and the product of the other three denominator directions.
-/

namespace HeadComplexity.FourHeadQuarticFace

noncomputable section

open scoped BigOperators

def other : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

def triple (Y Z W : Fin 4 → ℝ) (h : Fin 4) : ℝ :=
  Y (other h 0) * Z (other h 1) * W (other h 2) +
    Y (other h 0) * Z (other h 2) * W (other h 1) +
    Y (other h 1) * Z (other h 0) * W (other h 2) +
    Y (other h 1) * Z (other h 2) * W (other h 0) +
    Y (other h 2) * Z (other h 0) * W (other h 1) +
    Y (other h 2) * Z (other h 1) * W (other h 0)

def middle (c : ℝ) (AY AZ AW BY BZ BW : Fin 4 → ℝ) (h : Fin 4) : ℝ :=
  c * triple BY BZ BW h + triple AY BZ BW h + triple BY AZ BW h + triple BY BZ AW h

theorem triple_uniform {n m : ℕ} (B : Fin 4 → Fin n → ℝ)
    (hB : ∀ h, AffineFraction.UniformSign (B h))
    (Y Z W : Fin m → Fin n) (h : Fin 4) :
    AffineFraction.UniformSign (fun p ↦ triple (fun j ↦ B j (Y p))
      (fun j ↦ B j (Z p)) (fun j ↦ B j (W p)) h) := by
  rcases hB (other h 0) with h0 | h0 | h0 <;>
    rcases hB (other h 1) with h1 | h1 | h1 <;>
    rcases hB (other h 2) with h2 | h2 | h2
  all_goals first
    | solve |
      apply Or.inr; apply Or.inr
      intro p
      simp [triple, h0, h1, h2]
    | solve |
      apply Or.inl
      intro p
      have h00 := h0 (Y p); have h01 := h0 (Z p); have h02 := h0 (W p)
      have h10 := h1 (Y p); have h11 := h1 (Z p); have h12 := h1 (W p)
      have h20 := h2 (Y p); have h21 := h2 (Z p); have h22 := h2 (W p)
      dsimp only [triple]
      solve_by_elim (maxDepth := 40) [add_pos, mul_pos, mul_pos_of_neg_of_neg,
        mul_neg_of_pos_of_neg, mul_neg_of_neg_of_pos, add_neg]
    | solve |
      apply Or.inr; apply Or.inl
      intro p
      have h00 := h0 (Y p); have h01 := h0 (Z p); have h02 := h0 (W p)
      have h10 := h1 (Y p); have h11 := h1 (Z p); have h12 := h1 (W p)
      have h20 := h2 (Y p); have h21 := h2 (Z p); have h22 := h2 (W p)
      dsimp only [triple]
      solve_by_elim (maxDepth := 40) [add_pos, mul_pos, mul_pos_of_neg_of_neg,
        mul_neg_of_pos_of_neg, mul_neg_of_neg_of_pos, add_neg]

def coefficient (c : ℝ) (AX AY AZ AW BX BY BZ BW : Fin 4 → ℝ) : ℝ :=
  ∑ h, (AX h * triple BY BZ BW h + BX h * middle c AY AZ AW BY BZ BW h)

theorem coefficient_sum_X {m : ℕ} (c : ℝ) (AX BX : Fin m → Fin 4 → ℝ)
    (AY AZ AW BY BZ BW : Fin 4 → ℝ) :
    coefficient c (fun h ↦ ∑ i, AX i h) AY AZ AW
      (fun h ↦ ∑ i, BX i h) BY BZ BW =
        ∑ i, coefficient c (AX i) AY AZ AW (BX i) BY BZ BW := by
  simp only [coefficient, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun h i ↦ AX i h * triple BY BZ BW h),
    Finset.sum_comm (f := fun h i ↦ BX i h * middle c AY AZ AW BY BZ BW h)]

def face (c : ℝ) (n d AX AY AZ AW BX BY BZ BW : Fin 4 → ℝ) (x y z w : ℝ) : ℝ :=
  FourHeadSelectorQuadratic.cleared c
    (fun h ↦ n h + x * AX h + y * AY h + z * AZ h + w * AW h)
    (fun h ↦ d h + x * BX h + y * BY h + z * BZ h + w * BW h)

def alternating (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  F 1 1 1 1 - F 1 1 1 0 - F 1 1 0 1 - F 1 0 1 1 - F 0 1 1 1 +
    F 1 1 0 0 + F 1 0 1 0 + F 1 0 0 1 + F 0 1 1 0 + F 0 1 0 1 + F 0 0 1 1 -
    F 1 0 0 0 - F 0 1 0 0 - F 0 0 1 0 - F 0 0 0 1 + F 0 0 0 0

set_option maxHeartbeats 6000000 in
-- Expand the sixteen quartic evaluations and collect their mixed coefficient.
theorem alternating_face (c : ℝ) (n d AX AY AZ AW BX BY BZ BW : Fin 4 → ℝ) :
    alternating (face c n d AX AY AZ AW BX BY BZ BW) =
      coefficient c AX AY AZ AW BX BY BZ BW := by
  simp [alternating, face, FourHeadSelectorQuadratic.cleared, coefficient,
    middle, triple, other, Fin.sum_univ_succ]
  ring

end
end HeadComplexity.FourHeadQuarticFace
