import HeadComplexity.Polynomial.PositiveHalfRankCross

set_option linter.style.header false

/-!
# A three-head cubic cross obstruction

Flatten the trilinear coefficients on six X coordinates against six selected
Y,Z pairs. Each vanilla denominator direction and each product of the two
remaining denominator directions has uniform sign. The resulting square
cross matrix cannot have nonpositive off-diagonal entries and positive
column sums. All zero-direction cases are included.
-/

namespace HeadComplexity.ThreeHeadTripartiteCross

noncomputable section

open Finset
open scoped BigOperators

def other₀ : Fin 3 → Fin 3 := ![1, 0, 0]
def other₁ : Fin 3 → Fin 3 := ![2, 2, 1]

def pairFactor (Y Z : Fin 3 → ℝ) (h : Fin 3) : ℝ :=
  Y (other₀ h) * Z (other₁ h) + Y (other₁ h) * Z (other₀ h)

def middleFactor (c : ℝ) (AY AZ BY BZ : Fin 3 → ℝ) (h : Fin 3) : ℝ :=
  AY (other₀ h) * BZ (other₁ h) + AZ (other₀ h) * BY (other₁ h) +
    AY (other₁ h) * BZ (other₀ h) + AZ (other₁ h) * BY (other₀ h) +
      c * pairFactor BY BZ h

def coefficient (c : ℝ) (AX AY AZ BX BY BZ : Fin 3 → ℝ) : ℝ :=
  ∑ h, (AX h * pairFactor BY BZ h + BX h * middleFactor c AY AZ BY BZ h)

theorem coefficient_sum_X {m : ℕ} (c : ℝ) (AX BX : Fin m → Fin 3 → ℝ)
    (AY AZ BY BZ : Fin 3 → ℝ) :
    coefficient c (fun h ↦ ∑ i, AX i h) AY AZ (fun h ↦ ∑ i, BX i h) BY BZ =
      ∑ i, coefficient c (AX i) AY AZ (BX i) BY BZ := by
  simp only [coefficient, Finset.sum_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun h i ↦ AX i h * pairFactor BY BZ h),
    Finset.sum_comm (f := fun h i ↦ BX i h * middleFactor c AY AZ BY BZ h)]

private theorem orient {m : ℕ} (v : Fin m → ℝ) (hv : AffineFraction.UniformSign v) :
    ∃ s : ℝ, s * s = 1 ∧ ((∀ i, 0 < s * v i) ∨ (∀ i, s * v i = 0)) := by
  rcases hv with hp | hn | hz
  · exact ⟨1, by norm_num, Or.inl (by simpa using hp)⟩
  · exact ⟨-1, by norm_num, Or.inl (fun i ↦ by simpa using neg_pos.mpr (hn i))⟩
  · exact ⟨1, by norm_num, Or.inr (by simpa using hz)⟩

theorem uniform_obstruction {m : ℕ} [NeZero m]
    (A V D W : Fin m → Fin (m + m) → ℝ)
    (hV : ∀ h, AffineFraction.UniformSign (V h))
    (hW : ∀ h, AffineFraction.UniformSign (W h))
    (hoff : ∀ i j, i ≠ j → ∑ h, (A h i * W h j + V h i * D h j) ≤ 0)
    (hcol : ∀ j, 0 < ∑ i, ∑ h, (A h i * W h j + V h i * D h j)) : False := by
  choose s hs hsV using fun h ↦ orient (V h) (hV h)
  choose t ht htW using fun h ↦ orient (W h) (hW h)
  have he (i j) :
      ∑ h, ((t h * A h i) * (t h * W h j) + (s h * V h i) * (s h * D h j)) =
        ∑ h, (A h i * W h j + V h i * D h j) := by
    apply Finset.sum_congr rfl
    intro h _
    calc
      _ = (t h * t h) * (A h i * W h j) + (s h * s h) * (V h i * D h j) := by ring
      _ = _ := by rw [hs, ht]; ring
  apply PositiveHalfRankCross.obstruction
    (fun h i ↦ t h * A h i) (fun h i ↦ s h * V h i)
    (fun h j ↦ s h * D h j) (fun h j ↦ t h * W h j) hsV htW
  · simpa only [he] using hoff
  · simpa only [he] using hcol

theorem pairFactor_uniform {n m : ℕ} (B : Fin 3 → Fin n → ℝ)
    (hB : ∀ h, AffineFraction.UniformSign (B h)) (Y Z : Fin m → Fin n) (h : Fin 3) :
    AffineFraction.UniformSign (fun p ↦ pairFactor
      (fun j ↦ B j (Y p)) (fun j ↦ B j (Z p)) h) := by
  obtain ⟨s, hs, hsB⟩ := orient (B (other₀ h)) (hB _)
  obtain ⟨t, ht, htB⟩ := orient (B (other₁ h)) (hB _)
  rcases hsB with hp | hz
  · rcases htB with hq | hz
    · have hpos (p) : 0 < (s * t) * pairFactor
          (fun j ↦ B j (Y p)) (fun j ↦ B j (Z p)) h := by
        have h1 := mul_pos (hp (Y p)) (hq (Z p))
        have h2 := mul_pos (hq (Y p)) (hp (Z p))
        unfold pairFactor
        nlinarith
      have hst : s * t ≠ 0 := mul_ne_zero (by nlinarith [hs]) (by nlinarith [ht])
      rcases lt_or_gt_of_ne hst with hn | hp'
      · exact Or.inr (Or.inl (fun p ↦ (mul_pos_iff.mp (hpos p)).resolve_left
          (fun h ↦ (not_lt_of_ge hn.le) h.1) |>.2))
      · exact Or.inl (fun p ↦ (mul_pos_iff_of_pos_left hp').mp (hpos p))
    · exact Or.inr (Or.inr (fun p ↦ by
        have hz' (i) : B (other₁ h) i = 0 :=
          (mul_eq_zero.mp (hz i)).resolve_left (by nlinarith [ht])
        simp [pairFactor, hz']))
  · exact Or.inr (Or.inr (fun p ↦ by
      have hz' (i) : B (other₀ h) i = 0 :=
        (mul_eq_zero.mp (hz i)).resolve_left (by nlinarith [hs])
      simp [pairFactor, hz']))

theorem obstruction {n : ℕ} (c : ℝ) (A B : Fin 3 → Fin n → ℝ)
    (hB : ∀ h, AffineFraction.UniformSign (B h))
    (X Y Z : Fin 6 → Fin n)
    (hoff : ∀ i p, i ≠ p → coefficient c
      (fun h ↦ A h (X i)) (fun h ↦ A h (Y p)) (fun h ↦ A h (Z p))
      (fun h ↦ B h (X i)) (fun h ↦ B h (Y p)) (fun h ↦ B h (Z p)) ≤ 0)
    (hcol : ∀ p, 0 < ∑ i, coefficient c
      (fun h ↦ A h (X i)) (fun h ↦ A h (Y p)) (fun h ↦ A h (Z p))
      (fun h ↦ B h (X i)) (fun h ↦ B h (Y p)) (fun h ↦ B h (Z p))) : False := by
  apply uniform_obstruction
    (fun h i ↦ A h (X i)) (fun h i ↦ B h (X i))
    (fun h p ↦ middleFactor c (fun j ↦ A j (Y p)) (fun j ↦ A j (Z p))
      (fun j ↦ B j (Y p)) (fun j ↦ B j (Z p)) h)
    (fun h p ↦ pairFactor (fun j ↦ B j (Y p)) (fun j ↦ B j (Z p)) h)
  · intro h
    rcases hB h with hp | hn | hz
    · exact Or.inl (fun i ↦ hp _)
    · exact Or.inr (Or.inl (fun i ↦ hn _))
    · exact Or.inr (Or.inr (fun i ↦ hz _))
  · exact pairFactor_uniform B hB Y Z
  · exact hoff
  · exact hcol

end

end HeadComplexity.ThreeHeadTripartiteCross
