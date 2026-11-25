import HeadComplexity.Research.UnitGapBasisGeometry

set_option linter.style.header false

/-! Monochromatic coordinate leaves of an actual unit-contact basis can lose
positive denominator weight while retaining the full truth table and contacts. -/

noncomputable section
namespace HeadComplexity.UnitGapLeafDeletion
open scoped BigOperators

theorem affineValue_update_coeff {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (i : Fin n) (v : ℝ) (x : Fin n → Bool) :
    affineValue c (Function.update a i v) x =
      affineValue c a x + (v - a i) * boolToReal (x i) := by
  have ht : ∀ j, (Function.update a i v j) * boolToReal (x j) =
      a j * boolToReal (x j) +
        if j = i then (v - a i) * boolToReal (x i) else 0 := by
    intro j
    by_cases h : j = i
    · subst j
      simp
      ring
    · simp [h]
  simp only [affineValue, ht, Finset.sum_add_distrib]
  simp
  ring

theorem signed_contraction (f s A B t : ℝ)
    (hf : f = 1 ∨ f = -1) (hs : s = 1 ∨ s = -1)
    (ht : 0 ≤ t) (hgap : B ≤ f * A) :
    B - t ≤ f * (A - s * t) := by
  have hfs : f * s ≤ 1 := by rcases hf with rfl | rfl <;>
    rcases hs with rfl | rfl <;> norm_num
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hfs)]

/-- Every full-cube signed unit slack increases under this contraction. -/
theorem signed_gap_preserved {n : ℕ} (a₀ b₀ : ℝ) (a b : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) (i : Fin n) (s t : ℝ)
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hs : s = 1 ∨ s = -1)
    (ht : 0 ≤ t)
    (hgap : ∀ x, affineValue b₀ b x ≤ f x * affineValue a₀ a x) :
    ∀ x, affineValue b₀ (Function.update b i (b i - t)) x ≤
      f x * affineValue a₀ (Function.update a i (a i - s * t)) x := by
  intro x
  rw [affineValue_update_coeff, affineValue_update_coeff]
  have hx : 0 ≤ boolToReal (x i) := by cases x i <;> norm_num [boolToReal]
  have h := signed_contraction (f x) s (affineValue a₀ a x)
    (affineValue b₀ b x) (t * boolToReal (x i)) (hf x) hs (mul_nonneg ht hx) (hgap x)
  nlinarith

/-- All prescribed unit values survive if the one-face contacts have one sign. -/
theorem contacts_preserved {n : ℕ} {ι : Type*}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (points : ι → Fin n → Bool)
    (g : ι → ℝ) (i : Fin n) (s t : ℝ)
    (hcontact : ∀ j, affineValue a₀ a (points j) =
      g j * affineValue b₀ b (points j))
    (hone : ∀ j, points j i = true → g j = s) :
    ∀ j, affineValue a₀ (Function.update a i (a i - s * t)) (points j) =
      g j * affineValue b₀ (Function.update b i (b i - t)) (points j) := by
  intro j
  rw [affineValue_update_coeff, affineValue_update_coeff, hcontact]
  cases hx : points j i
  · simp [boolToReal]
  · rw [hone j hx]
    simp [boolToReal]
    ring

theorem remaining_slopes_pos {n : ℕ} (b : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (hb : ∀ j, 0 < b j) (ht : t < b i) :
    ∀ j, 0 < Function.update b i (b i - t) j := by
  intro j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self]
    linarith
  · simpa [h] using hb j

/-- Strict contraction remains inside the original admissible atom class. -/
theorem exists_admissible_contracted_atom {n : ℕ}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (i : Fin n) (s t : ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ j, 0 < b j) (ht : t < b i) :
    ∃ φ : FracAtom n, ∀ x, φ.eval x =
      affineValue a₀ (Function.update a i (a i - s * t)) x /
        affineValue b₀ (Function.update b i (b i - t)) x := by
  exact ⟨FracAtom.ofPositiveAffineRatio a₀ (Function.update a i (a i - s * t))
    b₀ (Function.update b i (b i - t)) hb₀ (remaining_slopes_pos b i t hb ht),
    fun x => FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x⟩

/-- The contraction preserves the complete sign table and all selected unit
observations using one genuine original head. -/
theorem exists_contracted_unit_head {n : ℕ} {ι : Type*}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (f : (Fin n → Bool) → ℝ)
    (points : ι → Fin n → Bool) (g : ι → ℝ) (i : Fin n) (s t : ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ j, 0 < b j)
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hs : s = 1 ∨ s = -1)
    (ht : 0 ≤ t) (hti : t < b i)
    (hgap : ∀ x, affineValue b₀ b x ≤ f x * affineValue a₀ a x)
    (hcontact : ∀ j, affineValue a₀ a (points j) =
      g j * affineValue b₀ b (points j))
    (hone : ∀ j, points j i = true → g j = s) :
    ∃ φ : FracAtom n, (∀ x, 1 ≤ f x * φ.eval x) ∧
      (∀ j, φ.eval (points j) = g j) := by
  obtain ⟨φ, hφ⟩ := exists_admissible_contracted_atom a₀ b₀ a b i s t hb₀ hb hti
  have hd := affineValue_pos b₀ (Function.update b i (b i - t)) hb₀
    (remaining_slopes_pos b i t hb hti)
  refine ⟨φ, ?_, ?_⟩
  · intro x
    rw [hφ, ← mul_div_assoc, le_div_iff₀ (hd x), one_mul]
    exact signed_gap_preserved a₀ b₀ a b f i s t hf hs ht hgap x
  · intro j
    rw [hφ, contacts_preserved a₀ b₀ a b points g i s t hcontact hone j]
    exact mul_div_cancel_right₀ _ (hd (points j)).ne'

theorem coefficient_mass_decreases {n : ℕ} (b : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (∑ j, Function.update b i (b i - t) j) = (∑ j, b j) - t := by
  have h := affineValue_update_coeff 0 b i (b i - t) (fun _ => true)
  simpa [affineValue, boolToReal, sub_eq_add_neg] using h

end HeadComplexity.UnitGapLeafDeletion
