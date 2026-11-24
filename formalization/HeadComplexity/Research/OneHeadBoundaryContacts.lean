import HeadComplexity.Research.UnitGapBasisGeometry
import HeadComplexity.Atoms.AtomicMargin

set_option linter.style.header false

/-! A coordinate whose numerator slope is no larger than the coherent
positive denominator slope cannot change a unit-gap truth table. -/

noncomputable section
namespace HeadComplexity.OneHeadBoundaryContacts
open scoped BigOperators

/-- Opposite endpoint labels need more numerator variation than the entire
positive denominator slope. -/
theorem abs_slope_gt_of_opposite_gap (a b da db : ℝ)
    (hb : 0 < b) (hdb : 0 ≤ db)
    (f g : Bool) (hfg : f ≠ g)
    (h0 : b ≤ (if f then a else -a))
    (h1 : b + db ≤ (if g then a + da else -(a + da))) : db < |da| := by
  cases f <;> cases g <;> simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  · exact False.elim (hfg rfl)
  · have hp : 0 < da := by linarith
    rw [abs_of_pos hp]
    linarith
  · have hn : da < 0 := by linarith
    rw [abs_of_neg hn]
    linarith
  · exact False.elim (hfg rfl)

/-- This is a full-cube statement and uses the original signed-label convention. -/
theorem coordinate_irrelevant_of_abs_slope_le {n : ℕ}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (f : (Fin n → Bool) → Bool)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i)
    (hgap : ∀ x, affineValue b₀ b x ≤ signedLabel f x * affineValue a₀ a x)
    (i : Fin n) (hi : |a i| ≤ b i)
    (x : Fin n → Bool) (hxi : x i = false) :
    f (Function.update x i true) = f x := by
  by_contra hn
  have h0 := hgap x
  have h1 := hgap (Function.update x i true)
  rw [UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hxi,
    UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hxi] at h1
  have h0' : affineValue b₀ b x ≤
      (if f x then affineValue a₀ a x else -affineValue a₀ a x) := by
    simpa only [signedLabel, ite_mul, one_mul, neg_one_mul] using h0
  have h1' : affineValue b₀ b x + b i ≤
      (if f (Function.update x i true) then affineValue a₀ a x + a i
       else -(affineValue a₀ a x + a i)) := by
    simpa only [signedLabel, ite_mul, one_mul, neg_one_mul] using h1
  have hc := abs_slope_gt_of_opposite_gap (affineValue a₀ a x)
    (affineValue b₀ b x) (a i) (b i)
    (affineValue_pos b₀ b hb₀ hb x) (hb i).le
    (f x) (f (Function.update x i true)) (Ne.symm hn) h0' h1'
  exact (not_lt_of_ge hi) hc

/-- At a maximum of an affine Boolean function, a positive slope forces bit one. -/
theorem maximizing_coordinate_of_positive_slope {n : ℕ}
    (c : ℝ) (a : Fin n → ℝ) (x : Fin n → Bool) (i : Fin n)
    (hmax : ∀ y, affineValue c a y ≤ affineValue c a x)
    (hi : 0 < a i) : x i = true := by
  cases hx : x i
  · have h := hmax (Function.update x i true)
    rw [UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hx] at h
    linarith
  · rfl

end HeadComplexity.OneHeadBoundaryContacts
