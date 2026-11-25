import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
An obstruction to a proposed intermediate packing lemma, not to an original
xorformer margin repair. A fixed two-dimensional involution admits arbitrarily
many pairwise disjoint boxes whose radii are the coordinates of a positive
simplex vector and whose center is its image under the involution.
-/

noncomputable section
namespace HeadComplexity.ScaledBoxPackingObstruction

def reflection (v : ℝ × ℝ) : ℝ × ℝ := (v.1 + 4 * v.2, -v.2)

theorem reflection_involution (v : ℝ × ℝ) : reflection (reflection v) = v := by
  ext <;> simp [reflection] <;> ring

def box (t : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1 - (4 - 3 * t)| < t ∧ |z.2 - (t - 1)| < 1 - t}

theorem center_identity (t : ℝ) :
    reflection (t, 1 - t) = (4 - 3 * t, t - 1) := by
  ext <;> simp [reflection] <;> ring

theorem box_nonempty {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (box t).Nonempty := by
  refine ⟨(4 - 3 * t, t - 1), ?_⟩
  simp only [box, Set.mem_ofPred_eq, sub_self, abs_zero]
  exact ⟨ht, by linarith⟩

theorem box_disjoint {s t : ℝ} (ht : 0 < t) (hst : s ≤ t / 4) :
    Disjoint (box s) (box t) := by
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  have hs := (abs_lt.mp hzS.1).1
  have ht' := (abs_lt.mp hzT.1).2
  linarith

def scale (j : ℕ) : ℝ := (1 / 4 : ℝ) ^ (j + 1)

theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

theorem scale_lt_one (j : ℕ) : scale j < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem scale_separation {i j : ℕ} (hij : i < j) : scale j ≤ scale i / 4 := by
  have hp : (1 / 4 : ℝ) ^ (j + 1) ≤ (1 / 4 : ℝ) ^ (i + 2) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    scale j ≤ (1 / 4 : ℝ) ^ (i + 2) := hp
    _ = scale i / 4 := by
      rw [show i + 2 = (i + 1) + 1 by omega, pow_succ]
      unfold scale
      ring

/-- An infinite family of nonempty, pairwise disjoint boxes for one fixed
involution. A finite bound from its exterior norms alone is impossible. -/
theorem boxes_pairwise_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (box (scale i)) (box (scale j)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (box_disjoint (scale_pos i) (scale_separation h)).symm
  · exact box_disjoint (scale_pos j) (scale_separation h)

end HeadComplexity.ScaledBoxPackingObstruction
