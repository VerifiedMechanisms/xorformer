import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-! Auxiliary perspective identities and convex-cone membership patterns.
These statements do not give an asymptotic lower bound for attention heads. -/

namespace HeadComplexity.ConvexPerspective

open Finset
open scoped BigOperators

theorem perspective_gap (a c b d t : ℝ) (hb : 0 < b) (hd : 0 < d)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    t * (a ^ 2 / b) + (1 - t) * (c ^ 2 / d) -
        (t * a + (1 - t) * c) ^ 2 / (t * b + (1 - t) * d) =
      t * (1 - t) * (a * d - c * b) ^ 2 /
        (b * d * (t * b + (1 - t) * d)) := by
  have hm : 0 < t * b + (1 - t) * d := by
    by_cases h : t = 0
    · simp [h, hd]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ht (Ne.symm h)) hb)
        (mul_nonneg (sub_nonneg.mpr ht') hd.le)
  field_simp [hb.ne', hd.ne', hm.ne']
  ring

theorem perspective_convex (a c b d t : ℝ) (hb : 0 < b) (hd : 0 < d)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (t * a + (1 - t) * c) ^ 2 / (t * b + (1 - t) * d) ≤
      t * (a ^ 2 / b) + (1 - t) * (c ^ 2 / d) := by
  have h := perspective_gap a c b d t hb hd ht ht'
  have hn : 0 ≤ t * (1 - t) * (a * d - c * b) ^ 2 /
      (b * d * (t * b + (1 - t) * d)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht')) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg hb.le hd.le)
        (add_nonneg (mul_nonneg ht hb.le)
          (mul_nonneg (sub_nonneg.mpr ht') hd.le))
  linarith

/-- The convexity inequality is preserved by arbitrary nonnegative row weights. -/
theorem weighted_perspective_convex {ι : Type*} [Fintype ι]
    (a c b d w : ι → ℝ) (t : ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i) (hw : ∀ i, 0 ≤ w i)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (∑ i, w i * ((t * a i + (1 - t) * c i) ^ 2 /
        (t * b i + (1 - t) * d i))) ≤
      t * (∑ i, w i * (a i ^ 2 / b i)) +
        (1 - t) * (∑ i, w i * (c i ^ 2 / d i)) := by
  calc
    _ ≤ ∑ i, w i * (t * (a i ^ 2 / b i) +
        (1 - t) * (c i ^ 2 / d i)) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
        (perspective_convex _ _ _ _ _ (hb i) (hd i) ht ht') (hw i)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- A positive coefficient can be replaced exactly by a square coefficient. -/
theorem square_shift (a b q : ℝ) (h : 0 ≤ a + q * b) :
    (Real.sqrt (a + q * b)) ^ 2 = a + q * b :=
  Real.sq_sqrt h

/-- Adding a multiple of a denominator to a numerator only changes the bias. -/
theorem shift_ratio {ι : Type*} [Fintype ι]
    (a b φ : ι → ℝ) (q : ℝ)
    (h : ∀ i, 0 ≤ a i + q * b i) (hb : (∑ i, b i * φ i) ≠ 0) :
    (∑ i, (Real.sqrt (a i + q * b i)) ^ 2 * φ i) /
        (∑ i, b i * φ i) - q =
      (∑ i, a i * φ i) / (∑ i, b i * φ i) := by
  simp_rw [square_shift _ _ _ (h _), add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-- An explicit homogeneous linear functional on three coordinates. -/
noncomputable def separatingForm (q : ℕ) (z : Fin 3 → ℝ) : ℝ :=
  z 1 - 2 * (q : ℝ) * z 0 + ((q : ℝ) ^ 2 - 1 / 2) * z 2

def parabolaPoint (r : ℕ) : Fin 3 → ℝ := ![(r : ℝ), (r : ℝ) ^ 2, 1]

theorem separatingForm_parabola (q r : ℕ) :
    separatingForm q (parabolaPoint r) = ((r : ℝ) - (q : ℝ)) ^ 2 - 1 / 2 := by
  simp [separatingForm, parabolaPoint]
  ring

theorem separatingForm_self (q : ℕ) :
    separatingForm q (parabolaPoint q) < 0 := by
  rw [separatingForm_parabola]
  norm_num

theorem separatingForm_other (q r : ℕ) (h : q ≠ r) :
    0 < separatingForm q (parabolaPoint r) := by
  rw [separatingForm_parabola]
  rcases lt_or_gt_of_ne h with h | h
  · have hn : (q : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast h
    nlinarith [sq_nonneg ((r : ℝ) - (q : ℝ) - 1)]
  · have hn : (r : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h
    nlinarith [sq_nonneg ((q : ℝ) - (r : ℝ) - 1)]

/-- The set omits exactly the selected points on the integer parabola. -/
def patternCone (s : Finset ℕ) : Set (Fin 3 → ℝ) :=
  {z | 0 ≤ z 2 ∧ ∀ q ∈ s, 0 ≤ separatingForm q z}

theorem patternCone_convex (s : Finset ℕ) : Convex ℝ (patternCone s) := by
  intro x hx y hy a b ha hb hab
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · intro q hq
    have hlin : separatingForm q (a • x + b • y) =
        a * separatingForm q x + b * separatingForm q y := by
      simp [separatingForm]
      ring
    rw [hlin]
    exact add_nonneg (mul_nonneg ha (hx.2 q hq)) (mul_nonneg hb (hy.2 q hq))

theorem patternCone_smul (s : Finset ℕ) (z : Fin 3 → ℝ)
    (hz : z ∈ patternCone s) (t : ℝ) (ht : 0 ≤ t) : t • z ∈ patternCone s := by
  constructor
  · exact mul_nonneg ht hz.1
  · intro q hq
    have hlin : separatingForm q (t • z) = t * separatingForm q z := by
      simp [separatingForm]
      ring
    rw [hlin]
    exact mul_nonneg ht (hz.2 q hq)

theorem parabola_mem_iff (s : Finset ℕ) (r : ℕ) :
    parabolaPoint r ∈ patternCone s ↔ r ∉ s := by
  constructor
  · intro h hr
    exact (not_le_of_gt (separatingForm_self r)) (h.2 r hr)
  · intro hr
    constructor
    · norm_num [parabolaPoint]
    · intro q hq
      exact (separatingForm_other q r (by intro e; subst q; exact hr hq)).le

/-- Every defining inequality has positive slack at one common point. -/
theorem common_strict_point (q : ℕ) :
    0 < (![0, 1, 1] : Fin 3 → ℝ) 2 ∧
      0 < separatingForm q ![0, 1, 1] := by
  change 0 < (1 : ℝ) ∧ 0 < 1 - 2 * (q : ℝ) * 0 + ((q : ℝ) ^ 2 - 1 / 2) * 1
  constructor
  · norm_num
  · nlinarith [sq_nonneg (q : ℝ)]

/-- Any finite incidence table is realized by convex cones in three dimensions.
The cone indexed by `i` contains exactly the parabola points labelled true by `L`. -/
theorem arbitrary_incidence {ι : Type*} (k : ℕ) (L : ι → Fin k → Bool) :
    ∃ K : ι → Set (Fin 3 → ℝ),
      (∀ i, Convex ℝ (K i)) ∧
      (∀ i z, z ∈ K i → ∀ t : ℝ, 0 ≤ t → t • z ∈ K i) ∧
      (∀ i r, parabolaPoint r.val ∈ K i ↔ L i r = true) := by
  classical
  let s : ι → Finset ℕ := fun i ↦
    ((Finset.univ : Finset (Fin k)).filter fun r ↦ L i r = false).image Fin.val
  refine ⟨fun i ↦ patternCone (s i), fun i ↦ patternCone_convex (s i),
    fun i z hz t ht ↦ patternCone_smul (s i) z hz t ht, ?_⟩
  intro i r
  rw [parabola_mem_iff]
  simp [s, Fin.val_injective.eq_iff]

end HeadComplexity.ConvexPerspective
