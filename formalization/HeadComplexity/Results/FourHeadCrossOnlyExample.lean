import HeadComplexity.Results.FourHeadCrossOnlyPattern
import HeadComplexity.Polynomial.ThresholdDegreeRestriction

set_option linter.style.header false

/-!
# An explicit degree-three completion of the four-head local obstruction

This is a certified lower-bound target, not a pure-RoPE separation: no pure
four-head upper bound is asserted. The extra quadratic term changes some
within-block coefficients while vanishing at all prescribed local points.
-/

namespace HeadComplexity.FourHeadCrossOnlyExample

open Finset FourHeadLocalPattern PureRoPEThreeHead MvPolynomial
open scoped BigOperators

def integerSpin (b : Bool) : ℤ := if b then 1 else -1

def quadratic (z : Fin 16 → Bool) : ℤ :=
  let sx := ∑ i : Fin 8, integerSpin (z (left i))
  let sy := ∑ i : Fin 8, integerSpin (z (right i))
  192 - 3 * (sx * sx + sy * sy) +
    180 * ∑ i : Fin 8, integerSpin (z (left i)) * integerSpin (z (right i)) +
    2 * integerSpin (z (left 0)) * integerSpin (z (right 0)) - 20 * sx * sy +
    20 * (integerSpin (z (right 4)) - integerSpin (z (right 5))) *
      (integerSpin (z (right 6)) - integerSpin (z (right 7)))

def score (x : Fin 17 → Bool) : ℤ :=
  integerSpin (x 16) * quadratic (fun i ↦ x (i.castAdd 1))

def function (x : Fin 17 → Bool) : Bool := decide (0 < score x)

theorem integerSpin_eq (b : Bool) : integerSpin b = 2 * (if b then 1 else 0) - 1 := by
  cases b <;> norm_num [integerSpin]

theorem sum_integerSpin (z : Fin 8 → Bool) :
    (∑ i, integerSpin (z i)) = 2 * (∑ i, if z i then (1 : ℤ) else 0) - 8 := by
  simp only [integerSpin_eq, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem quadratic_mod_four (z : Fin 16 → Bool) : quadratic z % 4 = 2 := by
  unfold quadratic
  rw [sum_integerSpin (fun i ↦ z (left i)), sum_integerSpin (fun i ↦ z (right i))]
  have hx : integerSpin (z (left 0)) = 1 ∨ integerSpin (z (left 0)) = -1 := by
    cases z (left 0) <;> simp [integerSpin]
  have hy : integerSpin (z (right 0)) = 1 ∨ integerSpin (z (right 0)) = -1 := by
    cases z (right 0) <;> simp [integerSpin]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;>
    ring_nf <;> omega

theorem quadratic_ne_zero (z : Fin 16 → Bool) : quadratic z ≠ 0 := by
  intro hz
  have h := quadratic_mod_four z
  rw [hz] at h
  norm_num at h

theorem score_ne_zero (x : Fin 17 → Bool) : score x ≠ 0 := by
  apply mul_ne_zero _ (quadratic_ne_zero _)
  cases x 16 <;> norm_num [integerSpin]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all finite local labels, including every orbit point.
theorem crossOnlyPattern : CrossOnlyPattern function := by
  unfold CrossOnlyPattern OrbitLabel
  decide +kernel

theorem vanillaHStar_ge_five : 5 ≤ HStar 17 function :=
  crossOnly_HStar_ge_five function crossOnlyPattern

theorem sharedHStar_ge_five : 5 ≤ SharedHStar 17 function :=
  crossOnly_SharedHStar_ge_five function crossOnlyPattern

private noncomputable def spinPolynomial (i : Fin 17) : MvPolynomial (Fin 17) ℝ :=
  C 2 * X i - C 1

private noncomputable def xSum : MvPolynomial (Fin 17) ℝ :=
  ∑ i : Fin 8, spinPolynomial ((left i).castAdd 1)

private noncomputable def ySum : MvPolynomial (Fin 17) ℝ :=
  ∑ i : Fin 8, spinPolynomial ((right i).castAdd 1)

private noncomputable def quadraticPolynomial : MvPolynomial (Fin 17) ℝ :=
  C 192 - C 3 * (xSum * xSum + ySum * ySum) +
    C 180 * ∑ i : Fin 8,
      spinPolynomial ((left i).castAdd 1) * spinPolynomial ((right i).castAdd 1) +
    C 2 * spinPolynomial ((left 0).castAdd 1) * spinPolynomial ((right 0).castAdd 1) -
    C 20 * xSum * ySum +
    C 20 * (spinPolynomial ((right 4).castAdd 1) - spinPolynomial ((right 5).castAdd 1)) *
      (spinPolynomial ((right 6).castAdd 1) - spinPolynomial ((right 7).castAdd 1))

private noncomputable def cubicPolynomial : MvPolynomial (Fin 17) ℝ :=
  spinPolynomial 16 * quadraticPolynomial

private theorem eval_spinPolynomial (x : Fin 17 → Bool) (i : Fin 17) :
    eval (cubePoint x) (spinPolynomial i) = (integerSpin (x i) : ℝ) := by
  cases h : x i <;> norm_num [spinPolynomial, integerSpin, cubePoint, boolToReal, h]

private theorem eval_cubicPolynomial (x : Fin 17 → Bool) :
    eval (cubePoint x) cubicPolynomial = (score x : ℝ) := by
  simp only [cubicPolynomial, quadraticPolynomial, xSum, ySum, map_sub, map_add,
    map_mul, map_sum, eval_C, eval_spinPolynomial, score, quadratic]
  push_cast
  rfl

private theorem spinPolynomial_degree (i : Fin 17) :
    (spinPolynomial i).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp

private theorem cubicPolynomial_degree : cubicPolynomial.totalDegree ≤ 3 := by
  have hs := spinPolynomial_degree
  have hx : xSum.totalDegree ≤ 1 := totalDegree_finsetSum_le (fun _ _ ↦ hs _)
  have hy : ySum.totalDegree ≤ 1 := totalDegree_finsetSum_le (fun _ _ ↦ hs _)
  have hxx : (xSum * xSum).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hx hx)
  have hyy : (ySum * ySum).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hy hy)
  have hprod : (∑ i : Fin 8,
      spinPolynomial ((left i).castAdd 1) * spinPolynomial ((right i).castAdd 1)).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le (fun _ _ ↦
      (totalDegree_mul _ _).trans (Nat.add_le_add (hs _) (hs _)))
  have hadd (P Q : MvPolynomial (Fin 17) ℝ) {d : ℕ}
      (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d) : (P + Q).totalDegree ≤ d :=
    (totalDegree_add _ _).trans (max_le hP hQ)
  have hsub (P Q : MvPolynomial (Fin 17) ℝ) {d : ℕ}
      (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d) : (P - Q).totalDegree ≤ d :=
    (totalDegree_sub _ _).trans (max_le hP hQ)
  have hscale (c : ℝ) (P : MvPolynomial (Fin 17) ℝ) {d : ℕ}
      (hP : P.totalDegree ≤ d) : (C c * P).totalDegree ≤ d :=
    (totalDegree_mul _ _).trans (by simpa using hP)
  have hq : quadraticPolynomial.totalDegree ≤ 2 := by
    unfold quadraticPolynomial
    apply hadd
    · apply hsub
      · apply hadd
        · apply hadd
          · exact hsub _ _ (by simp) (hscale _ _ (hadd _ _ hxx hyy))
          · exact hscale _ _ hprod
        · exact (totalDegree_mul _ _).trans
            (Nat.add_le_add (hscale _ _ (hs _)) (hs _))
      · exact (totalDegree_mul _ _).trans (Nat.add_le_add (hscale _ _ hx) hy)
    · exact (totalDegree_mul _ _).trans
        (Nat.add_le_add (hscale _ _ (hsub _ _ (hs _) (hs _))) (hsub _ _ (hs _) (hs _)))
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hs _) hq)

theorem thresholdDegLE_three : ThresholdDegLE function 3 := by
  refine ⟨cubicPolynomial, cubicPolynomial_degree, ?_⟩
  intro x
  rw [eval_cubicPolynomial]
  simp only [function, decide_eq_true_eq]
  exact_mod_cast (Iff.rfl : 0 < score x ↔ 0 < score x)

def parityRestriction (x : Fin 3 → Bool) : Fin 17 → Bool :=
  ![x 0, false, false, x 1, false, false, false, false, false,
    false, false, false, false, false, false, false, !(x 2)]

theorem parity_restriction : ∀ x, function (parityRestriction x) = PARITY 3 x := by
  decide +kernel

private noncomputable def restrictionPolynomial : Fin 17 → MvPolynomial (Fin 3) ℝ :=
  ![X 0, C 0, C 0, X 1, C 0, C 0, C 0, C 0, C 0,
    C 0, C 0, C 0, C 0, C 0, C 0, C 0, C 1 - X 2]

private theorem restrictionPolynomial_degree (i : Fin 17) :
    (restrictionPolynomial i).totalDegree ≤ 1 := by
  have h : ((C 1 - X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ)).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (by simp)
  fin_cases i <;> simp_all [restrictionPolynomial]

private theorem eval_restrictionPolynomial (x : Fin 3 → Bool) (i : Fin 17) :
    eval (cubePoint x) (restrictionPolynomial i) = boolToReal (parityRestriction x i) := by
  fin_cases i <;> simp [restrictionPolynomial, parityRestriction, cubePoint, boolToReal]
  cases x 2 <;> norm_num

theorem thresholdDeg_eq_three : thresholdDeg function = 3 := by
  classical
  have hex : ∃ d, ThresholdDegLE function d := ⟨3, thresholdDegLE_three⟩
  rw [thresholdDeg, dif_pos hex]
  apply Nat.le_antisymm (Nat.find_min' hex thresholdDegLE_three)
  have hr := (Nat.find_spec hex).affine_restriction parityRestriction restrictionPolynomial
    restrictionPolynomial_degree eval_restrictionPolynomial
  have hfun : (fun x ↦ function (parityRestriction x)) = PARITY 3 := funext parity_restriction
  rw [hfun, PARITY_eq_symmetricFn] at hr
  simpa only [signChanges_parity] using signChanges_le_of_ThresholdDegLE hr

theorem certified_target : thresholdDeg function = 3 ∧ 5 ≤ HStar 17 function :=
  ⟨thresholdDeg_eq_three, vanillaHStar_ge_five⟩

end HeadComplexity.FourHeadCrossOnlyExample
