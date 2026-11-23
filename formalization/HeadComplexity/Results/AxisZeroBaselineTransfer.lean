import HeadComplexity.Results.AxisZeroTransfer
import HeadComplexity.Results.ReverseAxisCompiler

set_option linter.style.header false

/-!
# Instantiation of the concrete transfer with the checked linear compiler

This is a consistency check of the complete transfer chain. It gives no new
asymptotic saving; the existing unconditional constant-eleven bound is sharper.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

private theorem split_bits {r s : ℕ} (bits : Fin (r + s) → Bool) :
    Fin.addCases (fun i ↦ bits (Fin.castAdd s i)) (fun j ↦ bits (Fin.natAdd r j)) = bits := by
  funext k
  refine Fin.addCases ?_ ?_ k <;> intro i <;> simp

private theorem baseline_num_affine {r s : ℕ}
    (M : Fin r → Fin s → ℝ) (i : Fin r) (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue 0 (Fin.addCases (fun _ ↦ 0)
      (fun j ↦ ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) * M i j))
      (Fin.addCases z w) = reverseAxisNumerator M i w := by
  simp [affineValue, Fin.sum_univ_add, reverseAxisNumerator, Finset.mul_sum, mul_assoc]

private theorem baseline_base_affine {r s : ℕ}
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue (((r + s : ℕ) : ℝ) + 2) (fun _ ↦ -1)
      (Fin.addCases z w) = reverseAxisDenom z w := by
  simp [affineValue, Fin.sum_univ_add, reverseAxisDenom]
  ring

private theorem baseline_row_affine {r s : ℕ} (i : Fin r)
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue (((r + s : ℕ) : ℝ) + 2)
      (Fin.addCases (fun k ↦ -1 - if k = i then 1 else 0) (fun _ ↦ -1))
      (Fin.addCases z w) = reverseAxisDenom z w - boolToReal (z i) := by
  simp [affineValue, Fin.sum_univ_add, reverseAxisDenom, sub_mul,
    Finset.sum_sub_distrib, ite_mul]
  ring

/-- The exact linear baseline exposes all the affine denominator data required
by the concrete transfer theorem. -/
theorem exists_baseline_reverse_axis_data {r s : ℕ} (M : Fin r → Fin s → ℝ) :
    ∃ L : ReverseAxisData r s (r + 1), ∀ z w,
      L.score (Fin.addCases z w) = reverseAxisScore M z w := by
  classical
  let c : ℝ := ((r + s : ℕ) : ℝ) + 2
  let nums : Fin r → Fin (r + s) → ℝ := fun i ↦
    Fin.addCases (fun _ ↦ 0)
      (fun j ↦ ((r + s : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - 1) * M i j)
  let slopes : Fin r → Fin (r + s) → ℝ := fun i ↦
    Fin.addCases (fun k ↦ -1 - if k = i then 1 else 0) (fun _ ↦ -1)
  let A : Fin (r + 1) → Fin (r + s) → ℝ :=
    Fin.cases (fun k ↦ -∑ i, nums i k) nums
  let B : Fin (r + 1) → Fin (r + s) → ℝ := Fin.cases (fun _ ↦ -1) slopes
  have hcommon (z : Fin r → Bool) (w : Fin s → Bool) :
      affineValue 0 (fun k ↦ -∑ i, nums i k) (Fin.addCases z w) =
        -(∑ i, reverseAxisNumerator M i w) := by
    simp only [affineValue, zero_add, neg_mul, Finset.sum_neg_distrib]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [affineValue, zero_add] using baseline_num_affine M i z w
  have heval (z : Fin r → Bool) (w : Fin s → Bool) :
      (∑ h, affineValue 0 (A h) (Fin.addCases z w) /
        affineValue c (B h) (Fin.addCases z w)) = reverseAxisScore M z w := by
    rw [Fin.sum_univ_succ]
    simp only [A, B, Fin.cases_zero, Fin.cases_succ]
    rw [hcommon, baseline_base_affine]
    have hrows : (∑ i, affineValue 0 (nums i) (Fin.addCases z w) /
        affineValue c (slopes i) (Fin.addCases z w)) =
        ∑ i, reverseAxisNumerator M i w /
          (reverseAxisDenom z w - boolToReal (z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [baseline_num_affine, baseline_row_affine]
    rw [hrows]
    simp only [reverseAxisScore, neg_div]
    ring
  have hpositive (h : Fin (r + 1)) (bits : Fin (r + s) → Bool) :
      0 < affineValue c (B h) bits := by
    rw [← split_bits bits]
    refine Fin.cases ?_ (fun i ↦ ?_) h
    · rw [show B 0 = (fun _ ↦ -1) from rfl, baseline_base_affine]
      have := reverseAxisDenom_ge_two
        (fun i ↦ bits (Fin.castAdd s i)) (fun j ↦ bits (Fin.natAdd r j))
      linarith
    · rw [show B i.succ = slopes i from rfl, baseline_row_affine]
      have := reverseAxisRowDenom_ge_one
        (fun i ↦ bits (Fin.castAdd s i)) (fun j ↦ bits (Fin.natAdd r j)) i
      linarith
  have hnegative (h : Fin (r + 1)) (k : Fin (r + s)) : B h k < 0 := by
    refine Fin.cases ?_ (fun i ↦ ?_) h
    · norm_num [B]
    · change slopes i k < 0
      refine Fin.addCases ?_ ?_ k
      · intro l
        simp only [slopes, Fin.addCases_left]
        split_ifs <;> norm_num
      · intro l
        norm_num [slopes]
  let L : ReverseAxisData r s (r + 1) :=
    { a₀ := fun _ ↦ 0, b₀ := fun _ ↦ c, a := A, b := B
      positive := hpositive
      negative := hnegative
      zero_left := fun w ↦ (heval _ w).trans (reverseAxisScore_zero_left M w)
      zero_right := fun z ↦ (heval z _).trans (reverseAxisScore_zero_right M z) }
  exact ⟨L, heval⟩

/-- An unconditional instance of the explicit compiler hypothesis, at linear
cost `r + 1`. It validates the transfer but does not prove a sublinear compiler. -/
theorem hasReverseAxisCompiler_linear (r s : ℕ) : HasReverseAxisCompiler r s (r + 1) := by
  intro table
  let M : Fin r → Fin s → ℝ := fun i j ↦ outputSign (table i j)
  obtain ⟨L, heval⟩ := exists_baseline_reverse_axis_data M
  refine ⟨r + 1, le_rfl, L, ?_⟩
  intro i j
  change 0 < outputSign (table i j) * L.score
    (Fin.addCases (reverseAxisOneHot i) (reverseAxisOneHot j))
  rw [heval, reverseAxisScore_oneHot]
  dsimp [M]
  cases table i j <;> norm_num [outputSign]

/-- The entire concrete gluing chain is instantiated unconditionally by the
linear baseline. This bound is weaker than the existing universal bound. -/
theorem worstCaseHeadComplexity_real_le_reverse_baseline {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    (worstCaseHeadComplexity (a + b) : ℝ) ≤
      484 * (2 : ℝ) ^ (a + b) * (a + 1) / ((a : ℝ) * b) + 2 ^ a + 2 ^ b := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    worstCaseHeadComplexity_real_le_of_reverse_axis_compiler ha hb
      (hasReverseAxisCompiler_linear a b)

end AxisZeroGluing
end HeadComplexity
