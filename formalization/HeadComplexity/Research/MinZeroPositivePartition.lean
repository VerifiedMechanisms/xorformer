import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Research.MarginInvariance

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.MinZeroPositivePartition
open Finset
open scoped BigOperators

def firstAtom (n : ℕ) : FracAtom (n + 1) :=
  FracAtom.ofPositiveAffineRatio 0 (fun i => if i = 0 then 2 else 0)
    1 (fun _ => 1) zero_lt_one (fun _ => zero_lt_one)

def partition (n : ℕ) (h : Fin 2) : FracAtom (n + 1) :=
  if h = 0 then firstAtom n else ((firstAtom n).scale (-1)).translate 1

theorem firstAtom_eval (n : ℕ) (x : Fin (n + 1) → Bool) :
    (firstAtom n).eval x = 2 * boolToReal (x 0) /
      (1 + ∑ i, boolToReal (x i)) := by
  rw [firstAtom, FracAtom.ofPositiveAffineRatio_eval]
  simp [affineValue]

theorem firstAtom_bounds (n : ℕ) (x : Fin (n + 1) → Bool) :
    0 ≤ (firstAtom n).eval x ∧ (firstAtom n).eval x ≤ 1 := by
  have hnonneg (i : Fin (n + 1)) : 0 ≤ boolToReal (x i) := by
    cases x i <;> norm_num [boolToReal]
  have hsum : 0 ≤ ∑ i, boolToReal (x i) := sum_nonneg fun i _ => hnonneg i
  have hsingle : boolToReal (x 0) ≤ ∑ i, boolToReal (x i) :=
    single_le_sum (fun i _ => hnonneg i) (mem_univ 0)
  have hB : 0 < 1 + ∑ i, boolToReal (x i) := by linarith
  rw [firstAtom_eval]
  refine ⟨div_nonneg (mul_nonneg (by norm_num) (hnonneg 0)) hB.le, ?_⟩
  rw [div_le_one hB]
  cases hx : x 0 <;>
    simp only [hx, boolToReal, Bool.false_eq_true, ite_false, ite_true] at hsingle ⊢ <;>
    linarith

theorem firstAtom_zero (n : ℕ) : (firstAtom n).eval (fun _ => false) = 0 := by
  norm_num [firstAtom_eval, boolToReal]

theorem firstAtom_one (n : ℕ) :
    (firstAtom n).eval (fun i => decide (i = 0)) = 1 := by
  norm_num [firstAtom_eval, boolToReal]

theorem partition_nonneg (n : ℕ) (h : Fin 2) (x : Fin (n + 1) → Bool) :
    0 ≤ (partition n h).eval x := by
  obtain ⟨h0,h1⟩ := firstAtom_bounds n x
  by_cases hh : h = 0
  · simpa [partition,hh] using h0
  · simp only [partition,ite_eq_right hh,FracAtom.translate_eval,FracAtom.scale_eval]
    linarith

theorem partition_le_one (n : ℕ) (h : Fin 2) (x : Fin (n + 1) → Bool) :
    (partition n h).eval x ≤ 1 := by
  obtain ⟨h0,h1⟩ := firstAtom_bounds n x
  by_cases hh : h = 0
  · simpa [partition,hh] using h1
  · simp only [partition,ite_eq_right hh,FracAtom.translate_eval,FracAtom.scale_eval]
    linarith

theorem partition_has_zero (n : ℕ) (h : Fin 2) :
    ∃ x : Fin (n + 1) → Bool, (partition n h).eval x = 0 := by
  by_cases hh : h = 0
  · exact ⟨fun _ => false, by simp [partition,hh,firstAtom_zero]⟩
  · exact ⟨fun i => decide (i = 0), by simp [partition,hh,firstAtom_one]⟩

theorem partition_sum (n : ℕ) (x : Fin (n + 1) → Bool) :
    ∑ h : Fin 2, (partition n h).eval x = 1 := by
  simp [Fin.sum_univ_two, partition]

theorem partition_atomSup_le (n : ℕ) (h : Fin 2) :
    RelativeMarginQuantifiers.atomSup (partition n h) ≤ 1 := by
  unfold RelativeMarginQuantifiers.atomSup
  apply Finset.sup'_le
  intro x hx
  rw [abs_of_nonneg (partition_nonneg n h x)]
  exact partition_le_one n h x

end HeadComplexity.MinZeroPositivePartition
