import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

/-!
# An exact mean-value identity for reciprocal Boolean evaluations

The identity is specific to zero-one inputs. It supplies a positive averaging
formula in denominator-parameter space. It does not count Boolean sign patterns
and does not assert a head-complexity lower bound.
-/

namespace HeadComplexity.ReciprocalMeanValue

open Finset
open scoped BigOperators

def denominator {n : ℕ} (b : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  1 + ∑ i, if x i then b i else 0

def increment {n : ℕ} (b : Fin n → ℝ) (a : ℝ) (i : Fin n) : Fin n → ℝ :=
  Function.update b i (b i + a)

theorem denominator_pos {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, 0 < b i)
    (x : Fin n → Bool) : 0 < denominator b x := by
  unfold denominator
  have : 0 ≤ ∑ i, if x i then b i else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (hb i).le
    · exact le_rfl
  linarith

theorem denominator_increment {n : ℕ} (b : Fin n → ℝ) (a : ℝ)
    (x : Fin n → Bool) (i : Fin n) :
    denominator (increment b a i) x = denominator b x + if x i then a else 0 := by
  classical
  unfold denominator increment
  rw [← Finset.add_sum_erase (Finset.univ) (fun j ↦ if x j then Function.update b i (b i + a) j else 0) (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase (Finset.univ) (fun j ↦ if x j then b j else 0) (Finset.mem_univ i)]
  have hsum : (∑ j ∈ Finset.univ.erase i, if x j then Function.update b i (b i + a) j else 0) =
      ∑ j ∈ Finset.univ.erase i, if x j then b j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update, hji]
  rw [hsum]
  simp only [Function.update_self]
  split_ifs <;> ring

theorem denominator_scale {n : ℕ} (b : Fin n → ℝ) (a : ℝ)
    (ha : 1 + a ≠ 0) (x : Fin n → Bool) :
    denominator (fun i ↦ b i / (1 + a)) x = (denominator b x + a) / (1 + a) := by
  unfold denominator
  have hsum : (∑ i, if x i then b i / (1 + a) else 0) =
      (∑ i, if x i then b i else 0) / (1 + a) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hsum]
  field_simp
  ring

theorem scalar_identity (B a s t : ℝ) (hB : B ≠ 0) (hBa : B + a ≠ 0)
    (hs : 1 + s ≠ 0) (hBt : B = 1 + t) :
    (1 / (1 + s)) * ((1 + a) / (B + a)) +
      (s / B - a * t / (B * (B + a))) / (1 + s) = 1 / B := by
  field_simp [hB, hBa, hs]
  rw [hBt]
  ring

theorem reciprocal_mean_value {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) (a : ℝ) (ha : 0 < a) (x : Fin n → Bool) :
    (1 / (1 + ∑ i, b i)) * (1 / denominator (fun i ↦ b i / (1 + a)) x) +
      ∑ i, (b i / (1 + ∑ j, b j)) * (1 / denominator (increment b a i) x) =
      1 / denominator b x := by
  classical
  let B := denominator b x
  have hB : 0 < B := denominator_pos b hb x
  have hBa : 0 < B + a := add_pos hB ha
  have hs : 0 < 1 + ∑ i, b i := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ (hb i).le)
    linarith
  have ha' : 1 + a ≠ 0 := by positivity
  rw [denominator_scale b a ha' x]
  have hi (i : Fin n) :
      (b i / (1 + ∑ j, b j)) * (1 / denominator (increment b a i) x) =
      (b i / B - a * (if x i then b i else 0) / (B * (B + a))) /
        (1 + ∑ j, b j) := by
    rw [denominator_increment]
    change b i / (1 + ∑ j, b j) * (1 / (B + if x i then a else 0)) = _
    split_ifs <;> field_simp <;> ring
  simp_rw [hi]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_div, ← Finset.mul_sum]
  have hinv : 1 / ((B + a) / (1 + a)) = (1 + a) / (B + a) := by
    field_simp
  change (1 / (1 + ∑ i, b i)) * (1 / ((B + a) / (1 + a))) + _ = 1 / B
  rw [hinv]
  exact scalar_identity B a (∑ i, b i) (∑ i, if x i then b i else 0)
    hB.ne' hBa.ne' hs.ne' rfl

end HeadComplexity.ReciprocalMeanValue
