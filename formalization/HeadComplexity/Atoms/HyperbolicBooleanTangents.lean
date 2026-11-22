import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Kernels for the hyperbolic Boolean-tangent construction

This file checks interpolation, a uniform evaluation bound, sign preservation,
and the univariate root-bracketing step. It does not formalize multivariate
hyperbolicity, the change-of-direction theorem, or an attention-head bound.
-/

namespace HeadComplexity.HyperbolicBooleanTangents

open scoped BigOperators
open Finset Polynomial

noncomputable def indicator {n : ℕ} (b : Fin n → Bool) (z₀ : ℝ)
    (z : Fin n → ℝ) : ℝ :=
  ∏ i, if b i then z i else z₀ - z i

noncomputable def interpolate {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (z₀ : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ b, f b * indicator b z₀ z

theorem indicator_boolean {n : ℕ} (b x : Fin n → Bool) :
    indicator b 1 (fun i => if x i then 1 else 0) = if b = x then 1 else 0 := by
  classical
  by_cases h : b = x
  · subst b
    simp only [indicator, ite_true]
    apply Finset.prod_eq_one
    intro i _
    cases x i <;> norm_num
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ x i := by
      by_contra! h'
      exact h (funext h')
    unfold indicator
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hbi : b i <;> cases hxi : x i <;> simp_all

theorem interpolate_boolean {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) :
    interpolate f 1 (fun i => if x i then 1 else 0) = f x := by
  classical
  unfold interpolate
  simp_rw [indicator_boolean]
  simp

theorem indicator_homogeneous {n : ℕ} (b : Fin n → Bool) (c z₀ : ℝ)
    (z : Fin n → ℝ) :
    indicator b (c * z₀) (fun i => c * z i) = c ^ n * indicator b z₀ z := by
  classical
  unfold indicator
  have h (i : Fin n) :
      (if b i then c * z i else c * z₀ - c * z i) =
        c * (if b i then z i else z₀ - z i) := by
    cases b i <;> simp [mul_sub]
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem interpolate_homogeneous {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (c z₀ : ℝ) (z : Fin n → ℝ) :
    interpolate f (c * z₀) (fun i => c * z i) = c ^ n * interpolate f z₀ z := by
  classical
  unfold interpolate
  simp_rw [indicator_homogeneous]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem indicator_abs_le {n : ℕ} (b : Fin n → Bool) (z₀ : ℝ)
    (z : Fin n → ℝ) (hz : ∀ i, |z i| ≤ 2)
    (hd : ∀ i, |z₀ - z i| ≤ 2) : |indicator b z₀ z| ≤ 2 ^ n := by
  classical
  unfold indicator
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin n, (2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact abs_nonneg _
      · intro i _; cases b i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hd i | exact hz i
    _ = _ := by simp

theorem interpolate_abs_le {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∀ b, |f b| ≤ 1) (z₀ : ℝ) (z : Fin n → ℝ)
    (hz : ∀ i, |z i| ≤ 2) (hd : ∀ i, |z₀ - z i| ≤ 2) :
    |interpolate f z₀ z| ≤ 4 ^ n := by
  classical
  unfold interpolate
  calc
    _ ≤ ∑ b, |f b * indicator b z₀ z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin n → Bool, (2 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      calc
        _ ≤ 1 * 2 ^ n := mul_le_mul (hf b) (indicator_abs_le b z₀ z hz hd)
          (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = (2 : ℝ) ^ n * 2 ^ n := by simp
    _ = 4 ^ n := by rw [← mul_pow]; norm_num

theorem perturbation_same_sign (p r a : ℝ) (ha : 0 < a)
    (hp : a ≤ |p|) (hr : |r| ≤ a / 2) : 0 < p * (p + r) := by
  have hb := abs_le.mp hr
  by_cases h : 0 ≤ p
  · rw [abs_of_nonneg h] at hp
    exact mul_pos (by linarith) (by linarith [hb.1])
  · have hn : p < 0 := lt_of_not_ge h
    rw [abs_of_neg hn] at hp
    exact mul_pos_of_neg_of_neg hn (by linarith [hb.2])

/-- Opposite strict endpoint signs give a root in the open interval. -/
theorem root_in_open_interval (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hs : p.eval a * p.eval b < 0) : ∃ t ∈ Set.Ioo a b, p.eval t = 0 := by
  have ha : p.eval a ≠ 0 := by intro h; rw [h, zero_mul] at hs; exact lt_irrefl _ hs
  have hb : p.eval b ≠ 0 := by intro h; rw [h, mul_zero] at hs; exact lt_irrefl _ hs
  have he : ∃ t ∈ Set.Icc a b, p.eval t = 0 := by
    rcases mul_neg_iff.mp hs with h | h
    · obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' hab.le p.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) from ⟨h.2.le, h.1.le⟩)
      exact ⟨t, ht, hz⟩
    · obtain ⟨t, ht, hz⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨h.1.le, h.2.le⟩)
      exact ⟨t, ht, hz⟩
  obtain ⟨t, ht, hz⟩ := he
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hz⟩
  · intro h; exact ha (h ▸ hz)
  · intro h; exact hb (h ▸ hz)

/-- Disjoint root brackets exhaust the roots of a polynomial of the given degree. -/
theorem splits_of_disjoint_brackets {k : ℕ} (p : ℝ[X]) (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ k) (a b : Fin k → ℝ)
    (hab : ∀ i, a i < b i)
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.Ioo (a i) (b i)) (Set.Ioo (a j) (b j)))
    (hs : ∀ i, p.eval (a i) * p.eval (b i) < 0) : p.Splits := by
  classical
  choose t ht hz using fun i => root_in_open_interval p (a i) (b i) (hab i) (hs i)
  have hinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (hdis i j hne) (ht i) (by rw [hij]; exact ht j)
  let s : Finset ℝ := Finset.univ.image t
  have hcard : s.card = k := by simp [s, Finset.card_image_of_injective, hinj]
  have hroots : ∀ x ∈ s, p.eval x = 0 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hz i
  have hr := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hroots (by simpa [hcard] using hdeg) hp
  have hbound : s.card ≤ p.natDegree := Polynomial.card_le_degree_of_subset_roots
    (fun x hx => (Polynomial.mem_roots hp).mpr (hroots x hx))
  rw [Polynomial.splits_iff_card_roots, hr]
  change s.card = p.natDegree
  exact Nat.le_antisymm hbound (by simpa [hcard] using hdeg)

end HeadComplexity.HyperbolicBooleanTangents
