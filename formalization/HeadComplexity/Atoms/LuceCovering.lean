import Mathlib.Tactic

set_option linter.style.header false

/-! Algebraic and stability ingredients for a uniform cover of bounded
coherent affine-ratio tables. The general covering construction is written
separately. No unrestricted worst-case head lower bound is asserted. -/

namespace HeadComplexity.LuceCovering

open scoped BigOperators

theorem normalized_l1_bound {I : Type*} [Fintype I]
    (a b : I → ℝ) (hb : ∀ i, 0 ≤ b i)
    (haSum : 0 < ∑ i, a i) (hbSum : 0 < ∑ i, b i) :
    (∑ i, |a i / (∑ j, a j) - b i / (∑ j, b j)|) ≤
      2 * (∑ i, |a i - b i|) / (∑ i, a i) := by
  let A := ∑ i, a i
  let B := ∑ i, b i
  let E := ∑ i, |a i-b i|
  have hA : 0 < A := haSum
  have hB : 0 < B := hbSum
  have hsum : |B-A| ≤ E := by
    calc
      |B-A| = |∑ i, (b i-a i)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |b i-a i| := Finset.abs_sum_le_sum_abs _ _
      _ = E := by simp only [E, abs_sub_comm]
  have hpoint (i : I) : |a i/A-b i/B| ≤
      |a i-b i|/A + b i * |B-A|/(A*B) := by
    have hid : a i/A-b i/B = (a i-b i)/A+b i*(B-A)/(A*B) := by
      field_simp [hA.ne', hB.ne']
      ring
    rw [hid]
    calc
      _ ≤ |(a i-b i)/A| + |b i*(B-A)/(A*B)| := abs_add_le _ _
      _ = _ := by rw [abs_div, abs_div, abs_mul, abs_of_pos hA,
        abs_of_pos (mul_pos hA hB), abs_of_nonneg (hb i)]
  change (∑ i, |a i/A-b i/B|) ≤ 2*E/A
  calc
    _ ≤ ∑ i, (|a i-b i|/A + b i*|B-A|/(A*B)) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = E/A + |B-A|/A := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
        ← Finset.sum_mul]
      change E/A+B*|B-A|/(A*B) = _
      field_simp [hA.ne', hB.ne']
    _ ≤ E/A+E/A := add_le_add (le_refl _) (div_le_div_of_nonneg_right hsum hA.le)
    _ = _ := by ring

theorem split_relative_error {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℝ) (good : Finset I) (η τ : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hη : 0 ≤ η)
    (hgood : ∀ i ∈ good, a i ≤ b i ∧ b i ≤ (1+η)*a i)
    (hbad : ∑ i ∈ goodᶜ, |a i-b i| ≤ τ) :
    (∑ i, |a i-b i|) ≤ η*(∑ i, a i)+τ := by
  have hg : (∑ i ∈ good, |a i-b i|) ≤ η*(∑ i ∈ good, a i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_of_nonpos (sub_nonpos.mpr (hgood i hi).1)]
    nlinarith [(hgood i hi).2]
  have hsub : (∑ i ∈ good, a i) ≤ ∑ i, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ ↦ ha i)
  have hsplit := Finset.sum_add_sum_compl good (fun i ↦ |a i-b i|)
  have hmul := mul_le_mul_of_nonneg_left hsub hη
  linarith

theorem choice_table_identity {I : Type*} [Fintype I]
    (s : Finset I) (w r : I → ℝ) (w₀ r₀ : ℝ)
    (hD : w₀ + ∑ i ∈ s, w i ≠ 0) :
    (r₀*w₀ + ∑ i ∈ s, ((w₀+w i)*r i-r₀*w₀)) /
        (w₀+∑ i ∈ s, w i) =
      w₀/(w₀+∑ i ∈ s, w i) *
        (r₀*(1-(s.card : ℝ))+∑ i ∈ s, r i) +
      ∑ i ∈ s, (w i/(w₀+∑ j ∈ s, w j))*r i := by
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp [hD]
  simp only [Finset.sum_sub_distrib, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem convex_combination_error {I X : Type*} [Fintype I]
    (a b : I → ℝ) (f g : I → X → ℝ) (ε δ : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hbSum : ∑ i, b i = 1)
    (hf : ∀ i x, |f i x| ≤ 1) (hfg : ∀ i x, |f i x-g i x| ≤ ε)
    (hab : ∑ i, |a i-b i| ≤ δ) (x : X) :
    |(∑ i, a i*f i x)-(∑ i, b i*g i x)| ≤ δ+ε := by
  have hi (i : I) : |a i*f i x-b i*g i x| ≤ |a i-b i|+b i*ε := by
    calc
      _ = |(a i-b i)*f i x+b i*(f i x-g i x)| := by congr 1; ring
      _ ≤ |(a i-b i)*f i x|+|b i*(f i x-g i x)| := abs_add_le _ _
      _ = |a i-b i| * |f i x|+b i*|f i x-g i x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hb i)]
      _ ≤ |a i-b i| * 1+b i*ε := add_le_add
        (mul_le_mul_of_nonneg_left (hf i x) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hfg i x) (hb i))
      _ = _ := by ring
  calc
    _ = |∑ i, (a i*f i x-b i*g i x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |a i*f i x-b i*g i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|a i-b i|+b i*ε) := Finset.sum_le_sum fun i _ ↦ hi i
    _ = (∑ i, |a i-b i|)+ε := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hbSum, one_mul]
    _ ≤ _ := add_le_add hab (le_refl _)

#print axioms normalized_l1_bound
#print axioms split_relative_error
#print axioms choice_table_identity
#print axioms convex_combination_error

end HeadComplexity.LuceCovering
