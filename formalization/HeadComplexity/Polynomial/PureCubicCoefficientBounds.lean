import HeadComplexity.Polynomial.PureCubicRawKernel
import HeadComplexity.Polynomial.PolynomialCubeLipschitz

set_option linter.style.header false

/-! # Elementary coefficient and all-one bounds for the actual explicit cubic -/

namespace HeadComplexity.PureCubicCoefficientBounds
noncomputable section
open MvPolynomial PureCubicRawKernel PureRoPEReplication GenericCubicHessianPullback
open scoped BigOperators

theorem coeff_monomial_abs_le {α : Type*} (d e : α →₀ ℕ) (a : ℝ) :
    |(monomial d a).coeff e| ≤ |a| := by
  classical
  simp only [coeff_monomial]
  split_ifs <;> simp

theorem coeff_triple_sum_bound {α ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (a : ι → ℝ) (b : κ → ℝ) (c : ν → ℝ)
    (d : ι → α →₀ ℕ) (e : κ → α →₀ ℕ) (f : ν → α →₀ ℕ) (u : α →₀ ℕ) :
    |((∑ i, monomial (d i) (a i)) * (∑ j, monomial (e j) (b j)) *
      (∑ k, monomial (f k) (c k))).coeff u| ≤
      (∑ i, |a i|) * (∑ j, |b j|) * (∑ k, |c k|) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul, coeff_sum]
  calc
    _ ≤ ∑ k, |∑ j, ∑ i, (monomial (d i + e j + f k) (a i * b j * c k)).coeff u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ j, ∑ i, |a i * b j * c k| := by
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ ↦ coeff_monomial_abs_le _ _ _)
    _ = _ := by simp only [abs_mul]

def affineExponent {α : Type*} : Option α → α →₀ ℕ
  | none => 0
  | some i => Finsupp.single i 1

def affineCoefficient {α : Type*} (c : ℝ) (a : α → ℝ) : Option α → ℝ
  | none => c
  | some i => a i

theorem affine_expansion {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    (∑ i : Option (Fin n), monomial (affineExponent i) (affineCoefficient c a i)) =
      C c + linearPolynomial a := by
  simp [Fintype.sum_option, affineExponent, affineCoefficient, linearPolynomial,
    C_mul_X_eq_monomial]

theorem affine_coefficient_sum {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    (∑ i : Option (Fin n), |affineCoefficient c a i|) = |c| + ∑ i, |a i| := by
  simp [Fintype.sum_option, affineCoefficient]

theorem coeff_affine_triple_bound {n : ℕ} (a b c : Fin n → ℝ) (u : Fin n →₀ ℕ) :
    |(linearPolynomial a * (1 + linearPolynomial b) * (1 + linearPolynomial c)).coeff u| ≤
      (∑ i, |a i|) * (1 + ∑ i, |b i|) * (1 + ∑ i, |c i|) := by
  have h := coeff_triple_sum_bound (affineCoefficient 0 a) (affineCoefficient 1 b)
    (affineCoefficient 1 c) affineExponent affineExponent affineExponent u
  simpa only [affine_expansion, affine_coefficient_sum, map_zero, zero_add,
    map_one, abs_zero, abs_one] using h

theorem base_sum_abs (h : Fin 3) : ∑ i, |baseS h i| ≤ 102 / 1000 := by
  fin_cases h <;> norm_num [baseS, Fin.sum_univ_succ]

theorem baseB_sum_abs (h : Fin 3) : ∑ i, |baseB h i| ≤ 1 / 100 := by
  fin_cases h <;> norm_num [baseB, Fin.sum_univ_succ]

theorem rawTarget_coefficient_bound (u : Fin 14 →₀ ℕ) : |rawTarget.coeff u| ≤ 1 := by
  have ht (h j k : Fin 3) :
      |(linearPolynomial (baseS h) * (1 + linearPolynomial (baseB j)) *
        (1 + linearPolynomial (baseB k))).coeff u| ≤ (102 / 1000 : ℝ) * (101 / 100)^2 := by
    apply (coeff_affine_triple_bound _ _ _ _).trans
    have hs := base_sum_abs h
    have hb := baseB_sum_abs j
    have hc := baseB_sum_abs k
    have hn : 0 ≤ ∑ i, |baseS h i| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hnb : 0 ≤ 1 + ∑ i, |baseB j i| := by positivity
    have hnc : 0 ≤ 1 + ∑ i, |baseB k i| := by positivity
    nlinarith [mul_le_mul hs (show 1 + ∑ i, |baseB j i| ≤ 101 / 100 by linarith)
      hnb (by norm_num : (0 : ℝ) ≤ 102 / 1000),
      mul_le_mul_of_nonneg_right hc (show 0 ≤ (102 / 1000 : ℝ) * (101 / 100) by positivity)]
  rw [rawTarget_formula, coeff_add, coeff_add]
  have h01 := abs_add_le
    ((linearPolynomial (baseS 0) * (1 + linearPolynomial (baseB 1)) *
      (1 + linearPolynomial (baseB 2))).coeff u)
    ((linearPolynomial (baseS 1) * (1 + linearPolynomial (baseB 0)) *
      (1 + linearPolynomial (baseB 2))).coeff u)
  have h012 := abs_add_le
    (((linearPolynomial (baseS 0) * (1 + linearPolynomial (baseB 1)) *
      (1 + linearPolynomial (baseB 2))).coeff u) +
      ((linearPolynomial (baseS 1) * (1 + linearPolynomial (baseB 0)) *
      (1 + linearPolynomial (baseB 2))).coeff u))
    ((linearPolynomial (baseS 2) * (1 + linearPolynomial (baseB 0)) *
      (1 + linearPolynomial (baseB 1))).coeff u)
  linarith [ht 0 1 2, ht 1 0 2, ht 2 0 1]

theorem rawTarget_all_one_positive :
    (1 / 10000 : ℝ) < eval (fun _ : Fin 14 ↦ (1 : ℝ)) rawTarget := by
  rw [eval_rawTarget]
  norm_num [baseS, baseB, Fin.sum_univ_succ]

theorem rawTarget_lipschitz (x y : Fin 14 → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) (hxy : ∀ i, |x i - y i| ≤ ε) :
    |eval x rawTarget - eval y rawTarget| ≤ 2040 * ε :=
  PolynomialCubeLipschitz.cubic_fourteen_lipschitz rawTarget rawTarget_degree.le
    x y ε hε hx hy hxy rawTarget_coefficient_bound

end
end HeadComplexity.PureCubicCoefficientBounds
