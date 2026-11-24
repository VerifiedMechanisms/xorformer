import HeadComplexity.Polynomial.CubicCoefficientHessian
import HeadComplexity.Polynomial.SymmetricCubicRecovery
import HeadComplexity.Polynomial.ExplicitCubicRawGap

set_option linter.style.header false

/-!
# Actual cubic derivative tensors and ordinary coefficients

This connects the symmetric tensor recovery statements to MvPolynomial
coefficients, including repeated-index multiplicities and evaluated Hessians.
-/

namespace HeadComplexity.CubicDerivativeTensor
noncomputable section
open scoped BigOperators
open MvPolynomial CubicCoefficientHessian GenericCubicHessianPullback

def tensor {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (i j k : Fin n) : ℝ :=
  coeff 0 (pderiv k (pderiv i (pderiv j p)))

theorem tensor_symmetric {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    SymmetricCubicRecovery.Symmetric (tensor p) := by
  constructor
  · intro i j k
    unfold tensor
    rw [third_coeff_formula, third_coeff_formula]
    by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp_all [Finsupp.add_apply, add_comm, add_left_comm]
  · intro i j k
    unfold tensor
    rw [third_coeff_formula, third_coeff_formula]
    by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp_all [Finsupp.add_apply, add_comm, add_left_comm]

theorem slice_eq_hessian {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3) (k : Fin n) :
    SymmetricCubicRecovery.slice (tensor p) k = polynomialHessian p (Pi.single k 1) := by
  ext i j
  symm
  rw [polynomialHessian, eval_hessian_eq_sum p hp]
  simp [SymmetricCubicRecovery.slice, tensor, Pi.single_apply]

theorem cubic_tensor_rank_le_six {n : ℕ} (S B : Fin 3 → Fin n → ℝ) (k : Fin n) :
    (SymmetricCubicRecovery.slice (tensor (cubic S B)) k).rank ≤ 6 := by
  rw [slice_eq_hessian _ (ExplicitCubicRawGap.cubic_homogeneous _ _)]
  exact hessian_rank_le_six _ _ _

theorem tensor_squarefree {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tensor p i j k = coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1) p := by
  rw [tensor, third_coeff_formula]
  simp [hij, hik, hjk, eq_comm]

theorem degree_three_decomposition {n : ℕ} (d : Fin n →₀ ℕ) (hd : d.degree = 3) :
    ∃ i j k : Fin n, d = Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1 := by
  obtain ⟨a, ha, hda⟩ := Finsupp.exists_le_degree_eq d 1 (by omega)
  obtain ⟨b, rfl⟩ := le_iff_exists_add.mp ha
  have hdb : b.degree = 2 := by
    simp only [map_add, hda] at hd
    omega
  have ha' : a ∈ Set.range (fun i : Fin n ↦ Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hda
  obtain ⟨i, rfl⟩ := ha'
  obtain ⟨c, hc, hdc⟩ := Finsupp.exists_le_degree_eq b 1 (by omega)
  obtain ⟨d, rfl⟩ := le_iff_exists_add.mp hc
  have hdd : d.degree = 1 := by
    simp only [map_add, hdc] at hdb
    omega
  have hc' : c ∈ Set.range (fun j : Fin n ↦ Finsupp.single j 1) := by
    rw [Finsupp.range_single_one]
    exact hdc
  have hd' : d ∈ Set.range (fun k : Fin n ↦ Finsupp.single k 1) := by
    rw [Finsupp.range_single_one]
    exact hdd
  obtain ⟨j, rfl⟩ := hc'
  obtain ⟨k, rfl⟩ := hd'
  exact ⟨i, j, k, by ac_rfl⟩

theorem coefficient_abs_le_tensor {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (i j k : Fin n) :
    |coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1) p| ≤
      |tensor p i j k| := by
  rw [tensor, third_coeff_formula, abs_mul, abs_mul]
  have ha : (1 : ℝ) ≤ |(((Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 : ℕ) : ℝ)| := by
    simp only [Nat.abs_cast]
    exact_mod_cast (show 1 ≤ (Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 by omega)
  have hb : (1 : ℝ) ≤
      |(((Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 : ℕ) : ℝ)| := by
    simp only [Nat.abs_cast]
    exact_mod_cast (show 1 ≤ (Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 by omega)
  have hab : (1 : ℝ) ≤
      |(((Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 : ℕ) : ℝ)| *
      |(((Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 : ℕ) : ℝ)| := by
    nlinarith
  exact le_mul_of_one_le_left (abs_nonneg _) hab

theorem coefficients_abs_le_of_tensor {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3) (E : ℝ) (hE : 0 ≤ E)
    (ht : ∀ i j k, |tensor p i j k| ≤ E) : ∀ d, |coeff d p| ≤ E := by
  intro d
  by_cases hd : d.degree = 3
  · obtain ⟨i, j, k, rfl⟩ := degree_three_decomposition d hd
    exact (coefficient_abs_le_tensor p i j k).trans (ht i j k)
  · rw [hp.coeff_eq_zero hd, abs_zero]
    exact hE

theorem coefficient_difference_le_of_tensor {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (E : ℝ) (hE : 0 ≤ E)
    (ht : ∀ i j k, |tensor p i j k - tensor q i j k| ≤ E) :
    ∀ d, |coeff d p - coeff d q| ≤ E := by
  have hh := coefficients_abs_le_of_tensor (p - q) (hp.sub hq) E hE
    (by simpa only [tensor, map_sub, coeff_sub] using ht)
  simpa only [coeff_sub] using hh


theorem tensor_product {n : ℕ} (u v w : Fin n → ℝ) (i j k : Fin n) :
    tensor (linearPolynomial u * linearPolynomial v * linearPolynomial w) i j k =
      u i * v j * w k + u i * v k * w j + u j * v i * w k +
      u j * v k * w i + u k * v i * w j + u k * v j * w i := by
  have hp : (linearPolynomial u * linearPolynomial v * linearPolynomial w).IsHomogeneous 3 :=
    ((ExplicitCubicRawGap.linearPolynomial_homogeneous u).mul
      (ExplicitCubicRawGap.linearPolynomial_homogeneous v)).mul
      (ExplicitCubicRawGap.linearPolynomial_homogeneous w)
  have hh := congrFun (congrFun (slice_eq_hessian _ hp k) i) j
  change tensor _ i j k = _ at hh
  rw [hh]
  simp [polynomialHessian, linearValue, Pi.single_apply]
  ring

theorem triple_abs_le_one (a b c : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |a * b * c| ≤ 1 := by
  rw [abs_mul, abs_mul]
  calc
    |a| * |b| * |c| ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

theorem tensor_product_abs_le_six {n : ℕ} (u v w : Fin n → ℝ)
    (hu : ∀ i, |u i| ≤ 1) (hv : ∀ i, |v i| ≤ 1) (hw : ∀ i, |w i| ≤ 1)
    (i j k : Fin n) :
    |tensor (linearPolynomial u * linearPolynomial v * linearPolynomial w) i j k| ≤ 6 := by
  rw [tensor_product]
  have h (a b c) := triple_abs_le_one (u a) (v b) (w c) (hu a) (hv b) (hw c)
  linarith [h i j k, h i k j, h j i k, h j k i, h k i j, h k j i,
    abs_add_le (u i * v j * w k) (u i * v k * w j),
    abs_add_le (u i * v j * w k + u i * v k * w j) (u j * v i * w k),
    abs_add_le (u i * v j * w k + u i * v k * w j + u j * v i * w k)
      (u j * v k * w i),
    abs_add_le (u i * v j * w k + u i * v k * w j + u j * v i * w k +
      u j * v k * w i) (u k * v i * w j),
    abs_add_le (u i * v j * w k + u i * v k * w j + u j * v i * w k +
      u j * v k * w i + u k * v i * w j) (u k * v j * w i)]

theorem tensor_add {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) (i j k : Fin n) :
    tensor (p + q) i j k = tensor p i j k + tensor q i j k := by
  simp only [tensor, map_add, coeff_add]

theorem cubic_tensor_abs_le_eighteen {n : ℕ} (S B : Fin 3 → Fin n → ℝ)
    (hS : ∀ h i, |S h i| ≤ 1) (hB : ∀ h i, |B h i| ≤ 1) (i j k : Fin n) :
    |tensor (cubic S B) i j k| ≤ 18 := by
  unfold cubic
  rw [tensor_add, tensor_add]
  have h0 := tensor_product_abs_le_six (S 0) (B 1) (B 2) (hS 0) (hB 1) (hB 2) i j k
  have h1 := tensor_product_abs_le_six (S 1) (B 0) (B 2) (hS 1) (hB 0) (hB 2) i j k
  have h2 := tensor_product_abs_le_six (S 2) (B 0) (B 1) (hS 2) (hB 0) (hB 1) i j k
  exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans (by linarith))

end
end HeadComplexity.CubicDerivativeTensor
