import HeadComplexity.Polynomial.ExplicitCubicSquarefreeGap
import HeadComplexity.Polynomial.CubeTopCoefficients
import HeadComplexity.Polynomial.PureCubicRawKernel
import HeadComplexity.Polynomial.ThreeHeadReplication

set_option linter.style.header false

/-! # The squarefree gap for arbitrary untied vanilla three-head mean polynomials -/

namespace HeadComplexity.ThreeHeadMeanGap
noncomputable section
open scoped BigOperators
open MvPolynomial GenericCubicHessianPullback CubicDerivativeTensor
open MeanGridCubic PureRoPEReplication PureCubicRawKernel

/-- A polynomial with specified affine coefficients on an arbitrary finite set. -/
def affine {α : Type*} [Fintype α] (c : ℝ) (a : α → ℝ) : MvPolynomial α ℝ :=
  C c + ∑ i, C (a i) * X i

theorem affine_degree {α : Type*} [Fintype α] (c : ℝ) (a : α → ℝ) :
    (affine c a).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

def cleared {α : Type*} (c : ℝ) (N D : Fin 3 → MvPolynomial α ℝ) : MvPolynomial α ℝ :=
  C c * D 0 * D 1 * D 2 + N 0 * D 1 * D 2 +
    N 1 * D 0 * D 2 + N 2 * D 0 * D 1

theorem cleared_degree {α : Type*} (c : ℝ) (N D : Fin 3 → MvPolynomial α ℝ)
    (hN : ∀ h, (N h).totalDegree ≤ 1) (hD : ∀ h, (D h).totalDegree ≤ 1) :
    (cleared c N D).totalDegree ≤ 3 := by
  have hp (A B C : MvPolynomial α ℝ) (hA : A.totalDegree ≤ 1)
      (hB : B.totalDegree ≤ 1) (hC : C.totalDegree ≤ 1) :
      (A * B * C).totalDegree ≤ 3 := by
    have h1 := totalDegree_mul A B
    have h2 := totalDegree_mul (A * B) C
    omega
  unfold cleared
  apply (totalDegree_add _ _).trans (max_le ?_ (hp _ _ _ (hN 2) (hD 0) (hD 1)))
  apply (totalDegree_add _ _).trans (max_le ?_ (hp _ _ _ (hN 1) (hD 0) (hD 2)))
  apply (totalDegree_add _ _).trans (max_le ?_ (hp _ _ _ (hN 0) (hD 1) (hD 2)))
  apply hp _ _ _ ?_ (hD 1) (hD 2)
  exact (totalDegree_mul _ _).trans (by simpa using hD 0)

theorem tensor_affine_product {n : ℕ} (a b c : ℝ) (u v w : Fin n → ℝ)
    (i j k : Fin n) :
    tensor ((C a + linearPolynomial u) * (C b + linearPolynomial v) *
      (C c + linearPolynomial w)) i j k =
    tensor (linearPolynomial u * linearPolynomial v * linearPolynomial w) i j k := by
  unfold tensor
  congr 1
  simp

theorem tensor_const_mul {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ)
    (i j k : Fin n) : tensor (C c * p) i j k = c * tensor p i j k := by
  simp [tensor, coeff_C_mul]

theorem tensor_cleared_affine {n : ℕ} (c : ℝ) (a d : Fin 3 → ℝ)
    (N E : Fin 3 → Fin n → ℝ) (i j k : Fin n) :
    tensor (cleared c (fun h ↦ affine (a h) (N h))
      (fun h ↦ affine (d h) (E h))) i j k =
    tensor (cubic N E + C c * linearPolynomial (E 0) * linearPolynomial (E 1) *
      linearPolynomial (E 2)) i j k := by
  change tensor (cleared c (fun h ↦ C (a h) + linearPolynomial (N h))
    (fun h ↦ C (d h) + linearPolynomial (E h))) i j k = _
  unfold cleared cubic
  simp only [tensor_add]
  rw [show C c * (C (d 0) + linearPolynomial (E 0)) *
      (C (d 1) + linearPolynomial (E 1)) * (C (d 2) + linearPolynomial (E 2)) =
      C c * ((C (d 0) + linearPolynomial (E 0)) *
      (C (d 1) + linearPolynomial (E 1)) * (C (d 2) + linearPolynomial (E 2))) by ring,
    show C c * linearPolynomial (E 0) * linearPolynomial (E 1) * linearPolynomial (E 2) =
      C c * (linearPolynomial (E 0) * linearPolynomial (E 1) * linearPolynomial (E 2)) by ring]
  simp only [tensor_const_mul, tensor_affine_product]
  ring

theorem affine_rename_groups {n m : ℕ} (c : ℝ) (a : Fin n × Fin m → ℝ) :
    rename Prod.fst (affine c a) = affine c (fun i ↦ ∑ r, a (i, r)) := by
  simp [affine, Fintype.sum_prod_type, Finset.sum_mul]

theorem cleared_rename {α β : Type*} (f : α → β) (c : ℝ)
    (N D : Fin 3 → MvPolynomial α ℝ) :
    rename f (cleared c N D) = cleared c (fun h ↦ rename f (N h))
      (fun h ↦ rename f (D h)) := by
  simp [cleared]

/-- The actual centered numerator/denominator coefficients of a vanilla family. -/
def numSlopes {m : ℕ} (r : Fin 3 → AffineFraction (14 * m))
    (h : Fin 3) (p : Fin 14 × Fin m) : ℝ := (r h).A (finProdFinEquiv p) / 2

def denSlopes {m : ℕ} (r : Fin 3 → AffineFraction (14 * m))
    (h : Fin 3) (p : Fin 14 × Fin m) : ℝ := (r h).C (finProdFinEquiv p) / 2

def numConstant {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (h : Fin 3) : ℝ :=
  (r h).b + ∑ p : Fin 14 × Fin m, numSlopes r h p

def denConstant {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (h : Fin 3) : ℝ :=
  (r h).d + ∑ p : Fin 14 × Fin m, denSlopes r h p

def spinCleared {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ) :
    MvPolynomial (Fin 14 × Fin m) ℝ :=
  cleared c (fun h ↦ affine (numConstant r h) (numSlopes r h))
    (fun h ↦ affine (denConstant r h) (denSlopes r h))

def meanCleared {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ) :
    MvPolynomial (Fin 14) ℝ := meanPolynomial (spinCleared r c)

def groupNumerator {m : ℕ} (r : Fin 3 → AffineFraction (14 * m))
    (h : Fin 3) (i : Fin 14) : ℝ := ∑ s, numSlopes r h (i, s)

def groupDenominator {m : ℕ} (r : Fin 3 → AffineFraction (14 * m))
    (h : Fin 3) (i : Fin 14) : ℝ := ∑ s, denSlopes r h (i, s)

theorem spinCleared_degree {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ) :
    (spinCleared r c).totalDegree ≤ 3 :=
  cleared_degree _ _ _ (fun _ ↦ affine_degree _ _) (fun _ ↦ affine_degree _ _)

theorem meanCleared_degree {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ) :
    (meanCleared r c).totalDegree ≤ 3 :=
  (meanPolynomial_degree _).trans (spinCleared_degree r c)

theorem groupDenominator_oriented {m : ℕ} (hm : 0 < m)
    (r : Fin 3 → AffineFraction (14 * m)) (hr : ∀ h, (r h).Admissible) :
    ∀ h, (∀ i, 0 < groupDenominator r h i) ∨
      (∀ i, groupDenominator r h i < 0) ∨ groupDenominator r h = 0 := by
  letI : NeZero m := ⟨by omega⟩
  intro h
  have hu : AffineFraction.UniformSign (groupDenominator r h) := by
    apply ThreeHeadReplication.uniform_group_sum
    rcases (hr h).2.1 with hp | hn | hz
    · exact Or.inl (fun p ↦ div_pos (hp _) (by norm_num))
    · exact Or.inr (Or.inl (fun p ↦ div_neg_of_neg_of_pos (hn _) (by norm_num)))
    · exact Or.inr (Or.inr (fun p ↦ by simp [denSlopes, hz]))
  rcases hu with hp | hn | hz
  · exact Or.inl hp
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr (funext hz))

theorem triple_exponent (i j k : Fin 14) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CubeTopCoefficients.exponent {i, j, k} =
      Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1 := by
  simp [CubeTopCoefficients.exponent, hij, hik, hjk]
  ac_rfl

theorem meanCleared_top_coefficient {m : ℕ} (hm : 2 < m)
    (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ)
    (i j k : Fin 14) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1) (meanCleared r c) =
    coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
      (cubic (groupNumerator r) (groupDenominator r) +
        C c * linearPolynomial (groupDenominator r 0) * linearPolynomial (groupDenominator r 1) *
          linearPolynomial (groupDenominator r 2)) := by
  have he := CubeTopCoefficients.meanPolynomial_cubic_coefficient hm (spinCleared r c)
    (spinCleared_degree r c) {i, j, k} (by simp [hij, hik, hjk])
  rw [triple_exponent i j k hij hik hjk] at he
  rw [show meanCleared r c = meanPolynomial (spinCleared r c) from rfl, he]
  simp only [spinCleared, cleared_rename, affine_rename_groups]
  rw [← tensor_squarefree _ i j k hij hik hjk, ← tensor_squarefree _ i j k hij hik hjk]
  exact tensor_cleared_affine _ _ _ _ _ _ _ _


theorem rawTarget_top_coefficient (i j k : Fin 14)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1) rawTarget =
      coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
        (cubic baseS baseB) := by
  have he : rawTarget = cleared 0 (fun h ↦ affine 0 (baseS h))
      (fun h ↦ affine 1 (baseB h)) := by
    simp [rawTarget_formula, cleared, affine, linearPolynomial]
  rw [he, ← tensor_squarefree _ i j k hij hik hjk,
    ← tensor_squarefree _ i j k hij hik hjk, tensor_cleared_affine]
  simp

theorem linearPolynomial_scale {n : ℕ} (a : ℝ) (v : Fin n → ℝ) :
    linearPolynomial (fun i ↦ a * v i) = C a * linearPolynomial v := by
  simp [linearPolynomial, Finset.mul_sum, mul_assoc]

theorem cubic_scale_readout {n : ℕ} (a c : ℝ) (N E : Fin 3 → Fin n → ℝ) :
    cubic (fun h i ↦ a * N h i) E + C (a * c) *
      linearPolynomial (E 0) * linearPolynomial (E 1) * linearPolynomial (E 2) =
    C a * (cubic N E + C c * linearPolynomial (E 0) *
      linearPolynomial (E 1) * linearPolynomial (E 2)) := by
  simp only [cubic, linearPolynomial_scale, map_mul]
  ring

/-- Every nonzero rescaling retains a strict squarefree gap. No positivity or
boundedness assumption on competing numerator coefficients is used. -/
theorem meanCleared_coefficient_gap {m : ℕ} (hm : 2 < m)
    (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (a : ℝ) (ha : a ≠ 0) :
    ∃ i j k : Fin 14, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      |a| * ExplicitCubicGapConstants.squarefreeRadius <
      |coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
          (meanCleared r c) - a *
        coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1) rawTarget| := by
  obtain ⟨i, j, k, hij, hik, hjk, hg⟩ :=
    ExplicitCubicSquarefreeGap.squarefree_coefficient_gap_with_readout
      (fun h i ↦ a⁻¹ * groupNumerator r h i) (groupDenominator r) (a⁻¹ * c)
      (groupDenominator_oriented (by omega) r hr)
  rw [cubic_scale_readout, coeff_C_mul,
    ← meanCleared_top_coefficient hm r c i j k hij hik hjk,
    ← rawTarget_top_coefficient i j k hij hik hjk] at hg
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  let d : Fin 14 →₀ ℕ := Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1
  have he : coeff d rawTarget - a⁻¹ * coeff d (meanCleared r c) =
      (a * coeff d rawTarget - coeff d (meanCleared r c)) / a := by
    field_simp
  change ExplicitCubicGapConstants.squarefreeRadius <
    |coeff d rawTarget - a⁻¹ * coeff d (meanCleared r c)| at hg
  rw [he, abs_div] at hg
  have hh := (lt_div_iff₀ (abs_pos.mpr ha)).mp hg
  simpa only [abs_sub_comm, mul_comm] using hh

/-- Conditional lower bound in exactly the coefficient form supplied by finite
mean-grid sign rigidity. -/
theorem not_meanCleared_close {m : ℕ} (hm : 2 < m)
    (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (a : ℝ) (ha : a ≠ 0)
    (hclose : ∀ d, |coeff d (meanCleared r c) - a * coeff d rawTarget| ≤
      |a| * ExplicitCubicGapConstants.squarefreeRadius) : False := by
  obtain ⟨i, j, k, _, _, _, hg⟩ := meanCleared_coefficient_gap hm r c hr a ha
  exact (not_lt_of_ge (hclose _)) hg

end
end HeadComplexity.ThreeHeadMeanGap
