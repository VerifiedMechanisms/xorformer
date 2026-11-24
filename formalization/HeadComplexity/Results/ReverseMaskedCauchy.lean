import HeadComplexity.Results.ReverseBalancedRows

set_option linter.style.header false

/-!
# Masked Cauchy queries with exact Boolean axis cancellation

Two heads per moving pole implement an arbitrary fixed mask on the queries.
The common positive column slope makes every denominator slope strict,
including masked-out entries. No shattering assertion is made here.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

private theorem paired_negative_pos {n : ℕ} (C : ℝ) (b : Fin n → ℝ)
    (hb : ∀ k, b k < 0) (hC : (∑ k, -b k) < C) (bits : Fin n → Bool) :
    0 < affineValue C b bits := by
  have hs : (∑ k, b k) ≤ ∑ k, b k * boolToReal (bits k) := by
    apply Finset.sum_le_sum
    intro k _
    cases bits k <;> simp [boolToReal, (hb k).le]
  simp only [Finset.sum_neg_distrib] at hC
  unfold affineValue
  linarith

private theorem paired_num_eval {r s : ℕ} (a : Fin r → ℝ)
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue 0 (Fin.addCases a (fun _ ↦ 0)) (Fin.addCases z w) =
      ∑ i, a i * boolToReal (z i) := by
  simp [affineValue, Fin.sum_univ_add]

private theorem paired_den_eval {r s : ℕ} (C : ℝ) (p : Fin r → ℝ)
    (u : Fin s → ℝ) (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue C (Fin.addCases (fun i ↦ -p i) (fun j ↦ -u j))
      (Fin.addCases z w) =
        C - (∑ i, p i * boolToReal (z i)) - ∑ j, u j * boolToReal (w j) := by
  simp [affineValue, Fin.sum_univ_add]
  ring

/-- Pairwise cancellation permits independently moving row poles.
Unlike global balancing, it needs no equality between different heads. -/
noncomputable def pairedRowsAxisData {r s H : ℕ}
    (C : ℝ) (p a : Fin H → Fin r → ℝ) (u v : Fin H → Fin s → ℝ)
    (hp : ∀ h i, 0 < p h i) (hu : ∀ h j, 0 < u h j) (hv : ∀ h j, 0 < v h j)
    (hCu : ∀ h, (∑ i, p h i) + (∑ j, u h j) < C)
    (hCv : ∀ h, (∑ i, p h i) + (∑ j, v h j) < C) :
    ReverseAxisData r s (H + H) := by
  let P : Fin (H + H) → Fin r → ℝ := Fin.addCases p p
  let U : Fin (H + H) → Fin s → ℝ := Fin.addCases u v
  let A : Fin (H + H) → Fin r → ℝ := Fin.addCases a (fun h i ↦ -a h i)
  have hP : ∀ h i, 0 < P h i := by
    intro h i
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) h
    · simpa [P] using hp k i
    · simpa [P, -Fin.natAdd_eq_addNat] using hp k i
  have hU : ∀ h j, 0 < U h j := by
    intro h j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) h
    · simpa [U] using hu k j
    · simpa [U, -Fin.natAdd_eq_addNat] using hv k j
  have hB : ∀ h, (∑ i, P h i) + (∑ j, U h j) < C := by
    intro h
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) h
    · simpa [P, U] using hCu k
    · simpa [P, U, -Fin.natAdd_eq_addNat] using hCv k
  let B : Fin (H + H) → Fin (r + s) → ℝ :=
    fun h ↦ Fin.addCases (fun i ↦ -P h i) (fun j ↦ -U h j)
  have hneg : ∀ h k, B h k < 0 := by
    intro h k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa [B] using neg_neg_of_pos (hP h i)
    · simpa [B] using neg_neg_of_pos (hU h j)
  have hbudget (h : Fin (H + H)) : (∑ k, -B h k) < C := by
    simpa [B, Fin.sum_univ_add, add_comm] using hB h
  refine
    { a₀ := fun _ ↦ 0
      b₀ := fun _ ↦ C
      a := fun h ↦ Fin.addCases (A h) (fun _ ↦ 0)
      b := B
      positive := fun h bits ↦ paired_negative_pos C (B h) (hneg h) (hbudget h) bits
      negative := hneg
      zero_left := ?_
      zero_right := ?_ }
  · intro w
    simp [paired_num_eval, boolToReal]
  · intro z
    change (∑ h : Fin (H + H),
      affineValue 0 (Fin.addCases (A h) (fun _ ↦ 0))
        (Fin.addCases z (fun _ ↦ false)) /
      affineValue C (B h) (Fin.addCases z (fun _ ↦ false))) = 0
    dsimp [B]
    simp_rw [paired_num_eval, paired_den_eval]
    simp only [show boolToReal false = 0 from rfl, mul_zero,
      Finset.sum_const_zero, sub_zero]
    simp [A, P, Fin.sum_univ_add, neg_mul, neg_div,
      Finset.sum_neg_distrib, -Fin.natAdd_eq_addNat]

theorem pairedRowsAxisData_grid {r s H : ℕ}
    (C : ℝ) (p a : Fin H → Fin r → ℝ) (u v : Fin H → Fin s → ℝ)
    (hp : ∀ h i, 0 < p h i) (hu : ∀ h j, 0 < u h j) (hv : ∀ h j, 0 < v h j)
    (hCu : ∀ h, (∑ i, p h i) + (∑ j, u h j) < C)
    (hCv : ∀ h, (∑ i, p h i) + (∑ j, v h j) < C) (i : Fin r) (j : Fin s) :
    (pairedRowsAxisData C p a u v hp hu hv hCu hCv).score (localGrid i j) =
      ∑ h, (a h i / (C - p h i - u h j) - a h i / (C - p h i - v h j)) := by
  have hn (b : Fin r → ℝ) :
      affineValue 0 (Fin.addCases b (fun _ : Fin s ↦ 0)) (localGrid i j) = b i := by
    unfold localGrid
    rw [paired_num_eval]
    simp [boolToReal]
  have hd (b : Fin r → ℝ) (c : Fin s → ℝ) :
      affineValue C (Fin.addCases (fun i ↦ -b i) (fun j ↦ -c j)) (localGrid i j) =
        C - b i - c j := by
    unfold localGrid
    rw [paired_den_eval]
    simp [boolToReal]
  simp only [pairedRowsAxisData, ReverseAxisData.score, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, hn, hd, neg_div,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- The exact paired identity is simple Cauchy after a row-only residue
rescaling. It is not an approximation by a squared kernel. -/
theorem paired_cauchy_identity (D q t a : ℝ) (hD : D ≠ 0)
    (hq : 1 - q ≠ 0) (htq : t - q ≠ 0) :
    D * (1 - q) * a / (D - D * q - D * (1 - t)) -
        D * (1 - q) * a / (D - D * q) = (1 - t) * a / (t - q) := by
  have hden₁ : D - D * q - D * (1 - t) = D * (t - q) := by ring
  have hden₂ : D - D * q = D * (1 - q) := by ring
  rw [hden₁, hden₂]
  field_simp
  ring

/-- Arbitrary fixed masks, independently moving row poles, strict slopes,
and full Boolean axis zeros cost exactly two heads per pole. The aggregate
budget is an explicit, checkable hypothesis, not just grid positivity. -/
theorem exists_maskedCauchy_reverseAxisData {r s H : ℕ}
    (D η : ℝ) (p a : Fin H → Fin r → ℝ) (t : Fin s → ℝ)
    (mask : Fin H → Fin s → Bool)
    (hD : 0 < D) (hη : 0 < η) (hp : ∀ h i, 0 < p h i)
    (ht : ∀ j, t j < 1) (hpt : ∀ h i j, p h i < t j)
    (hp1 : ∀ h i, p h i < 1)
    (hbudget : ∀ h,
      D * (∑ i, p h i) + (s : ℝ) * η +
        D * (∑ j, if mask h j then 1 - t j else 0) < D + η) :
    ∃ L : ReverseAxisData r s (H + H), ∀ i j,
      L.score (localGrid i j) = (1 - t j) *
        ∑ h, if mask h j then a h i / (t j - p h i) else 0 := by
  let P := fun h i ↦ D * p h i
  let A := fun h i ↦ D * (1 - p h i) * a h i
  let u := fun h j ↦ η + D * (if mask h j then 1 - t j else 0)
  let v := fun (_h : Fin H) (_j : Fin s) ↦ η
  have hP : ∀ h i, 0 < P h i := fun h i ↦ mul_pos hD (hp h i)
  have hmask (h : Fin H) (j : Fin s) :
      0 ≤ (if mask h j then 1 - t j else 0) := by
    split <;> simp_all [le_of_lt (ht j)]
  have hu : ∀ h j, 0 < u h j := by
    intro h j
    exact add_pos_of_pos_of_nonneg hη (mul_nonneg hD.le (hmask h j))
  have hv : ∀ h j, 0 < v h j := fun _ _ ↦ hη
  have hCu : ∀ h, (∑ i, P h i) + (∑ j, u h j) < D + η := by
    intro h
    simpa [P, u, Finset.mul_sum, Finset.sum_add_distrib, add_assoc] using hbudget h
  have hCv : ∀ h, (∑ i, P h i) + (∑ j, v h j) < D + η := by
    intro h
    calc
      _ ≤ (∑ i, P h i) + (∑ j, u h j) := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j _
        exact le_add_of_nonneg_right (mul_nonneg hD.le (hmask h j))
      _ < D + η := hCu h
  refine ⟨pairedRowsAxisData (D + η) P A u v hP hu hv hCu hCv, ?_⟩
  intro i j
  rw [pairedRowsAxisData_grid, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  dsimp [P, A, u, v]
  cases hm : mask h j
  · simp
  · simp only [↓reduceIte]
    have h₁ : D + η - D * p h i - (η + D * (1 - t j)) =
        D - D * p h i - D * (1 - t j) := by ring
    have h₂ : D + η - D * p h i - η = D - D * p h i := by ring
    rw [h₁, h₂]
    simpa only [mul_div_assoc] using paired_cauchy_identity D (p h i) (t j) (a h i)
      (ne_of_gt hD) (ne_of_gt (sub_pos.mpr (hp1 h i)))
      (ne_of_gt (sub_pos.mpr (hpt h i j)))

end AxisZeroGluing
end HeadComplexity
