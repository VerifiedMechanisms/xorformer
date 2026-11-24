import HeadComplexity.Results.FourHeadLocalPattern

set_option linter.style.header false

/-!
# A cross-only local obstruction to four vanilla heads

The middle-layer witnesses force positive cross-column sums without requiring
negative coefficients throughout either coordinate block. The 32 listed middle
witnesses have overlaps; the entire pattern prescribes 364 distinct inputs.
-/

namespace HeadComplexity.FourHeadLocalPattern

noncomputable section

open Finset PureRoPEThreeHead
open scoped BigOperators

def assemble (x y : Fin 8 → Bool) : Fin 16 → Bool :=
  ![x 0, y 0, x 1, y 1, x 2, y 2, x 3, y 3,
    x 4, y 4, x 5, y 5, x 6, y 6, x 7, y 7]

def middleBackground : Fin 8 → Fin 8 → Bool :=
  ![![false, true, true, true, false, false, false, false],
    ![true, false, true, true, false, false, false, false],
    ![true, true, false, true, false, false, false, false],
    ![true, true, true, false, false, false, false, false],
    ![true, true, true, false, false, false, false, false],
    ![true, true, true, false, false, false, false, false],
    ![true, true, true, false, false, false, false, false],
    ![true, true, true, false, false, false, false, false]]

def middleInput (j : Fin 8) (s a : Bool) : Fin 16 → Bool :=
  assemble (fun _ ↦ false)
    (Function.update (if s then middleBackground j else flip (middleBackground j)) j a)

def CrossOnlyPattern (f : (Fin 17 → Bool) → Bool) : Prop :=
  OrbitLabel f zeroInput false ∧
    (∀ i, OrbitLabel f (singleInput i) true) ∧
    (∀ i j : Fin 8, i ≠ j → OrbitLabel f (doubleInput (left i) (right j)) false) ∧
    (∀ j s, OrbitLabel f (middleInput j s true) false ∧
      OrbitLabel f (middleInput j s false) true)

theorem linear_assemble (u : Fin 16 → ℝ) (x y : Fin 8 → Bool) :
    linear u (assemble x y) = linear (fun i ↦ u (left i)) x +
      linear (fun i ↦ u (right i)) y := by
  simp [linear, assemble, left, right, Fin.sum_univ_succ]
  ring

theorem linear_middle (u : Fin 16 → ℝ) (j : Fin 8) (s a : Bool) :
    linear u (middleInput j s a) =
      linear (fun i ↦ u (left i)) (fun _ ↦ false) +
      spin s * (linear (fun i ↦ u (right i)) (middleBackground j) -
        u (right j) * spin (middleBackground j j)) + u (right j) * spin a := by
  unfold middleInput
  rw [linear_assemble, linear_update]
  cases s <;> cases a <;> cases hb : middleBackground j j <;>
    simp [linear_flip, spin, PureRoPEThreeHead.flip, hb] <;> ring

theorem linear_false {n : ℕ} (u : Fin n → ℝ) :
    linear u (fun _ ↦ false) = -(∑ i, u i) := by simp [linear, spin]

theorem cross_sum (A B : Fin 4 → Fin 16 → ℝ) (j : Fin 8) :
    (∑ i, crossCoefficient A B i j) =
      ∑ h, ((∑ i, A h (left i)) * B h (right j) +
        (∑ i, B h (left i)) * A h (right j)) := by
  unfold crossCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

theorem middle_difference (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ) (j : Fin 8) :
    productScore q A B (middleInput j true true) -
      productScore q A B (middleInput j true false) +
      productScore q A B (middleInput j false true) -
      productScore q A B (middleInput j false false) =
      -4 * ∑ i, crossCoefficient A B i j := by
  rw [cross_sum]
  simp only [productScore, linear_middle, linear_false, spin, Bool.false_eq_true,
    ite_false, ite_true, Fin.sum_univ_succ]
  ring

theorem quadratic_crossOnly_obstruction (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ)
    (hB : ∀ h, (∀ i, 0 < B h i) ∨ (∀ i, B h i = 0))
    (hz : productScore q A B zeroInput < 0)
    (hs : ∀ i, 0 < productScore q A B (singleInput i))
    (hc : ∀ i j : Fin 8, i ≠ j → productScore q A B (doubleInput (left i) (right j)) < 0)
    (hm : ∀ j s, productScore q A B (middleInput j s true) < 0 ∧
      0 < productScore q A B (middleInput j s false)) : False := by
  apply PositiveHalfRankCross.obstruction
    (fun h i ↦ A h (left i)) (fun h i ↦ B h (left i))
    (fun h j ↦ A h (right j)) (fun h j ↦ B h (right j))
  · intro h
    rcases hB h with h | h
    · exact Or.inl (fun i ↦ h _)
    · exact Or.inr (fun i ↦ h _)
  · intro h
    rcases hB h with h | h
    · exact Or.inl (fun i ↦ h _)
    · exact Or.inr (fun i ↦ h _)
  · intro i j hij
    have hidx : left i ≠ right j := by fin_cases i <;> fin_cases j <;> decide
    have he := product_face_difference q A B (left i) (right j) hidx
    linarith [hs (left i), hs (right j), hc i j hij]
  · intro j
    change 0 < ∑ i, crossCoefficient A B i j
    have he := middle_difference q A B j
    have h1 := hm j true
    have h2 := hm j false
    linarith

theorem crossOnly_not_computable_four (f : (Fin 17 → Bool) → Bool)
    (hf : CrossOnlyPattern f) : ¬ computableWithHeadsN 17 4 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 4 f).mp hc
  obtain ⟨q, A, B, hB, hq⟩ := exists_quadratic r c hr
  obtain ⟨A', B', hB', horient⟩ := orient_quadratic q A B hB
  have hq' (x) : extractedFunction r c x = productScore q A' B' x :=
    (hq x).trans (horient x)
  obtain ⟨hz, hs, hcross, hmiddle⟩ := hf
  apply quadratic_crossOnly_obstruction q A' B' hB'
  · rw [← hq']
    exact extractedFunction_negative r c hr f hsign _ hz
  · intro i
    rw [← hq']
    exact extractedFunction_positive r c hr f hsign _ (hs i)
  · intro i j hij
    rw [← hq']
    exact extractedFunction_negative r c hr f hsign _ (hcross i j hij)
  · intro j s
    constructor
    · rw [← hq']
      exact extractedFunction_negative r c hr f hsign _ (hmiddle j s).1
    · rw [← hq']
      exact extractedFunction_positive r c hr f hsign _ (hmiddle j s).2

theorem crossOnly_HStar_ge_five (f : (Fin 17 → Bool) → Bool) (hf : CrossOnlyPattern f) :
    5 ≤ HStar 17 f := by
  by_contra h
  have hle : HStar 17 f ≤ 4 := by omega
  apply crossOnly_not_computable_four f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 4 f).mpr
  exact affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

theorem crossOnly_SharedHStar_ge_five (f : (Fin 17 → Bool) → Bool)
    (hf : CrossOnlyPattern f) : 5 ≤ SharedHStar 17 f := by
  simpa only [SharedHStar_eq_HStar] using crossOnly_HStar_ge_five f hf

end

end HeadComplexity.FourHeadLocalPattern
