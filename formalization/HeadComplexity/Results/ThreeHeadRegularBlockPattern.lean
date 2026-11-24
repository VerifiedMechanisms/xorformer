import HeadComplexity.Results.ThreeHeadTripartitePattern

set_option linter.style.header false

/-!
# Cubic parity-face obstructions with regular covers of the X coordinates

A row may move several coordinates together. Nonempty blocks preserve the
uniform denominator orientation. A regular cover makes the column sum a
positive multiple of the all-X tied coefficient.
-/

namespace HeadComplexity.ThreeHeadRegularBlockPattern

noncomputable section

open Finset ThreeHeadBooleanFace ThreeHeadTripartiteCross ThreeHeadTripartitePattern
open scoped BigOperators

def Pattern (blocks : Fin 6 → Finset (Fin 11)) (f : (Fin 11 → Bool) → Bool) : Prop :=
  (∀ i p : Fin 6, i ≠ p → ∃ base, FaceLabel f (blocks i) (Y p) (Z p) base false) ∧
    ∀ p : Fin 6, ∃ base, FaceLabel f Xset (Y p) (Z p) base true

def RegularCover (blocks : Fin 6 → Finset (Fin 11)) (weight : ℝ) : Prop :=
  0 < weight ∧ (∀ i, (blocks i).Nonempty) ∧ (∀ i, blocks i ⊆ Xset) ∧
    ∀ a : Fin 11 → ℝ, (∑ r, ∑ i ∈ blocks r, a i) = weight * ∑ i ∈ Xset, a i

theorem uniform_sum (B : Fin 11 → ℝ) (hB : AffineFraction.UniformSign B)
    (blocks : Fin 6 → Finset (Fin 11)) (hne : ∀ i, (blocks i).Nonempty) :
    AffineFraction.UniformSign (fun i ↦ ∑ j ∈ blocks i, B j) := by
  rcases hB with hp | hn | hz
  · exact Or.inl (fun i ↦ Finset.sum_pos (fun j _ ↦ hp j) (hne i))
  · exact Or.inr (Or.inl (fun i ↦ Finset.sum_neg (fun j _ ↦ hn j) (hne i)))
  · exact Or.inr (Or.inr (fun i ↦ by simp only [hz, Finset.sum_const_zero]))

theorem coefficient_smul_X (c weight : ℝ) (AX AY AZ BX BY BZ : Fin 3 → ℝ) :
    coefficient c (fun h ↦ weight * AX h) AY AZ (fun h ↦ weight * BX h) BY BZ =
      weight * coefficient c AX AY AZ BX BY BZ := by
  simp only [coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem coefficient_regular_cover (blocks : Fin 6 → Finset (Fin 11)) (weight : ℝ)
    (hcover : RegularCover blocks weight) (c : ℝ) (A B : Fin 3 → Fin 11 → ℝ)
    (p : Fin 6) :
    (∑ r, coefficient c (fun h ↦ ∑ i ∈ blocks r, A h i)
      (fun h ↦ A h (Y p)) (fun h ↦ A h (Z p)) (fun h ↦ ∑ i ∈ blocks r, B h i)
      (fun h ↦ B h (Y p)) (fun h ↦ B h (Z p))) =
    weight * coefficient c (fun h ↦ ∑ i ∈ Xset, A h i)
      (fun h ↦ A h (Y p)) (fun h ↦ A h (Z p)) (fun h ↦ ∑ i ∈ Xset, B h i)
      (fun h ↦ B h (Y p)) (fun h ↦ B h (Z p)) := by
  rw [← coefficient_sum_X]
  simp_rw [hcover.2.2.2]
  exact coefficient_smul_X _ _ _ _ _ _ _ _

theorem not_computable_three (blocks : Fin 6 → Finset (Fin 11)) (weight : ℝ)
    (hcover : RegularCover blocks weight) (f : (Fin 11 → Bool) → Bool)
    (hf : Pattern blocks f) : ¬ computableWithHeadsN 11 3 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 3 f).mp hc
  let AX (h : Fin 3) (i : Fin 6) := ∑ j ∈ blocks i, (r h).A j
  let BX (h : Fin 3) (i : Fin 6) := ∑ j ∈ blocks i, (r h).C j
  let AY (p : Fin 6) (h : Fin 3) := (r h).A (Y p)
  let AZ (p : Fin 6) (h : Fin 3) := (r h).A (Z p)
  let BY (p : Fin 6) (h : Fin 3) := (r h).C (Y p)
  let BZ (p : Fin 6) (h : Fin 3) := (r h).C (Z p)
  apply uniform_obstruction AX BX
    (fun h p ↦ middleFactor c (AY p) (AZ p) (BY p) (BZ p) h)
    (fun h p ↦ pairFactor (BY p) (BZ p) h)
  · exact fun h ↦ uniform_sum (r h).C (hr h).2.1 blocks hcover.2.1
  · exact pairFactor_uniform (fun h ↦ (r h).C) (fun h ↦ (hr h).2.1) Y Z
  · intro i p hip
    obtain ⟨base, hb⟩ := hf.1 i p hip
    have hn := coefficient_negative r c hr f hsign (blocks i) (Y p) (Z p)
      (fun h ↦ Y_not_Xset p (hcover.2.2.1 i h))
      (fun h ↦ Z_not_Xset p (hcover.2.2.1 i h)) (Y_ne_Z p) base hb
    exact hn.le
  · intro p
    obtain ⟨base, hb⟩ := hf.2 p
    have hp := coefficient_positive r c hr f hsign Xset (Y p) (Z p)
      (Y_not_Xset p) (Z_not_Xset p) (Y_ne_Z p) base hb
    change 0 < ∑ i, coefficient c (fun h ↦ AX h i) (AY p) (AZ p)
      (fun h ↦ BX h i) (BY p) (BZ p)
    rw [coefficient_regular_cover blocks weight hcover]
    exact mul_pos hcover.1 hp

theorem HStar_ge_four (blocks : Fin 6 → Finset (Fin 11)) (weight : ℝ)
    (hcover : RegularCover blocks weight) (f : (Fin 11 → Bool) → Bool)
    (hf : Pattern blocks f) : 4 ≤ HStar 11 f := by
  by_contra h
  have hle : HStar 11 f ≤ 3 := by omega
  apply not_computable_three blocks weight hcover f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 3 f).mpr
  exact FourHeadLocalPattern.affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

def complementBlocks (i : Fin 6) : Finset (Fin 11) := Xset.erase (X i)

theorem complementBlocks_regular : RegularCover complementBlocks 5 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · exact fun i ↦ Finset.erase_subset _ _
  · intro a
    simp [complementBlocks, Xset, X, Fin.sum_univ_succ]
    ring

def cyclicBlocks : Fin 6 → Finset (Fin 11) :=
  ![{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 0}, {4, 5, 1}, {5, 0, 2}]

theorem cyclicBlocks_regular : RegularCover cyclicBlocks 3 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro a
    simp [cyclicBlocks, Xset, Fin.sum_univ_succ]
    ring

end

end HeadComplexity.ThreeHeadRegularBlockPattern
