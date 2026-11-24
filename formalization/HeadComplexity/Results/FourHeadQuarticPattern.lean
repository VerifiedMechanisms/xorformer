import HeadComplexity.Polynomial.FourHeadBooleanFace
import HeadComplexity.Polynomial.FourHeadQuarticFace
import HeadComplexity.Results.FourHeadLocalPattern

set_option linter.style.header false

/-!
# An adaptive quartic-face lower bound against every vanilla four-head model

Fifty-six negative parity faces force the off-diagonal quartic cross coefficients
negative. Eight positive parity faces with a tied eight-coordinate block force
positive column sums. Background coordinates may be chosen separately on
every face. The existing affine-fraction equivalence supplies the unchanged
original architectural model, including constant heads.
-/

namespace HeadComplexity.FourHeadQuarticPattern

noncomputable section

open Finset FourHeadBooleanFace FourHeadQuarticFace
open scoped BigOperators

def X : Fin 8 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7]
def Y : Fin 8 → Fin 14 := ![8, 8, 8, 8, 9, 9, 9, 9]
def Z : Fin 8 → Fin 14 := ![10, 10, 11, 11, 10, 10, 11, 11]
def W : Fin 8 → Fin 14 := ![12, 13, 12, 13, 12, 13, 12, 13]
def Xset : Finset (Fin 14) := {0, 1, 2, 3, 4, 5, 6, 7}

theorem X_ne_Y (i p : Fin 8) : X i ≠ Y p := by fin_cases i <;> fin_cases p <;> decide
theorem X_ne_Z (i p : Fin 8) : X i ≠ Z p := by fin_cases i <;> fin_cases p <;> decide
theorem X_ne_W (i p : Fin 8) : X i ≠ W p := by fin_cases i <;> fin_cases p <;> decide
theorem Y_ne_W (p : Fin 8) : Y p ≠ W p := by fin_cases p <;> decide
theorem Z_ne_W (p : Fin 8) : Z p ≠ W p := by fin_cases p <;> decide
theorem W_not_Xset (p : Fin 8) : W p ∉ Xset := by fin_cases p <;> decide
theorem Y_ne_Z (p : Fin 8) : Y p ≠ Z p := by fin_cases p <;> decide
theorem Y_not_Xset (p : Fin 8) : Y p ∉ Xset := by fin_cases p <;> decide
theorem Z_not_Xset (p : Fin 8) : Z p ∉ Xset := by fin_cases p <;> decide

theorem sum_Xset (a : Fin 14 → ℝ) : (∑ i ∈ Xset, a i) = ∑ i, a (X i) := by
  simp [Xset, X, Fin.sum_univ_succ]

def Pattern (f : (Fin 14 → Bool) → Bool) : Prop :=
  (∀ i p : Fin 8, i ≠ p → ∃ base, FaceLabel f {X i} (Y p) (Z p) (W p) base false) ∧
    ∀ p : Fin 8, ∃ base, FaceLabel f Xset (Y p) (Z p) (W p) base true

def FixedPattern (f : (Fin 14 → Bool) → Bool) : Prop :=
  (∀ i p : Fin 8, i ≠ p → FaceLabel f {X i} (Y p) (Z p) (W p) (fun _ ↦ false) false) ∧
    ∀ p : Fin 8, FaceLabel f Xset (Y p) (Z p) (W p) (fun _ ↦ true) true

theorem FixedPattern.pattern {f : (Fin 14 → Bool) → Bool} (h : FixedPattern f) : Pattern f :=
  ⟨fun i p hip ↦ ⟨fun _ ↦ false, h.1 i p hip⟩, fun p ↦ ⟨fun _ ↦ true, h.2 p⟩⟩

def clearedFunction {n : ℕ} (r : Fin 4 → AffineFraction n) (c : ℝ)
    (x : Fin n → Bool) : ℝ :=
  FourHeadSelectorQuadratic.cleared c (fun h ↦ (r h).numerator x) (fun h ↦ (r h).denominator x)

theorem clearedFunction_sign {n : ℕ} (r : Fin 4 → AffineFraction n) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true) (x : Fin n → Bool) :
    0 < clearedFunction r c x ↔ f x = true := by
  have hp (h) : 0 < (r h).denominator x := (hr h).1 x
  unfold clearedFunction
  rw [FourHeadSelectorQuadratic.cleared_eq _ _ _ (fun h ↦ (hp h).ne')]
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2)) (hp 3))]
  exact hf x

theorem clearedFunction_face {n : ℕ} (r : Fin 4 → AffineFraction n) (c : ℝ)
    (I : Finset (Fin n)) (j k l : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hl : l ∉ I)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (base : Fin n → Bool) (a b d e : Bool) :
    clearedFunction r c (blockFace I j k l base a b d e) =
      FourHeadQuarticFace.face c
        (fun h ↦ faceConstant (r h).b (r h).A I j k l base)
        (fun h ↦ faceConstant (r h).d (r h).C I j k l base)
        (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
        (fun h ↦ (r h).A l)
        (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k)
        (fun h ↦ (r h).C l)
        (boolToReal a) (boolToReal b) (boolToReal d) (boolToReal e) := by
  unfold clearedFunction FourHeadQuarticFace.face
  congr 1
  · funext h
    unfold AffineFraction.numerator
    rw [affine_blockFace _ _ _ _ _ _ hj hk hl hjk hjl hkl]
    ring
  · funext h
    unfold AffineFraction.denominator
    rw [affine_blockFace _ _ _ _ _ _ hj hk hl hjk hjl hkl]
    ring

theorem alternating_clearedFunction {n : ℕ} (r : Fin 4 → AffineFraction n) (c : ℝ)
    (I : Finset (Fin n)) (j k l : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hl : l ∉ I)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (base : Fin n → Bool) :
    FourHeadBooleanFace.alternating
      (fun a b d e ↦ clearedFunction r c (blockFace I j k l base a b d e)) =
      coefficient c
        (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
        (fun h ↦ (r h).A l)
        (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k)
        (fun h ↦ (r h).C l) := by
  have he := FourHeadQuarticFace.alternating_face c
    (fun h ↦ faceConstant (r h).b (r h).A I j k l base)
    (fun h ↦ faceConstant (r h).d (r h).C I j k l base)
    (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j)
    (fun h ↦ (r h).A k)
        (fun h ↦ (r h).A l)
    (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j)
    (fun h ↦ (r h).C k)
        (fun h ↦ (r h).C l)
  rw [← he]
  simp only [FourHeadBooleanFace.alternating, ThreeHeadBooleanFace.alternating,
    clearedFunction_face r c I j k l hj hk hl hjk hjl hkl,
    boolToReal, Bool.false_eq_true, ite_false, ite_true, FourHeadQuarticFace.alternating]
  ring

theorem coefficient_positive {n : ℕ} (r : Fin 4 → AffineFraction n) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true)
    (I : Finset (Fin n)) (j k l : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hl : l ∉ I)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (base : Fin n → Bool) (hface : FaceLabel f I j k l base true) :
    0 < coefficient c
      (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
        (fun h ↦ (r h).A l)
      (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k)
        (fun h ↦ (r h).C l) := by
  rw [← alternating_clearedFunction r c I j k l hj hk hl hjk hjl hkl base]
  apply alternating_pos
  intro a b d e
  rw [clearedFunction_sign r c hr f hf]
  rw [hface a b d e]
  simp

theorem coefficient_negative {n : ℕ} (r : Fin 4 → AffineFraction n) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true)
    (I : Finset (Fin n)) (j k l : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hl : l ∉ I)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (base : Fin n → Bool) (hface : FaceLabel f I j k l base false) :
    coefficient c
      (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
        (fun h ↦ (r h).A l)
      (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k)
        (fun h ↦ (r h).C l) < 0 := by
  rw [← alternating_clearedFunction r c I j k l hj hk hl hjk hjl hkl base]
  apply alternating_neg
  intro a b d e
  rw [clearedFunction_sign r c hr f hf]
  rw [hface a b d e]
  simp

theorem not_computable_four (f : (Fin 14 → Bool) → Bool) (hf : Pattern f) :
    ¬ computableWithHeadsN 14 4 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 4 f).mp hc
  apply ThreeHeadTripartiteCross.uniform_obstruction
    (fun h i ↦ (r h).A (X i)) (fun h i ↦ (r h).C (X i))
    (fun h p ↦ middle c (fun j ↦ (r j).A (Y p)) (fun j ↦ (r j).A (Z p))
      (fun j ↦ (r j).A (W p)) (fun j ↦ (r j).C (Y p))
      (fun j ↦ (r j).C (Z p)) (fun j ↦ (r j).C (W p)) h)
    (fun h p ↦ triple (fun j ↦ (r j).C (Y p)) (fun j ↦ (r j).C (Z p))
      (fun j ↦ (r j).C (W p)) h)
  · intro h
    rcases (hr h).2.1 with hp | hn | hz
    · exact Or.inl (fun i ↦ hp _)
    · exact Or.inr (Or.inl (fun i ↦ hn _))
    · exact Or.inr (Or.inr (fun i ↦ hz _))
  · exact triple_uniform (fun h ↦ (r h).C) (fun h ↦ (hr h).2.1) Y Z W
  · intro i p hip
    obtain ⟨base, hb⟩ := hf.1 i p hip
    have hn := coefficient_negative r c hr f hsign {X i} (Y p) (Z p) (W p)
      (by simpa using (X_ne_Y i p).symm) (by simpa using (X_ne_Z i p).symm)
      (by simpa using (X_ne_W i p).symm) (Y_ne_Z p) (Y_ne_W p) (Z_ne_W p) base hb
    simpa only [Finset.sum_singleton, coefficient] using hn.le
  · intro p
    obtain ⟨base, hb⟩ := hf.2 p
    have hp := coefficient_positive r c hr f hsign Xset (Y p) (Z p) (W p)
      (Y_not_Xset p) (Z_not_Xset p) (W_not_Xset p) (Y_ne_Z p) (Y_ne_W p) (Z_ne_W p) base hb
    simp only [sum_Xset] at hp
    rw [coefficient_sum_X] at hp
    exact hp

theorem HStar_ge_five (f : (Fin 14 → Bool) → Bool) (hf : Pattern f) : 5 ≤ HStar 14 f := by
  by_contra h
  have hle : HStar 14 f ≤ 4 := by omega
  apply not_computable_four f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 4 f).mpr
  exact FourHeadLocalPattern.affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

end

end HeadComplexity.FourHeadQuarticPattern
