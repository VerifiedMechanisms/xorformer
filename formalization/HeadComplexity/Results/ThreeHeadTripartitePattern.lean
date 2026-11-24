import HeadComplexity.Polynomial.ThreeHeadBooleanFace
import HeadComplexity.Polynomial.ThreeHeadCubicFace
import HeadComplexity.Results.FourHeadLocalPattern

set_option linter.style.header false

/-!
# An adaptive cubic-face lower bound against every vanilla three-head model

Thirty negative parity faces force the off-diagonal cubic cross coefficients
negative. Six positive parity faces with a tied six-coordinate block force
positive column sums. Background coordinates may be chosen separately on
every face. The existing affine-fraction equivalence supplies the unchanged
original architectural model, including constant heads.
-/

namespace HeadComplexity.ThreeHeadTripartitePattern

noncomputable section

open Finset ThreeHeadBooleanFace ThreeHeadTripartiteCross
open scoped BigOperators

def X : Fin 6 → Fin 11 := ![0, 1, 2, 3, 4, 5]
def Y : Fin 6 → Fin 11 := ![6, 6, 6, 7, 7, 7]
def Z : Fin 6 → Fin 11 := ![8, 9, 10, 8, 9, 10]
def Xset : Finset (Fin 11) := {0, 1, 2, 3, 4, 5}

theorem X_ne_Y (i p : Fin 6) : X i ≠ Y p := by fin_cases i <;> fin_cases p <;> decide
theorem X_ne_Z (i p : Fin 6) : X i ≠ Z p := by fin_cases i <;> fin_cases p <;> decide
theorem Y_ne_Z (p : Fin 6) : Y p ≠ Z p := by fin_cases p <;> decide
theorem Y_not_Xset (p : Fin 6) : Y p ∉ Xset := by fin_cases p <;> decide
theorem Z_not_Xset (p : Fin 6) : Z p ∉ Xset := by fin_cases p <;> decide

theorem sum_Xset (a : Fin 11 → ℝ) : (∑ i ∈ Xset, a i) = ∑ i, a (X i) := by
  simp [Xset, X, Fin.sum_univ_succ]

def Pattern (f : (Fin 11 → Bool) → Bool) : Prop :=
  (∀ i p : Fin 6, i ≠ p → ∃ base, FaceLabel f {X i} (Y p) (Z p) base false) ∧
    ∀ p : Fin 6, ∃ base, FaceLabel f Xset (Y p) (Z p) base true

def FixedPattern (f : (Fin 11 → Bool) → Bool) : Prop :=
  (∀ i p : Fin 6, i ≠ p → FaceLabel f {X i} (Y p) (Z p) (fun _ ↦ false) false) ∧
    ∀ p : Fin 6, FaceLabel f Xset (Y p) (Z p) (fun _ ↦ true) true

theorem FixedPattern.pattern {f : (Fin 11 → Bool) → Bool} (h : FixedPattern f) : Pattern f :=
  ⟨fun i p hip ↦ ⟨fun _ ↦ false, h.1 i p hip⟩, fun p ↦ ⟨fun _ ↦ true, h.2 p⟩⟩

def clearedFunction {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (x : Fin n → Bool) : ℝ :=
  ThreeHeadCubicFace.cleared c (fun h ↦ (r h).numerator x) (fun h ↦ (r h).denominator x)

theorem clearedFunction_sign {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true) (x : Fin n → Bool) :
    0 < clearedFunction r c x ↔ f x = true := by
  have hp (h) : 0 < (r h).denominator x := (hr h).1 x
  unfold clearedFunction
  rw [ThreeHeadCubicFace.cleared_eq _ _ _ (fun h ↦ (hp h).ne')]
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2))]
  exact hf x

theorem clearedFunction_face {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (I : Finset (Fin n)) (j k : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hjk : j ≠ k)
    (base : Fin n → Bool) (a b d : Bool) :
    clearedFunction r c (blockFace I j k base a b d) =
      ThreeHeadCubicFace.face c
        (fun h ↦ faceConstant (r h).b (r h).A I j k base)
        (fun h ↦ faceConstant (r h).d (r h).C I j k base)
        (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
        (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k)
        (boolToReal a) (boolToReal b) (boolToReal d) := by
  unfold clearedFunction ThreeHeadCubicFace.face
  congr 1
  · funext h
    unfold AffineFraction.numerator
    rw [affine_blockFace _ _ _ _ _ hj hk hjk]
    ring
  · funext h
    unfold AffineFraction.denominator
    rw [affine_blockFace _ _ _ _ _ hj hk hjk]
    ring

theorem alternating_clearedFunction {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (I : Finset (Fin n)) (j k : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hjk : j ≠ k)
    (base : Fin n → Bool) :
    alternating (fun a b d ↦ clearedFunction r c (blockFace I j k base a b d)) =
      coefficient c
        (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
        (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k) := by
  simp only [alternating, clearedFunction_face r c I j k hj hk hjk,
    boolToReal, Bool.false_eq_true, ite_false, ite_true]
  exact ThreeHeadCubicFace.alternating_face _ _ _ _ _ _ _ _ _

theorem coefficient_positive {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true)
    (I : Finset (Fin n)) (j k : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hjk : j ≠ k)
    (base : Fin n → Bool) (hface : FaceLabel f I j k base true) :
    0 < coefficient c
      (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
      (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k) := by
  rw [← alternating_clearedFunction r c I j k hj hk hjk base]
  apply alternating_pos
  intro a b d
  rw [clearedFunction_sign r c hr f hf]
  rw [hface a b d]
  simp

theorem coefficient_negative {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true)
    (I : Finset (Fin n)) (j k : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hjk : j ≠ k)
    (base : Fin n → Bool) (hface : FaceLabel f I j k base false) :
    coefficient c
      (fun h ↦ ∑ i ∈ I, (r h).A i) (fun h ↦ (r h).A j) (fun h ↦ (r h).A k)
      (fun h ↦ ∑ i ∈ I, (r h).C i) (fun h ↦ (r h).C j) (fun h ↦ (r h).C k) < 0 := by
  rw [← alternating_clearedFunction r c I j k hj hk hjk base]
  apply alternating_neg
  intro a b d
  rw [clearedFunction_sign r c hr f hf]
  rw [hface a b d]
  simp

theorem not_computable_three (f : (Fin 11 → Bool) → Bool) (hf : Pattern f) :
    ¬ computableWithHeadsN 11 3 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 3 f).mp hc
  apply ThreeHeadTripartiteCross.obstruction c (fun h ↦ (r h).A) (fun h ↦ (r h).C)
    (fun h ↦ (hr h).2.1) X Y Z
  · intro i p hip
    obtain ⟨base, hb⟩ := hf.1 i p hip
    have hn := coefficient_negative r c hr f hsign {X i} (Y p) (Z p)
      (by simpa using (X_ne_Y i p).symm) (by simpa using (X_ne_Z i p).symm)
      (Y_ne_Z p) base hb
    simpa only [Finset.sum_singleton] using hn.le
  · intro p
    obtain ⟨base, hb⟩ := hf.2 p
    have hp := coefficient_positive r c hr f hsign Xset (Y p) (Z p)
      (Y_not_Xset p) (Z_not_Xset p) (Y_ne_Z p) base hb
    simp only [sum_Xset] at hp
    rw [coefficient_sum_X] at hp
    exact hp

theorem HStar_ge_four (f : (Fin 11 → Bool) → Bool) (hf : Pattern f) : 4 ≤ HStar 11 f := by
  by_contra h
  have hle : HStar 11 f ≤ 3 := by omega
  apply not_computable_three f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 3 f).mpr
  exact FourHeadLocalPattern.affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

end

end HeadComplexity.ThreeHeadTripartitePattern
