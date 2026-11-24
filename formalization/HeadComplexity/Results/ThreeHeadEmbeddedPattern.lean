import HeadComplexity.Results.ThreeHeadTripartitePattern

set_option linter.style.header false

/-!
# Cubic face obstructions with arbitrarily many auxiliary coordinates

The first eleven coordinates carry the cubic cross matrix. Each witness may
fix every remaining coordinate independently. Since the cleared polynomial
has degree at most three, auxiliary backgrounds do not change the extracted
cubic coefficients.
-/

namespace HeadComplexity.ThreeHeadEmbeddedPattern

noncomputable section

open Finset ThreeHeadBooleanFace ThreeHeadTripartiteCross ThreeHeadTripartitePattern
open scoped BigOperators

def embed {n : ℕ} (hn : 11 ≤ n) (i : Fin 11) : Fin n := ⟨i, lt_of_lt_of_le i.isLt hn⟩

theorem embed_injective {n : ℕ} (hn : 11 ≤ n) : Function.Injective (embed hn) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) h)

def coreSet {n : ℕ} (hn : 11 ≤ n) : Finset (Fin n) := Xset.image (embed hn)

theorem Y_not_coreSet {n : ℕ} (hn : 11 ≤ n) (p : Fin 6) : embed hn (Y p) ∉ coreSet hn := by
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  exact Y_not_Xset p ((embed_injective hn he) ▸ hi)

theorem Z_not_coreSet {n : ℕ} (hn : 11 ≤ n) (p : Fin 6) : embed hn (Z p) ∉ coreSet hn := by
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  exact Z_not_Xset p ((embed_injective hn he) ▸ hi)

theorem sum_coreSet {n : ℕ} (hn : 11 ≤ n) (a : Fin n → ℝ) :
    (∑ i ∈ coreSet hn, a i) = ∑ i, a (embed hn (X i)) := by
  rw [coreSet, Finset.sum_image]
  · exact sum_Xset (fun i ↦ a (embed hn i))
  · exact fun _ _ _ _ h ↦ embed_injective hn h

def Pattern {n : ℕ} (hn : 11 ≤ n) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ i p : Fin 6, i ≠ p → ∃ base,
    FaceLabel f {embed hn (X i)} (embed hn (Y p)) (embed hn (Z p)) base false) ∧
    ∀ p : Fin 6, ∃ base,
      FaceLabel f (coreSet hn) (embed hn (Y p)) (embed hn (Z p)) base true

theorem not_computable_three {n : ℕ} (hn : 11 ≤ n) (f : (Fin n → Bool) → Bool)
    (hf : Pattern hn f) : ¬ computableWithHeadsN n 3 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 3 f).mp hc
  apply ThreeHeadTripartiteCross.obstruction c (fun h ↦ (r h).A) (fun h ↦ (r h).C)
    (fun h ↦ (hr h).2.1) (fun i ↦ embed hn (X i))
    (fun p ↦ embed hn (Y p)) (fun p ↦ embed hn (Z p))
  · intro i p hip
    obtain ⟨base, hb⟩ := hf.1 i p hip
    have hj : embed hn (Y p) ∉ ({embed hn (X i)} : Finset (Fin n)) := by
      simpa only [Finset.mem_singleton] using
        (fun h ↦ X_ne_Y i p ((embed_injective hn h).symm))
    have hk : embed hn (Z p) ∉ ({embed hn (X i)} : Finset (Fin n)) := by
      simpa only [Finset.mem_singleton] using
        (fun h ↦ X_ne_Z i p ((embed_injective hn h).symm))
    have hn' := coefficient_negative r c hr f hsign
      {embed hn (X i)} (embed hn (Y p)) (embed hn (Z p)) hj hk
      (fun h ↦ Y_ne_Z p (embed_injective hn h)) base hb
    simpa only [Finset.sum_singleton] using hn'.le
  · intro p
    obtain ⟨base, hb⟩ := hf.2 p
    have hp := coefficient_positive r c hr f hsign (coreSet hn)
      (embed hn (Y p)) (embed hn (Z p)) (Y_not_coreSet hn p) (Z_not_coreSet hn p)
      (fun h ↦ Y_ne_Z p (embed_injective hn h)) base hb
    simp only [sum_coreSet] at hp
    rw [coefficient_sum_X] at hp
    exact hp

theorem HStar_ge_four {n : ℕ} (hn : 11 ≤ n) (f : (Fin n → Bool) → Bool)
    (hf : Pattern hn f) : 4 ≤ HStar n f := by
  by_contra h
  have hle : HStar n f ≤ 3 := by omega
  apply not_computable_three hn f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 3 f).mpr
  exact FourHeadLocalPattern.affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

end

end HeadComplexity.ThreeHeadEmbeddedPattern
