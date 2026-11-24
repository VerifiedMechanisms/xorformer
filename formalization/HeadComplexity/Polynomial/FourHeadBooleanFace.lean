import HeadComplexity.Polynomial.ThreeHeadBooleanFace

set_option linter.style.header false

/-! # Four-dimensional Boolean block faces -/

namespace HeadComplexity.FourHeadBooleanFace

noncomputable section

open Finset
open scoped BigOperators

def blockFace {n : ℕ} (I : Finset (Fin n)) (j k l : Fin n)
    (base : Fin n → Bool) (a b c d : Bool) : Fin n → Bool :=
  fun i ↦ if i ∈ I then a else if i = j then b else if i = k then c
    else if i = l then d else base i

def faceConstant {n : ℕ} (q : ℝ) (v : Fin n → ℝ) (I : Finset (Fin n))
    (j k l : Fin n) (base : Fin n → Bool) : ℝ :=
  q + ∑ i, if i ∈ I ∨ i = j ∨ i = k ∨ i = l then 0 else v i * boolToReal (base i)

theorem affine_blockFace {n : ℕ} (q : ℝ) (v : Fin n → ℝ) (I : Finset (Fin n))
    (j k l : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hl : l ∉ I)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (base : Fin n → Bool) (a b c d : Bool) :
    q + ∑ i, v i * boolToReal (blockFace I j k l base a b c d i) =
      faceConstant q v I j k l base + (∑ i ∈ I, v i) * boolToReal a +
        v j * boolToReal b + v k * boolToReal c + v l * boolToReal d := by
  have he (i) : v i * boolToReal (blockFace I j k l base a b c d i) =
      (if i ∈ I ∨ i = j ∨ i = k ∨ i = l then 0 else v i * boolToReal (base i)) +
      (if i ∈ I then v i * boolToReal a else 0) +
      (if i = j then v j * boolToReal b else 0) +
      (if i = k then v k * boolToReal c else 0) +
      (if i = l then v l * boolToReal d else 0) := by
    by_cases hi : i ∈ I
    · have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
      have hik : i ≠ k := by intro h; exact hk (h ▸ hi)
      have hil : i ≠ l := by intro h; exact hl (h ▸ hi)
      simp [blockFace, hi, hij, hik, hil]
    · by_cases hij : i = j
      · subst i
        simp [blockFace, hj, hjk, hjl]
      · by_cases hik : i = k
        · subst i
          simp [blockFace, hk, hjk.symm, hkl]
        · by_cases hil : i = l
          · subst i
            simp [blockFace, hl, hjl.symm, hkl.symm]
          · simp [blockFace, hi, hij, hik, hil]
  simp_rw [he]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul, faceConstant]
  ring

def parity (a b c d : Bool) : Bool := !(((a ^^ b) ^^ c) ^^ d)

def FaceLabel {n : ℕ} (f : (Fin n → Bool) → Bool) (I : Finset (Fin n))
    (j k l : Fin n) (base : Fin n → Bool) (positive : Bool) : Prop :=
  ∀ a b c d, f (blockFace I j k l base a b c d) =
    if positive then parity a b c d else !(parity a b c d)

def alternating (P : Bool → Bool → Bool → Bool → ℝ) : ℝ :=
  ThreeHeadBooleanFace.alternating (fun a b c ↦ P a b c true) -
    ThreeHeadBooleanFace.alternating (fun a b c ↦ P a b c false)

theorem alternating_pos (P : Bool → Bool → Bool → Bool → ℝ)
    (hf : ∀ a b c d, 0 < P a b c d ↔ parity a b c d = true) :
    0 < alternating P := by
  have hp := ThreeHeadBooleanFace.alternating_pos (fun a b c ↦ P a b c true)
    (fun a b c ↦ by simpa [parity, ThreeHeadBooleanFace.parity] using hf a b c true)
  have hn := ThreeHeadBooleanFace.alternating_neg (fun a b c ↦ P a b c false)
    (fun a b c ↦ by simpa [parity, ThreeHeadBooleanFace.parity] using hf a b c false)
  unfold alternating
  linarith

theorem alternating_neg (P : Bool → Bool → Bool → Bool → ℝ)
    (hf : ∀ a b c d, 0 < P a b c d ↔ (!(parity a b c d)) = true) :
    alternating P < 0 := by
  have hn := ThreeHeadBooleanFace.alternating_neg (fun a b c ↦ P a b c true)
    (fun a b c ↦ by simpa [parity, ThreeHeadBooleanFace.parity] using hf a b c true)
  have hp := ThreeHeadBooleanFace.alternating_pos (fun a b c ↦ P a b c false)
    (fun a b c ↦ by simpa [parity, ThreeHeadBooleanFace.parity] using hf a b c false)
  unfold alternating
  linarith

end

end HeadComplexity.FourHeadBooleanFace
