import HeadComplexity.Polynomial.ThreeHeadTripartiteCross

set_option linter.style.header false

/-!
# Boolean block faces and strict alternating signs

A block of coordinates may move together as one Boolean variable. The two
other face variables occupy distinct coordinates outside that block.
-/

namespace HeadComplexity.ThreeHeadBooleanFace

noncomputable section

open Finset
open scoped BigOperators

def blockFace {n : ℕ} (I : Finset (Fin n)) (j k : Fin n)
    (base : Fin n → Bool) (a b c : Bool) : Fin n → Bool :=
  fun i ↦ if i ∈ I then a else if i = j then b else if i = k then c else base i

def faceConstant {n : ℕ} (q : ℝ) (v : Fin n → ℝ) (I : Finset (Fin n))
    (j k : Fin n) (base : Fin n → Bool) : ℝ :=
  q + ∑ i, if i ∈ I ∨ i = j ∨ i = k then 0 else v i * boolToReal (base i)

theorem affine_blockFace {n : ℕ} (q : ℝ) (v : Fin n → ℝ) (I : Finset (Fin n))
    (j k : Fin n) (hj : j ∉ I) (hk : k ∉ I) (hjk : j ≠ k)
    (base : Fin n → Bool) (a b c : Bool) :
    q + ∑ i, v i * boolToReal (blockFace I j k base a b c i) =
      faceConstant q v I j k base + (∑ i ∈ I, v i) * boolToReal a +
        v j * boolToReal b + v k * boolToReal c := by
  have he (i) : v i * boolToReal (blockFace I j k base a b c i) =
      (if i ∈ I ∨ i = j ∨ i = k then 0 else v i * boolToReal (base i)) +
      (if i ∈ I then v i * boolToReal a else 0) +
      (if i = j then v j * boolToReal b else 0) +
      (if i = k then v k * boolToReal c else 0) := by
    by_cases hi : i ∈ I
    · have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
      have hik : i ≠ k := by intro h; exact hk (h ▸ hi)
      simp [blockFace, hi, hij, hik]
    · by_cases hij : i = j
      · subst i
        simp [blockFace, hj, hjk]
      · by_cases hik : i = k
        · subst i
          simp [blockFace, hk, hjk.symm]
        · simp [blockFace, hi, hij, hik]
  simp_rw [he]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul]
  simp only [faceConstant]
  ring

def parity (a b c : Bool) : Bool := (a ^^ b) ^^ c

def FaceLabel {n : ℕ} (f : (Fin n → Bool) → Bool) (I : Finset (Fin n))
    (j k : Fin n) (base : Fin n → Bool) (positive : Bool) : Prop :=
  ∀ a b c, f (blockFace I j k base a b c) =
    if positive then parity a b c else !(parity a b c)

def alternating (P : Bool → Bool → Bool → ℝ) : ℝ :=
  P true true true - P true true false - P true false true - P false true true +
    P true false false + P false true false + P false false true - P false false false

theorem alternating_pos (P : Bool → Bool → Bool → ℝ)
    (hf : ∀ a b c, 0 < P a b c ↔ parity a b c = true) : 0 < alternating P := by
  have h111 := (hf true true true).mpr (by decide)
  have h100 := (hf true false false).mpr (by decide)
  have h010 := (hf false true false).mpr (by decide)
  have h001 := (hf false false true).mpr (by decide)
  have h110 : P true true false ≤ 0 := by simpa [parity] using hf true true false
  have h101 : P true false true ≤ 0 := by simpa [parity] using hf true false true
  have h011 : P false true true ≤ 0 := by simpa [parity] using hf false true true
  have h000 : P false false false ≤ 0 := by simpa [parity] using hf false false false
  unfold alternating
  linarith

theorem alternating_neg (P : Bool → Bool → Bool → ℝ)
    (hf : ∀ a b c, 0 < P a b c ↔ (!(parity a b c)) = true) : alternating P < 0 := by
  have h110 := (hf true true false).mpr (by decide)
  have h101 := (hf true false true).mpr (by decide)
  have h011 := (hf false true true).mpr (by decide)
  have h000 := (hf false false false).mpr (by decide)
  have h111 : P true true true ≤ 0 := by simpa [parity] using hf true true true
  have h100 : P true false false ≤ 0 := by simpa [parity] using hf true false false
  have h010 : P false true false ≤ 0 := by simpa [parity] using hf false true false
  have h001 : P false false true ≤ 0 := by simpa [parity] using hf false false true
  unfold alternating
  linarith

end

end HeadComplexity.ThreeHeadBooleanFace
