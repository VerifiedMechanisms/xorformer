import HeadComplexity.Atoms.UniformApproximation
import HeadComplexity.Atoms.FracAtomSymmetry

set_option linter.style.header false

/-!
# Norm-preserving gates on coherent faces

A positive affine denominator may be localized to a negative coordinate face
by increasing its slopes on the face's forbidden coordinates. An arbitrarily
small increase on every coordinate keeps every new head strictly admissible,
even when the original affine denominator has zero slopes.
-/

namespace HeadComplexity.CoherentFaceGating

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- Restricting an affine ratio with nonnegative denominator slopes to a
negative face is uniformly approximable by one genuine head. At every input,
the approximating head's absolute value is bounded by that of the ungated
ratio, so the full-cube norm never increases. -/
theorem exists_atom_negativeFace_ratio
    (S : Finset (Fin n)) (a c : ℝ) (u w : Fin n → ℝ)
    (hc : 0 < c) (hw : ∀ i, 0 ≤ w i) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : FracAtom n,
      (∀ x, |φ.eval x - squarefreeMonomial S (flipBits x) *
        (affineValue a u x / affineValue c w x)| < ε) ∧
      (∀ x, |φ.eval x| ≤ |affineValue a u x / affineValue c w x|) := by
  classical
  let C : ℝ := 1 + ∑ x : Fin n → Bool, |affineValue a u x|
  have hC : 0 < C := by
    dsimp [C]
    have := Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) ↦
      abs_nonneg (affineValue a u x)
    linarith
  have hA : ∀ x, |affineValue a u x| < C := by
    intro x
    have := Finset.single_le_sum
      (fun y (_ : y ∈ Finset.univ) ↦ abs_nonneg (affineValue a u y))
      (Finset.mem_univ x)
    dsimp [C]
    linarith
  let δ : ℝ := ε * c ^ 2 / (C * ((n : ℝ) + 1))
  let R : ℝ := 1 + C / ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  let v : Fin n → ℝ := fun i ↦ w i + δ + if i ∈ S then R else 0
  have hv : ∀ i, 0 < v i := by
    intro i
    dsimp [v]
    split_ifs <;> linarith [hw i]
  let φ : FracAtom n := FracAtom.ofPositiveAffineRatio a u c v hc hv
  have hφ : ∀ x, φ.eval x = affineValue a u x / affineValue c v x :=
    fun x ↦ FracAtom.ofPositiveAffineRatio_eval a u c v hc hv x
  have hB : ∀ x, c ≤ affineValue c w x := by
    intro x
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
      mul_nonneg (hw i) (boolToReal_nonneg (x i))
    simpa [affineValue] using this
  have hDB : ∀ x, affineValue c w x ≤ affineValue c v x := by
    intro x
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (boolToReal_nonneg (x i))
    dsimp [v]
    split_ifs <;> linarith
  have hD : ∀ x, 0 < affineValue c v x := fun x ↦ hc.trans_le ((hB x).trans (hDB x))
  refine ⟨φ, ?_, ?_⟩
  · intro x
    rw [hφ]
    by_cases hface : ∀ i ∈ S, x i = false
    · have hmono : squarefreeMonomial S (flipBits x) = 1 := by
        unfold squarefreeMonomial
        apply Finset.prod_eq_one
        intro i hi
        simp [flipBits, boolToReal, hface i hi]
      rw [hmono, one_mul]
      let T : ℝ := δ * ∑ i : Fin n, boolToReal (x i)
      have hT : 0 ≤ T := by
        dsimp [T]
        exact mul_nonneg hδ.le (Finset.sum_nonneg fun i _ ↦ boolToReal_nonneg (x i))
      have hTle : T ≤ δ * (n : ℝ) := by
        dsimp [T]
        apply mul_le_mul_of_nonneg_left _ hδ.le
        calc
          ∑ i : Fin n, boolToReal (x i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ boolToReal_le_one (x i)
          _ = (n : ℝ) := by simp
      have hden : affineValue c v x = affineValue c w x + T := by
        unfold affineValue
        dsimp [v, T]
        rw [Finset.mul_sum]
        rw [add_assoc, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi, hface i hi, boolToReal]
        · simp [hi]; ring
      have hBpos : 0 < affineValue c w x := hc.trans_le (hB x)
      have hprod : c ^ 2 ≤ affineValue c v x * affineValue c w x := by
        nlinarith [hB x, hDB x]
      have herr : |affineValue a u x / affineValue c v x -
          affineValue a u x / affineValue c w x| =
          |affineValue a u x| * T /
            (affineValue c v x * affineValue c w x) := by
        rw [show affineValue a u x / affineValue c v x -
            affineValue a u x / affineValue c w x =
            -(affineValue a u x * T /
              (affineValue c v x * affineValue c w x)) by
          rw [hden]
          field_simp [hBpos.ne', (hD x).ne']
          ring]
        rw [abs_neg, abs_div, abs_mul, abs_of_nonneg hT,
          abs_of_pos (mul_pos (hD x) hBpos)]
      rw [herr]
      have hnum : |affineValue a u x| * T < ε * c ^ 2 := by
        have hfirst : |affineValue a u x| * T ≤ C * (δ * (n : ℝ)) :=
          (mul_le_mul_of_nonneg_right (hA x).le hT).trans
            (mul_le_mul_of_nonneg_left hTle hC.le)
        have hsecond : C * (δ * (n : ℝ)) < C * (δ * ((n : ℝ) + 1)) := by
          nlinarith
        have hid : C * (δ * ((n : ℝ) + 1)) = ε * c ^ 2 := by
          dsimp [δ]
          field_simp [hC.ne']
        exact hfirst.trans_lt (hsecond.trans_eq hid)
      have hnum0 : 0 ≤ |affineValue a u x| * T := mul_nonneg (abs_nonneg _) hT
      calc
        |affineValue a u x| * T /
            (affineValue c v x * affineValue c w x) ≤
            |affineValue a u x| * T / c ^ 2 :=
          div_le_div_of_nonneg_left hnum0 (sq_pos_of_pos hc) hprod
        _ < ε := (div_lt_iff₀ (sq_pos_of_pos hc)).2 hnum
    · push Not at hface
      obtain ⟨i, hi, hxi⟩ := hface
      have hxtrue : x i = true := by cases h : x i <;> simp_all
      have hmono : squarefreeMonomial S (flipBits x) = 0 := by
        unfold squarefreeMonomial
        apply Finset.prod_eq_zero hi
        simp [flipBits, boolToReal, hxtrue]
      rw [hmono, zero_mul, sub_zero, abs_div, abs_of_pos (hD x)]
      have hRden : R ≤ affineValue c v x := by
        have hterm : R ≤ v i * boolToReal (x i) := by
          simp [v, hi, hxtrue, boolToReal]
          linarith [hw i]
        have hsum := Finset.single_le_sum
          (fun j (_ : j ∈ Finset.univ) ↦ mul_nonneg (hv j).le (boolToReal_nonneg (x j)))
          (Finset.mem_univ i)
        dsimp [affineValue]
        linarith
      have hRlarge : C < ε * R := by dsimp [R]; field_simp; nlinarith
      apply (div_lt_iff₀ (hD x)).2
      exact (hA x).trans (hRlarge.trans_le (mul_le_mul_of_nonneg_left hRden hε.le))
  · intro x
    rw [hφ, abs_div, abs_div, abs_of_pos (hD x),
      abs_of_pos (hc.trans_le (hB x))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (hc.trans_le (hB x)) (hDB x)

/-- Uniform one-atom interface for the norm-preserving coherent-face gate. -/
theorem uniformlyOneAtomApproximable_negativeFace_ratio
    (S : Finset (Fin n)) (a c : ℝ) (u w : Fin n → ℝ)
    (hc : 0 < c) (hw : ∀ i, 0 ≤ w i) :
    UniformlyOneAtomApproximable
      (fun x ↦ squarefreeMonomial S (flipBits x) *
        (affineValue a u x / affineValue c w x)) := by
  intro ε hε
  obtain ⟨φ, happrox, -⟩ := exists_atom_negativeFace_ratio S a c u w hc hw ε hε
  exact ⟨φ, happrox⟩

end HeadComplexity.CoherentFaceGating
