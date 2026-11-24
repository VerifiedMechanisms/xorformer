import HeadComplexity.Research.OneHeadFeasibleBasisNonuniqueness
import HeadComplexity.Atoms.AtomicMargin

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

/-! Exact shared-threshold-chamber form of a positive-denominator unit gap.
The finite example rules out coding the branch by coefficient-ratio order alone;
it is not a capacity lower bound or a globally small-margin truth table. -/

noncomputable section
namespace HeadComplexity.OneHeadSharedChamber
open scoped BigOperators

def plusPart (a b : ℝ) : ℝ := (a + b) / 2

def minusPart (a b : ℝ) : ℝ := (b - a) / 2

theorem parts_sum (a b : ℝ) : plusPart a b + minusPart a b = b := by
  unfold plusPart minusPart
  ring

theorem parts_sub (a b : ℝ) : plusPart a b - minusPart a b = a := by
  unfold plusPart minusPart
  ring

theorem positive_contact (a b : ℝ) (h : a = b) :
    plusPart a b = b ∧ minusPart a b = 0 := by
  subst a
  constructor <;> simp [plusPart, minusPart]

theorem negative_contact (a b : ℝ) (h : a = -b) :
    plusPart a b = 0 ∧ minusPart a b = b := by
  subst a
  constructor <;> simp [plusPart, minusPart]

/-- The numerator and denominator split into two weak separators with the same
labels, one of which may vanish at a contact. -/
theorem unit_gap_iff_shared_chamber (a b : ℝ) (hb : 0 < b) (f : Bool) :
    b ≤ (if f then a else -a) ↔
      0 ≤ (if f then plusPart a b else -plusPart a b) ∧
      0 ≤ (if f then -minusPart a b else minusPart a b) := by
  cases f <;> simp only [Bool.false_eq_true, ↓reduceIte, plusPart, minusPart]
  all_goals constructor
  all_goals intro h
  all_goals first | constructor <;> linarith | rcases h with ⟨h₁, h₂⟩; linarith

/-- Without fixing labels, the full unit gap forbids a positive product of the
two affine parts. -/
theorem unit_gap_iff_product_nonpos (a b : ℝ) (hb : 0 < b) :
    b ≤ |a| ↔ plusPart a b * minusPart a b ≤ 0 := by
  unfold plusPart minusPart
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    constructor <;> intro h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ a + b by linarith)]
    · by_contra hn
      have hba : a < b := lt_of_not_ge hn
      have hp := mul_pos (sub_pos.mpr hba) (show 0 < a + b by linarith)
      nlinarith
  · have han : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg han]
    constructor <;> intro h
    · nlinarith [mul_nonneg (show 0 ≤ -a - b by linarith)
        (show 0 ≤ -a + b by linarith)]
    · by_contra hn
      have hba : -a < b := lt_of_not_ge hn
      have hp := mul_pos (show 0 < b + a by linarith) (show 0 < b - a by linarith)
      nlinarith

/-- Full-cube version, using exactly the signed labels of the margin API. -/
theorem full_gap_iff_shared_chamber {n : ℕ}
    (A B : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → Bool)
    (hB : ∀ x, 0 < B x) :
    (∀ x, B x ≤ signedLabel f x * A x) ↔
      (∀ x, 0 ≤ signedLabel f x * plusPart (A x) (B x)) ∧
      (∀ x, 0 ≤ signedLabel f x * (-minusPart (A x) (B x))) := by
  have hp (x : Fin n → Bool) :
      (B x ≤ signedLabel f x * A x) ↔
        0 ≤ signedLabel f x * plusPart (A x) (B x) ∧
        0 ≤ signedLabel f x * (-minusPart (A x) (B x)) := by
    have hh := unit_gap_iff_shared_chamber (A x) (B x) (hB x) (f x)
    cases hf : f x <;> simpa [signedLabel, hf] using hh
  constructor
  · intro h
    exact ⟨fun x => ((hp x).mp (h x)).1, fun x => ((hp x).mp (h x)).2⟩
  · rintro ⟨hu, hv⟩ x
    exact (hp x).mpr ⟨hu x, hv x⟩

namespace RatioOrderCounterexample

def denominatorCoefficients : Fin 2 → Fin 7 → ℝ :=
  ![![20,22,26,4,3,28,24], ![1,14,29,9,5,20,9]]

def numeratorCoefficients : Fin 2 → Fin 7 → ℝ :=
  ![![216,-174,-366,-192,-193,-168,220], ![119,-104,-219,-109,-125,-98,139]]

def coefficientOrder : Fin 7 → Fin 7 := ![4,3,2,1,5,6,0]

def affine (a : Fin 7 → ℝ) (x : Fin 6 → Bool) : ℝ :=
  affineValue (a 0) (fun i => a i.succ) x

theorem denominatorCoefficients_pos (k : Fin 2) (i : Fin 7) :
    0 < denominatorCoefficients k i := by
  fin_cases k <;> fin_cases i <;> norm_num [denominatorCoefficients]

/-- The complete strict order of all seven ratios, including the intercept,
is identical for the two different feasible extensions. -/
theorem same_strict_ratio_order (k : Fin 2) (j : Fin 6) :
    numeratorCoefficients k (coefficientOrder j.castSucc) /
        denominatorCoefficients k (coefficientOrder j.castSucc) <
      numeratorCoefficients k (coefficientOrder j.succ) /
        denominatorCoefficients k (coefficientOrder j.succ) := by
  fin_cases k <;> fin_cases j <;>
    norm_num [numeratorCoefficients, denominatorCoefficients, coefficientOrder]

theorem common_basis_contacts (k : Fin 2) (j : Fin 7) :
    affine (numeratorCoefficients k) (OneHeadFeasibleBasisNonuniqueness.basisPoint j) =
      OneHeadFeasibleBasisNonuniqueness.basisValue j *
        affine (denominatorCoefficients k) (OneHeadFeasibleBasisNonuniqueness.basisPoint j) := by
  fin_cases k <;> fin_cases j <;>
    norm_num [affine, affineValue, numeratorCoefficients, denominatorCoefficients,
      OneHeadFeasibleBasisNonuniqueness.basisPoint,
      OneHeadFeasibleBasisNonuniqueness.basisValue, Fin.sum_univ_succ, boolToReal]

set_option maxHeartbeats 4000000 in
-- Enumerating two coefficient arrays on all 64 Boolean vertices needs a larger tactic budget.
theorem full_cube_unit_gap (k : Fin 2) (x : Fin 6 → Bool) :
    affine (denominatorCoefficients k) x ≤ |affine (numeratorCoefficients k) x| := by
  have hx : x = ![x 0,x 1,x 2,x 3,x 4,x 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  fin_cases k <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;>
    norm_num [affine, affineValue, numeratorCoefficients, denominatorCoefficients,
      Fin.sum_univ_succ, boolToReal]

theorem different_labels :
    0 < affine (numeratorCoefficients 0) ![false,false,false,true,false,false] ∧
    affine (numeratorCoefficients 1) ![false,false,false,true,false,false] < 0 := by
  norm_num [affine, affineValue, numeratorCoefficients, Fin.sum_univ_succ, boolToReal]

def atom (k : Fin 2) : FracAtom 6 :=
  FracAtom.ofPositiveAffineRatio (numeratorCoefficients k 0)
    (fun i => numeratorCoefficients k i.succ) (denominatorCoefficients k 0)
    (fun i => denominatorCoefficients k i.succ)
    (denominatorCoefficients_pos k 0) (fun i => denominatorCoefficients_pos k i.succ)

theorem atom_eval (k : Fin 2) (x : Fin 6 → Bool) :
    (atom k).eval x = affine (numeratorCoefficients k) x /
      affine (denominatorCoefficients k) x := by
  exact FracAtom.ofPositiveAffineRatio_eval ..

end RatioOrderCounterexample
end HeadComplexity.OneHeadSharedChamber
