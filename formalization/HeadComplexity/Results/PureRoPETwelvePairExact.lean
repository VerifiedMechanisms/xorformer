import HeadComplexity.Results.PureRoPEThreeHeadObstruction

set_option linter.style.header false

/-!
# Exact pure and vanilla counts for the twelve-bit matching predicate

The four-head integer certificate is reproduced from
VerifiedMechanisms/xorformer-runs commit
1899d884da3affbf21a8528bcb74b409c9783876,
`Results/TwelvePairExact.lean`. The entire certificate is checked again here
against this checkout's unchanged scalar and architectural definitions.
-/

namespace HeadComplexity.PureRoPEThreeHead.TwelvePair

open Finset
open scoped BigOperators

def denominatorConstant : Fin 4 → ℤ := ![1672, 1673, 1695, 1671]
def denominatorSlope : Fin 4 → Fin 12 → ℤ :=
  ![![-175, -262, -1, -308, -259, -170, -84, -84, -1, -1, -1, -1],
    ![-160, -263, -143, -268, -314, -1, -1, -1, -98, -98, -1, -1],
    ![-185, -278, -185, -281, -275, -180, -3, -3, -1, -1, -1, -1],
    ![-1, -317, -144, -269, -260, -155, -1, -1, -1, -1, -98, -99]]
def numeratorConstant : Fin 4 → ℤ := ![10011746, 9875811, -10011746, -10011746]
def numeratorSlope : Fin 4 → Fin 12 → ℤ :=
  ![![-3952418, -2281831, 10011746, -6142197, -2238238, -3845394, 4457351, 4457351,
      -162221, -162221, -60888, -56346],
    ![-2200994, -2333372, -605695, -2828740, -6044101, 7412611, -775541, -775541,
      3613278, 3613278, -265089, -252305],
    ![-1183718, 7443275, -8606348, 8516499, 7462344, -1907178, -3684362, -3684362,
      -3855343, -3855343, -3920598, -3940820],
    ![7197212, -2198416, 1307416, 486431, 805571, 64920, -745458, -745458,
      -448354, -448354, 4548846, 4555067]]

def integerEval (c : ℤ) (a : Fin 12 → ℤ) (x : Fin 12 → Bool) : ℤ :=
  c + ∑ i, if x i then a i else 0
def integerDen (h : Fin 4) : (Fin 12 → Bool) → ℤ :=
  integerEval (denominatorConstant h) (denominatorSlope h)
def integerNum (h : Fin 4) : (Fin 12 → Bool) → ℤ :=
  integerEval (numeratorConstant h) (numeratorSlope h)
def integerCleared (x : Fin 12 → Bool) : ℤ :=
  integerNum 0 x * integerDen 1 x * integerDen 2 x * integerDen 3 x +
    integerNum 1 x * integerDen 0 x * integerDen 2 x * integerDen 3 x +
    integerNum 2 x * integerDen 0 x * integerDen 1 x * integerDen 3 x +
    integerNum 3 x * integerDen 0 x * integerDen 1 x * integerDen 2 x

theorem slopes_negative : ∀ h i, denominatorSlope h i < 0 := by decide +kernel
theorem denominator_minimum_positive : ∀ h, 0 < denominatorConstant h +
    ∑ i, denominatorSlope h i := by decide +kernel

theorem integerDen_positive (h : Fin 4) (x : Fin 12 → Bool) : 0 < integerDen h x := by
  apply (denominator_minimum_positive h).trans_le
  unfold integerDen integerEval
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro i _
  cases x i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact (slopes_negative h i).le
  · exact le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
-- Split the full integer cube check into sixteen slices for kernel reduction.
theorem integer_certificate : ∀ bits : Fin 12 → Bool,
    (0 < integerCleared bits ↔ function bits = true) ∧ integerCleared bits ≠ 0 := by
  have h : ∀ b0 b1 b2 b3 : Bool, ∀ tail : Fin 8 → Bool,
      (0 < integerCleared (Fin.append (m := 4) (n := 8) ![b0, b1, b2, b3] tail) ↔
        function (Fin.append (m := 4) (n := 8) ![b0, b1, b2, b3] tail) = true) ∧
      integerCleared (Fin.append (m := 4) (n := 8) ![b0, b1, b2, b3] tail) ≠ 0 := by
    intro b0 b1 b2 b3
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide +kernel
  intro bits
  have hv : ![bits 0, bits 1, bits 2, bits 3] =
      (fun i : Fin 4 ↦ bits (i.castAdd 8)) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hv, Fin.append_castAdd_natAdd] using
    h (bits 0) (bits 1) (bits 2) (bits 3) (fun i ↦ bits (Fin.natAdd 4 i))

noncomputable def fraction (h : Fin 4) : AffineFraction 12 where
  A i := numeratorSlope h i
  b := numeratorConstant h
  C i := denominatorSlope h i
  d := denominatorConstant h

theorem fraction_denominator (h : Fin 4) (x : Fin 12 → Bool) :
    (fraction h).denominator x = (integerDen h x : ℝ) := by
  unfold AffineFraction.denominator fraction integerDen integerEval
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

theorem fraction_numerator (h : Fin 4) (x : Fin 12 → Bool) :
    (fraction h).numerator x = (integerNum h x : ℝ) := by
  unfold AffineFraction.numerator fraction integerNum integerEval
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

theorem fraction_admissible (h : Fin 4) : (fraction h).Admissible := by
  have hneg (i : Fin 12) : (fraction h).C i < 0 := by
    change (denominatorSlope h i : ℝ) < 0
    exact_mod_cast slopes_negative h i
  refine ⟨?_, Or.inr (Or.inl hneg), ?_⟩
  · intro x
    rw [fraction_denominator]
    exact_mod_cast integerDen_positive h x
  · intro hz
    exact False.elim ((hneg 0).ne (hz 0))

theorem fraction_sign (x : Fin 12 → Bool) :
    0 < ∑ h, (fraction h).eval x ↔ function x = true := by
  have hp (h : Fin 4) : (0 : ℝ) < integerDen h x := by exact_mod_cast integerDen_positive h x
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have h2 := (hp 2).ne'
  have h3 := (hp 3).ne'
  have he : ((integerDen 0 x : ℝ) * integerDen 1 x * integerDen 2 x * integerDen 3 x) *
      (∑ h, (fraction h).eval x) = integerCleared x := by
    simp only [AffineFraction.eval, fraction_numerator, fraction_denominator,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, integerCleared]
    push_cast
    field_simp
    ring
  have hd := mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2)) (hp 3)
  have hs : (0 : ℝ) < integerCleared x ↔ function x = true := by
    exact_mod_cast (integer_certificate x).1
  rw [← he, mul_pos_iff_of_pos_left hd] at hs
  exact hs

theorem vanilla_computable_four : computableWithHeadsN 12 4 function := by
  apply (computableWithHeadsN_iff_affineFractionComputable 4 function).mpr
  exact ⟨fraction, 0, fraction_admissible, fun x ↦ by simpa using fraction_sign x⟩

theorem vanillaHStar_eq_four : HStar 12 function = 4 := by
  classical
  apply Nat.le_antisymm _ vanillaHStar_ge_four
  have hex := exists_computable function
  unfold HStar
  rw [dif_pos hex]
  exact Nat.find_min' hex vanilla_computable_four

theorem pureRoPEHStar_eq_four : PureRoPEHStar 12 function = 4 :=
  Nat.le_antisymm (by rw [← vanillaHStar_eq_four]; exact pureRoPEHStar_le_vanilla function)
    pureRoPEHStar_ge_four

theorem sharedHStar_eq_four : SharedHStar 12 function = 4 := by
  simpa only [SharedHStar_eq_HStar] using vanillaHStar_eq_four

open MvPolynomial

private noncomputable def spinPolynomial (i : Fin 12) : MvPolynomial (Fin 12) ℝ :=
  C 1 - C 2 * X i

private noncomputable def quadraticPolynomial : MvPolynomial (Fin 12) ℝ :=
  C 22 + C 20 * (∑ i : Fin 6, spinPolynomial (left i) * spinPolynomial (right i)) -
    (∑ i : Fin 12, spinPolynomial i) * (∑ i : Fin 12, spinPolynomial i)

private theorem eval_spinPolynomial (x : Fin 12 → Bool) (i : Fin 12) :
    eval (cubePoint x) (spinPolynomial i) = -(integerSpin (x i) : ℝ) := by
  cases h : x i <;> norm_num [spinPolynomial, integerSpin, cubePoint, boolToReal, h]

private theorem eval_quadraticPolynomial (x : Fin 12 → Bool) :
    eval (cubePoint x) quadraticPolynomial = (scoreInt x : ℝ) := by
  simp only [quadraticPolynomial, map_sub, map_add, map_mul, map_sum, eval_C,
    eval_spinPolynomial, neg_mul_neg, Finset.sum_neg_distrib, scoreInt]
  push_cast
  ring

private theorem quadraticPolynomial_degree : quadraticPolynomial.totalDegree ≤ 2 := by
  have hs (i : Fin 12) : (spinPolynomial i).totalDegree ≤ 1 := totalDegree_parityFactor i
  have hsum : (∑ i : Fin 12, spinPolynomial i).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le (fun i _ ↦ hs i)
  have hp : (∑ i : Fin 6, spinPolynomial (left i) *
      spinPolynomial (right i)).totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (Nat.add_le_add (hs _) (hs _))
  unfold quadraticPolynomial
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simpa using hp)
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add hsum hsum)

theorem thresholdDegLE_two : ThresholdDegLE function 2 := by
  refine ⟨quadraticPolynomial, quadraticPolynomial_degree, ?_⟩
  intro x
  rw [eval_quadraticPolynomial]
  simp only [function, decide_eq_true_eq]
  exact_mod_cast (Iff.rfl : 0 < scoreInt x ↔ 0 < scoreInt x)

theorem thresholdDeg_eq_two : thresholdDeg function = 2 := by
  classical
  have hex : ∃ d, ThresholdDegLE function d := ⟨2, thresholdDegLE_two⟩
  rw [thresholdDeg, dif_pos hex]
  apply Nat.le_antisymm (Nat.find_min' hex thresholdDegLE_two)
  by_contra h
  have hfind : Nat.find hex ≤ 1 := by omega
  obtain ⟨P, hPdeg, hPsign⟩ := Nat.find_spec hex
  have hltf := (ThresholdDegLE_one_iff_isLTF function).mp
    ⟨P, hPdeg.trans hfind, hPsign⟩
  have hone := (pureRoPEComputable_one_iff_isLTF function).mpr hltf
  exact not_pureRoPEComputable_three (computable_mono (by omega : 1 ≤ 3) hone)

theorem exact_complexities : thresholdDeg function = 2 ∧
    PureRoPEHStar 12 function = 4 ∧ HStar 12 function = 4 :=
  ⟨thresholdDeg_eq_two, pureRoPEHStar_eq_four, vanillaHStar_eq_four⟩

end HeadComplexity.PureRoPEThreeHead.TwelvePair
