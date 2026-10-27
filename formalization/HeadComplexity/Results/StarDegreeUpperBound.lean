import HeadComplexity.Results.MonomialStarCover
import Mathlib.Data.Nat.Choose.Sum

set_option linter.style.header false

/-!
# Degree-sensitive monomial star bounds

Use centers of cardinalities `d - 1, d - 3, ...`. A nonconstant monomial
of degree at most `d` either is a center or becomes one after deleting a
coordinate. Each center is compiled as one whole affine block.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- The parity of `d - 1` selects the center ranks below `d`. -/
def starCenterRanks (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun r ↦ r % 2 = (d - 1) % 2

/-- Explicit degree-sensitive head budget. -/
def starDegreeBound (n d : ℕ) : ℕ :=
  ∑ r ∈ starCenterRanks d, n.choose r

/-- All centers in the chosen ranks. -/
def degreeStarCenters (n d : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ S.card ∈ starCenterRanks d

theorem card_degreeStarCenters (n d : ℕ) :
    (degreeStarCenters n d).card = starDegreeBound n d := by
  classical
  unfold degreeStarCenters starDegreeBound
  rw [← Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Finset (Fin n))) (starCenterRanks d) Finset.card]
  apply Finset.sum_congr rfl
  intro r _
  rw [show (Finset.univ : Finset (Finset (Fin n))).filter (fun S ↦ S.card = r) =
      (Finset.univ : Finset (Fin n)).powersetCard r by ext S; simp]
  simp

/-- The alternating rank family covers every active monomial in a
polynomial of degree at most `d`. -/
theorem SquarefreePolynomial.hasStarCover_degreeStarCenters
    {n d : ℕ} (P : SquarefreePolynomial n) (hdeg : P.DegreeLE d) :
    P.HasStarCover (degreeStarCenters n d) := by
  classical
  intro T hT
  have hT' := (Finset.mem_filter.mp hT).2
  have hne : T.Nonempty := hT'.1
  have hcard : T.card ≤ d := hdeg T hT'.2
  by_cases hparity : T.card % 2 = (d - 1) % 2
  · refine ⟨T, ?_, Or.inl rfl⟩
    simp only [degreeStarCenters, Finset.mem_filter, Finset.mem_univ, true_and,
      starCenterRanks, Finset.mem_range]
    exact ⟨by have := hne.card_pos; omega, hparity⟩
  · obtain ⟨i, hi⟩ := hne
    refine ⟨T.erase i, ?_, Or.inr ⟨i, Finset.notMem_erase i T,
      Finset.insert_erase hi⟩⟩
    simp only [degreeStarCenters, Finset.mem_filter, Finset.mem_univ, true_and,
      starCenterRanks, Finset.mem_range]
    have herase := Finset.card_erase_of_mem hi
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    constructor <;> omega

/-- A polynomial threshold certificate of degree at most `d` compiles with
one head per selected star center. -/
theorem computableWithHeadsN_starDegreeBound_of_ThresholdDegLE
    {n d : ℕ} {f : (Fin n → Bool) → Bool} (h : ThresholdDegLE f d) :
    computableWithHeadsN n (starDegreeBound n d) f := by
  obtain ⟨P, hdeg, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE h
  have hcomp := P.computableWithHeadsN_of_starCover f hP
    (degreeStarCenters n d) (P.hasStarCover_degreeStarCenters hdeg)
  rwa [card_degreeStarCenters] at hcomp

/-- Degree-sensitive head upper bound. For example, quadratic threshold
functions require at most `n` heads, rather than a quadratic support budget. -/
theorem HStar_le_starDegreeBound_of_ThresholdDegLE
    {n d : ℕ} {f : (Fin n → Bool) → Bool} (h : ThresholdDegLE f d) :
    HStar n f ≤ starDegreeBound n d :=
  HStar_le_of_computableWithHeadsN
    (computableWithHeadsN_starDegreeBound_of_ThresholdDegLE h)

/-- Minimum threshold-degree presentation of the new compiler. -/
theorem HStar_le_starDegreeBound_thresholdDeg
    {n : ℕ} (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ starDegreeBound n (thresholdDeg f) :=
  HStar_le_starDegreeBound_of_ThresholdDegLE (thresholdDeg_spec f)

/-- The original degree lower bound strengthens to a two-sided quantitative
relationship, with no additional hypothesis on the Boolean function. -/
theorem thresholdDeg_le_HStar_le_starDegreeBound
    {n : ℕ} (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ HStar n f ∧
      HStar n f ≤ starDegreeBound n (thresholdDeg f) :=
  ⟨thresholdDeg_le_HStar f, HStar_le_starDegreeBound_thresholdDeg f⟩

/-- The minimum-degree presentation used in the comparison is equivalent to
the original model-level theorem, rather than merely a specialization.
The reverse direction uses the attained threshold-degree certificate and
minimality of the actual attention head count. -/
theorem thresholdDeg_bound_iff_model_degree_bound
    {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (thresholdDeg f ≤ HStar n f) ↔
      (∀ H, computableWithHeadsN n H f → ThresholdDegLE f H) := by
  constructor
  · intro hminimum H hcomputable
    obtain ⟨P, hdegree, hsign⟩ := thresholdDeg_spec f
    exact ⟨P, hdegree.trans (hminimum.trans
      (HStar_le_of_computableWithHeadsN hcomputable)), hsign⟩
  · intro hmodel
    exact thresholdDeg_le_of_ThresholdDegLE
      (hmodel (HStar n f) (HStar_computable f))

@[simp] theorem starDegreeBound_zero (n : ℕ) : starDegreeBound n 0 = 0 := by
  simp [starDegreeBound, starCenterRanks]

@[simp] theorem starDegreeBound_one (n : ℕ) : starDegreeBound n 1 = 1 := by
  have h : starCenterRanks 1 = {0} := by decide
  simp [starDegreeBound, h]

@[simp] theorem starDegreeBound_two (n : ℕ) : starDegreeBound n 2 = n := by
  have h : starCenterRanks 2 = {1} := by decide
  simp [starDegreeBound, h]

@[simp] theorem starDegreeBound_three (n : ℕ) :
    starDegreeBound n 3 = 1 + n.choose 2 := by
  have h : starCenterRanks 3 = {0, 2} := by decide
  simp [starDegreeBound, h]

/-- Adding two to the degree adds just the next selected binomial layer. -/
theorem starDegreeBound_add_two (n d : ℕ) :
    starDegreeBound n (d + 2) = starDegreeBound n d + n.choose (d + 1) := by
  have hranks : starCenterRanks (d + 2) = insert (d + 1) (starCenterRanks d) := by
    ext r
    simp only [starCenterRanks, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    omega
  have hnot : d + 1 ∉ starCenterRanks d := by simp [starCenterRanks]
  rw [starDegreeBound, hranks, Finset.sum_insert hnot]
  exact Nat.add_comm _ _

/-- The alternating-rank budget is the full degree-at-most-`d-1` dimension
on one fewer variable. This makes the degree saving explicit. -/
theorem starDegreeBound_eq_sum_pred_choose {n : ℕ} (hn : 0 < n) (d : ℕ) :
    starDegreeBound n d = ∑ r ∈ Finset.range d, (n - 1).choose r := by
  induction d using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more d ih _ =>
      rw [starDegreeBound_add_two, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hpascal := Nat.choose_succ_succ' (n - 1) d
      rw [show n - 1 + 1 = n by omega] at hpascal
      omega

/-- Every quadratic threshold function has a linear head budget. -/
theorem HStar_le_ambient_of_quadratic
    {n : ℕ} {f : (Fin n → Bool) → Bool} (h : ThresholdDegLE f 2) :
    HStar n f ≤ n := by
  simpa using HStar_le_starDegreeBound_of_ThresholdDegLE h

/-- Every cubic threshold function has a quadratic head budget. -/
theorem HStar_le_one_add_choose_two_of_cubic
    {n : ℕ} {f : (Fin n → Bool) → Bool} (h : ThresholdDegLE f 3) :
    HStar n f ≤ 1 + n.choose 2 := by
  simpa using HStar_le_starDegreeBound_of_ThresholdDegLE h

/-- This joint statement preserves the former support-count bound in every
boundary case, while adding the new star-cover bound. -/
theorem HStar_le_min_starDegree_affineFree_of_ThresholdDegLE
    {n d : ℕ} {f : (Fin n → Bool) → Bool} (h : ThresholdDegLE f d) :
    HStar n f ≤ min (starDegreeBound n d)
      (1 + ∑ r ∈ Finset.Icc 2 d, n.choose r) :=
  Nat.le_min.mpr ⟨HStar_le_starDegreeBound_of_ThresholdDegLE h,
    HStar_le_one_add_sum_choose_of_ThresholdDegLE h⟩

end HeadComplexity
