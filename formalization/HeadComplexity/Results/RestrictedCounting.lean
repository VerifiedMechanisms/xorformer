import HeadComplexity.Atoms.FracComputableMonotone
import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Results.CountingLowerBound

set_option linter.style.header false

/-!
# Counting on a selected input grid

Restrict the Warren reduction to an arbitrary finite grid. A degree-`d`
extension family which shatters that grid yields exact-degree hard functions
when the low-head and lower-degree pattern budgets do not cover all labels.
Warren's inequality remains an explicit premise, as in theorem 26.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n d H : ℕ} {I : Type} [Fintype I]

/-- Lower-degree squarefree coefficient coordinates. -/
abbrev LowerDegreeParameter (n d : ℕ) := {S : Finset (Fin n) // S.card < d}

noncomputable def lowerDegreeTracePoly (input : I → (Fin n → Bool)) (i : I) :
    MvPolynomial (LowerDegreeParameter n d) ℝ :=
  ∑ S : LowerDegreeParameter n d, C (squarefreeMonomial S.val (input i)) * X S

omit [Fintype I] in
theorem lowerDegreeTracePoly_degree (input : I → (Fin n → Bool)) (i : I) :
    (lowerDegreeTracePoly (d := d) input i).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro S _
  exact (totalDegree_mul _ _).trans (by simp)

omit [Fintype I] in
theorem mem_lowerDegreePatterns_of_lt (input : I → (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (hdegree : thresholdDeg f < d) :
    (fun i ↦ f (input i)) ∈ strictPolynomialSignPatterns
      (lowerDegreeTracePoly (d := d) input) := by
  classical
  obtain ⟨P, hPdeg, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE (thresholdDeg_spec f)
  have hzero (S : Finset (Fin n)) (hS : ¬ S.card < d) : P.coeff S = 0 := by
    by_contra hc
    have := hPdeg S hc
    omega
  have heval (i : I) :
      eval (fun S : LowerDegreeParameter n d ↦ P.coeff S.val)
        (lowerDegreeTracePoly input i) = P.eval (input i) := by
    simp only [lowerDegreeTracePoly, map_sum, map_mul, eval_C, eval_X]
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card < d)
      (by intro S; simp)
      (fun S ↦ squarefreeMonomial S (input i) * P.coeff S)]
    rw [Finset.sum_filter, ← P.fullSum_eq_eval]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S.card < d
    · simp [hS, mul_comm]
    · simp [hS, hzero S hS]
  refine ⟨fun S ↦ P.coeff S.val, fun i ↦ ?_⟩
  rw [heval]
  have hs := hP (input i)
  cases hf : f (input i)
  · have hnonpos : P.eval (input i) ≤ 0 := by
      by_contra! hp
      have := hs.1.mp hp
      simp [hf] at this
    simpa [hf] using lt_of_le_of_ne hnonpos hs.2
  · simpa [hf] using hs.1.mpr hf

omit [Fintype I] in
theorem mem_headPatterns_of_HStar_le (input : I → (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (hheads : HStar n f ≤ H) :
    (fun i ↦ f (input i)) ∈ strictPolynomialSignPatterns
      (fun i ↦ countingClearedPoly (H := H) (input i)) := by
  obtain ⟨point, hpoint⟩ := mem_strictPatterns_of_computable
    (computableWithHeadsN_mono hheads (HStar_computable f))
  exact ⟨point, fun i ↦ hpoint (input i)⟩

/-- Every labeling of a selected grid has a degree-at-most-`d` extension. -/
structure DegreeShatteringFamily (n d : ℕ) (I : Type) [Fintype I] where
  input : I → (Fin n → Bool)
  extend : (I → Bool) → ((Fin n → Bool) → Bool)
  degree : ∀ labels, ThresholdDegLE (extend labels) d
  agrees : ∀ labels i, extend labels (input i) = labels i

noncomputable def headTraceBudget (n H L : ℕ) : ℝ :=
  (4 * Real.exp 1 * (H + 1) * L / (1 + 2 * H * (n + 1))) ^ (1 + 2 * H * (n + 1))

noncomputable def lowerDegreeTraceBudget (n d L : ℕ) : ℝ :=
  (4 * Real.exp 1 * L / Fintype.card (LowerDegreeParameter n d)) ^
    Fintype.card (LowerDegreeParameter n d)

/-- Finite exact-degree separation on any shattered grid. All analytic
dependence is the same explicit Warren premise as in the original count. -/
theorem DegreeShatteringFamily.exists_exact_degree_hard
    (C : DegreeShatteringFamily n d I) (hWarren : WarrenStrictSignPatternBound)
    (hheadDim : 1 + 2 * H * (n + 1) ≤ Fintype.card I)
    (hlowerPos : 0 < Fintype.card (LowerDegreeParameter n d))
    (hlowerDim : Fintype.card (LowerDegreeParameter n d) ≤ Fintype.card I)
    (hbudget : headTraceBudget n H (Fintype.card I) +
      lowerDegreeTraceBudget n d (Fintype.card I) < (2 : ℝ) ^ Fintype.card I) :
    ∃ f : (Fin n → Bool) → Bool, thresholdDeg f = d ∧ H < HStar n f := by
  classical
  let headPatterns := strictPolynomialSignPatterns
    (fun i ↦ countingClearedPoly (H := H) (C.input i))
  let degreePatterns := strictPolynomialSignPatterns (lowerDegreeTracePoly (d := d) C.input)
  have hhead : (headPatterns.ncard : ℝ) ≤ headTraceBudget n H (Fintype.card I) := by
    simpa [headTraceBudget, headPatterns, Nat.cast_add, Nat.cast_mul] using
      hWarren _ (H + 1) _ (by omega) (by omega) hheadDim
      I (CountingParameter n H) _ rfl card_countingParameter
      (fun i ↦ countingClearedPoly_totalDegree_le (C.input i))
  have hlower : (degreePatterns.ncard : ℝ) ≤ lowerDegreeTraceBudget n d (Fintype.card I) := by
    simpa [lowerDegreeTraceBudget] using hWarren _ 1 _ (by omega) hlowerPos hlowerDim
      I (LowerDegreeParameter n d) (lowerDegreeTracePoly C.input) rfl rfl
      (lowerDegreeTracePoly_degree C.input)
  have hex : ∃ labels : I → Bool, labels ∉ headPatterns ∪ degreePatterns := by
    by_contra! hall
    have heq : headPatterns ∪ degreePatterns = Set.univ := Set.eq_univ_of_forall hall
    have hc := Set.ncard_union_le headPatterns degreePatterns
    rw [heq, Set.ncard_univ] at hc
    rw [Nat.card_eq_fintype_card] at hc
    have hcast : ((Fintype.card (I → Bool) : ℕ) : ℝ) ≤
        (headPatterns.ncard : ℝ) + degreePatterns.ncard := by exact_mod_cast hc
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat] at hcast
    linarith
  obtain ⟨labels, hlabels⟩ := hex
  refine ⟨C.extend labels, ?_, ?_⟩
  · apply Nat.le_antisymm (thresholdDeg_le_of_ThresholdDegLE (C.degree labels))
    by_contra! hlt
    have hmem := mem_lowerDegreePatterns_of_lt C.input (C.extend labels) hlt
    have heq : (fun i ↦ C.extend labels (C.input i)) = labels := funext (C.agrees labels)
    rw [heq] at hmem
    exact hlabels (Or.inr hmem)
  · by_contra! hle
    have hmem := mem_headPatterns_of_HStar_le C.input (C.extend labels) hle
    have heq : (fun i ↦ C.extend labels (C.input i)) = labels := funext (C.agrees labels)
    rw [heq] at hmem
    exact hlabels (Or.inl hmem)

end HeadComplexity
