import HeadComplexity.Results.RestrictedCounting
import HeadComplexity.Results.StarDegreeUpperBound

set_option linter.style.header false

/-!
# Fixed-degree hard functions from one-hot tensor grids

Every sign tensor on an `m^d` one-hot grid has a strict degree-`d` extension
on `d*m` bits. The restricted counting theorem excludes both smaller degree
and small head counts, with explicit finite Warren budgets.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {d m : ℕ}

def oneHotInput (index : Fin d → Fin m) (position : Fin (d * m)) : Bool :=
  decide ((finProdFinEquiv.symm position).2 = index (finProdFinEquiv.symm position).1)

noncomputable def oneHotScore (labels : (Fin d → Fin m) → Bool) :
    MvPolynomial (Fin (d * m)) ℝ :=
  (∑ index : Fin d → Fin m, C (if labels index then 1 else -1) *
    ∏ j : Fin d, X (finProdFinEquiv (j, index j))) - C (1 / 2)

theorem eval_oneHot_monomial (index target : Fin d → Fin m) :
    eval (cubePoint (oneHotInput target))
      (∏ j : Fin d, (X (finProdFinEquiv (j, index j)) : MvPolynomial (Fin (d * m)) ℝ)) =
      if index = target then 1 else 0 := by
  classical
  rw [map_prod]
  by_cases heq : index = target
  · subst index
    simp [oneHotInput, cubePoint, boolToReal]
  · rw [ite_eq_right heq]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp heq
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [oneHotInput, cubePoint, boolToReal, hj]

theorem oneHotScore_eval (labels : (Fin d → Fin m) → Bool) (target : Fin d → Fin m) :
    eval (cubePoint (oneHotInput target)) (oneHotScore labels) =
      (if labels target then 1 else -1) - 1 / 2 := by
  classical
  simp only [oneHotScore, map_sub, map_sum, map_mul, eval_C, eval_oneHot_monomial]
  simp

theorem oneHotScore_degree (labels : (Fin d → Fin m) → Bool) :
    (oneHotScore labels).totalDegree ≤ d := by
  refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
  apply totalDegree_finsetSum_le
  intro index _
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_finsetProd _ _).trans (by simp)

noncomputable def oneHotExtension (labels : (Fin d → Fin m) → Bool)
    (bits : Fin (d * m) → Bool) : Bool :=
  decide (0 < eval (cubePoint bits) (oneHotScore labels))

noncomputable def oneHotShatteringFamily (d m : ℕ) :
    DegreeShatteringFamily (d * m) d (Fin d → Fin m) where
  input := oneHotInput
  extend := oneHotExtension
  degree := fun labels ↦ ⟨oneHotScore labels, oneHotScore_degree labels, by
    intro bits
    simp [oneHotExtension]⟩
  agrees := by
    intro labels target
    rw [oneHotExtension, oneHotScore_eval]
    cases labels target <;> norm_num

/-- Explicit finite form of the exact fixed-degree separation. The two
budgets account respectively for low heads and degree strictly below `d`. -/
theorem exists_exact_fixed_degree_hard (d m H : ℕ)
    (hWarren : WarrenStrictSignPatternBound)
    (hheadDim : 1 + 2 * H * (d * m + 1) ≤ m ^ d)
    (hlowerPos : 0 < Fintype.card (LowerDegreeParameter (d * m) d))
    (hlowerDim : Fintype.card (LowerDegreeParameter (d * m) d) ≤ m ^ d)
    (hbudget : headTraceBudget (d * m) H (m ^ d) +
      lowerDegreeTraceBudget (d * m) d (m ^ d) < (2 : ℝ) ^ (m ^ d)) :
    ∃ f : (Fin (d * m) → Bool) → Bool,
      thresholdDeg f = d ∧ H < HStar (d * m) f := by
  apply (oneHotShatteringFamily d m).exists_exact_degree_hard hWarren
  · simpa using hheadDim
  · exact hlowerPos
  · simpa using hlowerDim
  · simpa using hbudget

/-- Maximum head count in one exact threshold-degree class. -/
noncomputable def degreeClassHeadMaximum (n d : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin n → Bool) → Bool)).filter
    fun f ↦ thresholdDeg f = d).sup fun f ↦ HStar n f

theorem degree_le_degreeClassHeadMaximum {n d : ℕ}
    (hclass : ∃ f : (Fin n → Bool) → Bool, thresholdDeg f = d) :
    d ≤ degreeClassHeadMaximum n d := by
  classical
  obtain ⟨f, hdegree⟩ := hclass
  have hhead := thresholdDeg_le_HStar f
  rw [hdegree] at hhead
  exact hhead.trans (Finset.le_sup (f := fun g ↦ HStar n g)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hdegree⟩))

theorem degreeClassHeadMaximum_le_starDegreeBound (n d : ℕ) :
    degreeClassHeadMaximum n d ≤ starDegreeBound n d := by
  classical
  apply Finset.sup_le
  intro f hf
  have hdegree := (Finset.mem_filter.mp hf).2
  exact HStar_le_starDegreeBound_of_ThresholdDegLE (hdegree ▸ thresholdDeg_spec f)

/-- The restricted count gives the lower endpoint for the exact-degree maximum. -/
theorem fixed_degree_maximum_gt (d m H : ℕ)
    (hWarren : WarrenStrictSignPatternBound)
    (hheadDim : 1 + 2 * H * (d * m + 1) ≤ m ^ d)
    (hlowerPos : 0 < Fintype.card (LowerDegreeParameter (d * m) d))
    (hlowerDim : Fintype.card (LowerDegreeParameter (d * m) d) ≤ m ^ d)
    (hbudget : headTraceBudget (d * m) H (m ^ d) +
      lowerDegreeTraceBudget (d * m) d (m ^ d) < (2 : ℝ) ^ (m ^ d)) :
    H < degreeClassHeadMaximum (d * m) d := by
  classical
  obtain ⟨f, hdegree, hheads⟩ := exists_exact_fixed_degree_hard d m H
    hWarren hheadDim hlowerPos hlowerDim hbudget
  exact hheads.trans_le (Finset.le_sup (f := fun g ↦ HStar (d * m) g)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hdegree⟩))

end HeadComplexity
