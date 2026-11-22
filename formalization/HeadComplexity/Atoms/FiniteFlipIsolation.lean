import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.style.header false

/-! A selected pair of flips isolates its target on a Hamming sphere of radius
two. This is the Boolean combinatorial input to the reciprocal pole argument. -/
namespace HeadComplexity.FiniteFlipIsolation

open scoped symmDiff

variable {I : Type*} [DecidableEq I]

theorem pair_isolates (center target x pair : Finset I)
    (hpair : pair.card = 2) (htarget : target ∆ center = pair)
    (hsphere : (x ∆ center).card = 2) (hcontains : pair ⊆ x ∆ center) :
    x = target := by
  have hp : pair = x ∆ center :=
    Finset.eq_of_subset_of_card_le hcontains (by omega)
  apply symmDiff_left_injective center
  exact hp.symm.trans htarget.symm

noncomputable def numerator (center pair x : Finset I) : ℝ :=
  if pair ⊆ x ∆ center then 1 else 0

noncomputable def offset (center x : Finset I) : ℤ :=
  2 - ((x ∆ center).card : ℤ)

theorem numerator_abs_le (center pair x : Finset I) :
    |numerator center pair x| ≤ 1 := by
  unfold numerator
  split_ifs <;> norm_num

theorem target_values (center target pair : Finset I)
    (hpair : pair.card = 2) (htarget : target ∆ center = pair) :
    offset center target = 0 ∧ numerator center pair target = 1 := by
  simp [offset, numerator, htarget, hpair]

theorem off_target_vanishes (center target x pair : Finset I)
    (hpair : pair.card = 2) (htarget : target ∆ center = pair)
    (hneq : x ≠ target) (hoffset : offset center x = 0) :
    numerator center pair x = 0 := by
  have hsphere : (x ∆ center).card = 2 := by
    unfold offset at hoffset
    omega
  have hnot : ¬ pair ⊆ x ∆ center := by
    intro hcontains
    exact hneq (pair_isolates center target x pair hpair htarget hsphere hcontains)
  simp [numerator, hnot]

theorem numerator_pair_product (center x : Finset I) (i j : I) :
    numerator center {i, j} x =
      (if i ∈ x ∆ center then (1 : ℝ) else 0) *
      (if j ∈ x ∆ center then (1 : ℝ) else 0) := by
  simp only [numerator, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  split_ifs <;> simp_all

end HeadComplexity.FiniteFlipIsolation
