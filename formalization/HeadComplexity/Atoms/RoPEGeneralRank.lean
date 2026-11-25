import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The pair-equation kernel in the arbitrary-head tensor obstruction

This file proves the finite-dimensional linear algebra used in the general-head
extension. It does not identify these equations with polynomial derivatives;
that coefficient calculation is stated separately in the mathematical proof.
-/

namespace HeadComplexity.RoPEGeneralRank

open Module

variable {ι : Type*}

/-- The symmetric off-diagonal equations associated with a direction d. -/
def PairEquations (d e : ι → ℝ) : Prop :=
  ∀ i j, i ≠ j → d i * e j + d j * e i = 0

theorem pairEquations_sub {d e f : ι → ℝ}
    (he : PairEquations d e) (hf : PairEquations d f) :
    PairEquations d (e - f) := by
  intro i j hij
  have he' := he i j hij
  have hf' := hf i j hij
  change d i * (e j - f j) + d j * (e i - f i) = 0
  linarith

/-- A solution is determined by one coordinate at which the direction is nonzero. -/
theorem eq_zero_of_pairEquations_of_coordinate_zero
    {d e : ι → ℝ} {s : ι} (hs : d s ≠ 0)
    (he : PairEquations d e) (hes : e s = 0) : e = 0 := by
  funext j
  by_cases hjs : j = s
  · simpa [hjs] using hes
  · have h := he s j (Ne.symm hjs)
    rw [hes, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hs

theorem eq_of_pairEquations_of_coordinate_eq
    {d e f : ι → ℝ} {s : ι} (hs : d s ≠ 0)
    (he : PairEquations d e) (hf : PairEquations d f)
    (hcoord : e s = f s) : e = f := by
  have hsub : e - f = 0 :=
    eq_zero_of_pairEquations_of_coordinate_zero hs
      (pairEquations_sub he hf) (sub_eq_zero.mpr hcoord)
  exact sub_eq_zero.mp hsub

/-- The pair-equation solution space. -/
def pairKernel (d : ι → ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {e | PairEquations d e}
  zero_mem' := by intro i j hij; simp
  add_mem' := by
    intro e f he hf i j hij
    have he' := he i j hij
    have hf' := hf i j hij
    change d i * (e j + f j) + d j * (e i + f i) = 0
    linarith
  smul_mem' := by
    intro c e he i j hij
    have he' := he i j hij
    change d i * (c * e j) + d j * (c * e i) = 0
    calc
      _ = c * (d i * e j + d j * e i) := by ring
      _ = 0 := by rw [he', mul_zero]

theorem finrank_pairKernel_le_one {d : ι → ℝ} {s : ι} (hs : d s ≠ 0) :
    finrank ℝ (pairKernel d) ≤ 1 := by
  let coordinate : pairKernel d →ₗ[ℝ] ℝ :=
    { toFun := fun e => e.1 s
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective coordinate := by
    intro e f h
    apply Subtype.ext
    exact eq_of_pairEquations_of_coordinate_eq hs e.property f.property h
  simpa using coordinate.finrank_le_finrank_of_injective hinj

/-- Two successive pair-equation constraints bound a kernel by two dimensions. -/
theorem finrank_le_two_of_pair_constraints
    (K : Submodule ℝ ((ι → ℝ) × (ι → ℝ)))
    {d : ι → ℝ} {s : ι} (hs : d s ≠ 0)
    (he : ∀ w ∈ K, PairEquations d w.1)
    (hb : ∀ w ∈ K, w.1 = 0 → PairEquations d w.2) :
    finrank ℝ K ≤ 2 := by
  let coordinates : K →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun w => (w.1.1 s, w.1.2 s)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective coordinates := by
    intro x y hxy
    have hfst : x.1.1 s = y.1.1 s := congrArg Prod.fst hxy
    have hsnd : x.1.2 s = y.1.2 s := congrArg Prod.snd hxy
    have hw : x.1 - y.1 ∈ K := K.sub_mem x.property y.property
    have hezero : (x.1 - y.1).1 = 0 :=
      eq_zero_of_pairEquations_of_coordinate_zero hs
        (he _ hw) (sub_eq_zero.mpr hfst)
    have hbzero : (x.1 - y.1).2 = 0 :=
      eq_zero_of_pairEquations_of_coordinate_zero hs
        (hb _ hw hezero) (sub_eq_zero.mpr hsnd)
    apply Subtype.ext
    apply sub_eq_zero.mp
    exact Prod.ext hezero hbzero
  simpa using coordinates.finrank_le_finrank_of_injective hinj

/-- A map on twice as many coordinates as indices whose kernel has the pair
constraints has rank at least twice the index count minus two. -/
theorem twice_card_le_rank_add_two
    [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : ((ι → ℝ) × (ι → ℝ)) →ₗ[ℝ] V)
    {d : ι → ℝ} {s : ι} (hs : d s ≠ 0)
    (he : ∀ w ∈ T.ker, PairEquations d w.1)
    (hb : ∀ w ∈ T.ker, w.1 = 0 → PairEquations d w.2) :
    2 * Fintype.card ι ≤ finrank ℝ T.range + 2 := by
  have hker := finrank_le_two_of_pair_constraints T.ker hs he hb
  have hrank := T.finrank_range_add_finrank_ker
  simp only [Module.finrank_prod, Module.finrank_pi] at hrank
  omega

theorem card_lt_rank_of_three_le
    [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : ((ι → ℝ) × (ι → ℝ)) →ₗ[ℝ] V)
    {d : ι → ℝ} {s : ι} (hs : d s ≠ 0)
    (he : ∀ w ∈ T.ker, PairEquations d w.1)
    (hb : ∀ w ∈ T.ker, w.1 = 0 → PairEquations d w.2)
    (hcard : 3 ≤ Fintype.card ι) :
    Fintype.card ι < finrank ℝ T.range := by
  have h := twice_card_le_rank_add_two T hs he hb
  omega

end HeadComplexity.RoPEGeneralRank
