import HeadComplexity.Results.MonomialStarCover
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option linter.style.header false

/-!
# Real-rate finite alteration for monomial star covers

All probabilities are finite products of the two real weights `p` and `1-p`.
The proof is algebraic, including the zero and one endpoints.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace FiniteBernoulliCover

noncomputable def weight {ι : Type*} [Fintype ι] (p : ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then p else 1 - p

private theorem weighted_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (g : ι → Bool → ℝ) :
    (∑ ω : ι → Bool, weight p ω * ∏ i, g i (ω i)) =
      ∏ i, ((1 - p) * g i false + p * g i true) := by
  simp only [weight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a ↦ (if a then p else 1 - p) * g i a)]
  simp [add_comm]

private theorem sum_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    (∑ ω : ι → Bool, weight p ω) = 1 := by
  have h := weighted_prod p (fun (_ : ι) (_ : Bool) ↦ (1 : ℝ))
  simpa using h

private theorem weighted_avoids {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (A : Finset ι) :
    (∑ ω : ι → Bool, weight p ω *
      (if ∀ i ∈ A, ω i = false then (1 : ℝ) else 0)) = (1 - p) ^ A.card := by
  classical
  let g : ι → Bool → ℝ :=
    fun i a ↦ if i ∈ A → a = false then 1 else 0
  have hpoint : ∀ ω : ι → Bool,
      (if ∀ i ∈ A, ω i = false then (1 : ℝ) else 0) = ∏ i, g i (ω i) := by
    intro ω
    simp [g, Fintype.prod_boole]
  simp_rw [hpoint]
  rw [weighted_prod]
  have hmean : ∀ i, (1 - p) * g i false + p * g i true =
      if i ∈ A then 1 - p else 1 := by
    intro i
    by_cases hi : i ∈ A <;> simp [g, hi]
  simp_rw [hmean]
  simp

/-- Independent real-rate selection and one repair for every missed target. -/
theorem exists_cover_card_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (neighbors : κ → Finset ι) (patch : κ → ι)
    (hpatch : ∀ t, patch t ∈ neighbors t)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    ∃ C : Finset ι, (∀ t, ∃ i ∈ C, i ∈ neighbors t) ∧
      (C.card : ℝ) ≤ (Fintype.card ι : ℝ) * p +
        ∑ t, (1 - p) ^ (neighbors t).card := by
  classical
  let selected : (ι → Bool) → Finset ι :=
    fun ω ↦ Finset.univ.filter fun i ↦ ω i = true
  let missed : (ι → Bool) → Finset κ :=
    fun ω ↦ Finset.univ.filter fun t ↦ ∀ i ∈ neighbors t, ω i = false
  let cost : (ι → Bool) → ℝ :=
    fun ω ↦ (selected ω).card + (missed ω).card
  have hw : ∀ ω : ι → Bool, 0 ≤ weight p ω := by
    intro ω
    apply Finset.prod_nonneg
    intro i _
    split <;> linarith
  have hsel : ∀ ω, ((selected ω).card : ℝ) =
      ∑ i, if ω i = true then (1 : ℝ) else 0 := by
    intro ω
    simp [selected]
  have hmiss : ∀ ω, ((missed ω).card : ℝ) =
      ∑ t, if ∀ i ∈ neighbors t, ω i = false then (1 : ℝ) else 0 := by
    intro ω
    simp [missed]
  have hsingle : ∀ i : ι,
      (∑ ω : ι → Bool, weight p ω * (if ω i = true then (1 : ℝ) else 0)) = p := by
    intro i
    have havoid := weighted_avoids p ({i} : Finset ι)
    simp only [Finset.mem_singleton, forall_eq, Finset.card_singleton, pow_one] at havoid
    have hpoint : ∀ ω : ι → Bool,
        (if ω i = true then (1 : ℝ) else 0) =
          1 - (if ω i = false then (1 : ℝ) else 0) := by
      intro ω
      cases ω i <;> norm_num
    simp_rw [hpoint, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, sum_weight, havoid]
    ring
  have hmean : (∑ ω : ι → Bool, weight p ω * cost ω) =
      (Fintype.card ι : ℝ) * p + ∑ t, (1 - p) ^ (neighbors t).card := by
    simp only [cost, hsel, hmiss, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hsingle]
    rw [Finset.sum_comm]
    simp_rw [weighted_avoids]
    simp
  obtain ⟨ω, _, hmin⟩ := (Finset.univ : Finset (ι → Bool)).exists_min_image
    cost Finset.univ_nonempty
  have hsmall : cost ω ≤ (Fintype.card ι : ℝ) * p +
      ∑ t, (1 - p) ^ (neighbors t).card := by
    have h := Finset.sum_le_sum fun η (_ : η ∈ Finset.univ) ↦
      mul_le_mul_of_nonneg_left (hmin η (Finset.mem_univ η)) (hw η)
    rw [← Finset.sum_mul, sum_weight, one_mul, hmean] at h
    exact h
  refine ⟨selected ω ∪ (missed ω).image patch, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ missed ω
    · exact ⟨patch t, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩),
        hpatch t⟩
    · have ht' : ∃ i ∈ neighbors t, ω i = true := by simpa [missed] using ht
      obtain ⟨i, hi, htrue⟩ := ht'
      exact ⟨i, Finset.mem_union_left _ (by simp [selected, htrue]), hi⟩
  · have hcard : (selected ω ∪ (missed ω).image patch).card ≤
        (selected ω).card + (missed ω).card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left Finset.card_image_le _)
    exact (by dsimp [cost]; exact_mod_cast hcard :
      ((selected ω ∪ (missed ω).image patch).card : ℝ) ≤ cost ω).trans hsmall

/-- A partial cover with a discounted repair set. This is the finite
weighted alteration lemma used by the block recursion. -/
theorem exists_patch_card_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (neighbors : κ → Finset ι) (p δ : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    ∃ (S : Finset ι) (T : Finset κ),
      (∀ t, t ∉ T → ∃ i ∈ S, i ∈ neighbors t) ∧
      (S.card : ℝ) + δ * T.card ≤ (Fintype.card ι : ℝ) * p +
        δ * ∑ t, (1 - p) ^ (neighbors t).card := by
  classical
  let selected : (ι → Bool) → Finset ι :=
    fun ω ↦ Finset.univ.filter fun i ↦ ω i = true
  let missed : (ι → Bool) → Finset κ :=
    fun ω ↦ Finset.univ.filter fun t ↦ ∀ i ∈ neighbors t, ω i = false
  let cost : (ι → Bool) → ℝ :=
    fun ω ↦ (selected ω).card + δ * (missed ω).card
  have hw : ∀ ω : ι → Bool, 0 ≤ weight p ω := by
    intro ω
    apply Finset.prod_nonneg
    intro i _
    split <;> linarith
  have hsel : ∀ ω, ((selected ω).card : ℝ) =
      ∑ i, if ω i = true then (1 : ℝ) else 0 := by
    intro ω
    simp [selected]
  have hmiss : ∀ ω, ((missed ω).card : ℝ) =
      ∑ t, if ∀ i ∈ neighbors t, ω i = false then (1 : ℝ) else 0 := by
    intro ω
    simp [missed]
  have hsingle : ∀ i : ι,
      (∑ ω : ι → Bool, weight p ω * (if ω i = true then (1 : ℝ) else 0)) = p := by
    intro i
    have havoid := weighted_avoids p ({i} : Finset ι)
    simp only [Finset.mem_singleton, forall_eq, Finset.card_singleton, pow_one] at havoid
    have hpoint : ∀ ω : ι → Bool,
        (if ω i = true then (1 : ℝ) else 0) =
          1 - (if ω i = false then (1 : ℝ) else 0) := by
      intro ω
      cases ω i <;> norm_num
    simp_rw [hpoint, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, sum_weight, havoid]
    ring
  have hmean : (∑ ω : ι → Bool, weight p ω * cost ω) =
      (Fintype.card ι : ℝ) * p + δ * ∑ t, (1 - p) ^ (neighbors t).card := by
    simp only [cost, hsel, hmiss, mul_add, Finset.sum_add_distrib]
    have hfirst : (∑ ω : ι → Bool, weight p ω *
        ∑ i, if ω i = true then (1 : ℝ) else 0) = (Fintype.card ι : ℝ) * p := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [hsingle]
      simp
    rw [hfirst]
    congr 1
    simp_rw [show ∀ ω : ι → Bool,
      weight p ω * (δ * ∑ t,
        if ∀ i ∈ neighbors t, ω i = false then (1 : ℝ) else 0) =
      δ * (weight p ω * ∑ t,
        if ∀ i ∈ neighbors t, ω i = false then (1 : ℝ) else 0) by intro ω; ring]
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [weighted_avoids]
  obtain ⟨ω, _, hmin⟩ := (Finset.univ : Finset (ι → Bool)).exists_min_image
    cost Finset.univ_nonempty
  have hsmall : cost ω ≤ (Fintype.card ι : ℝ) * p +
      δ * ∑ t, (1 - p) ^ (neighbors t).card := by
    have h := Finset.sum_le_sum fun η (_ : η ∈ Finset.univ) ↦
      mul_le_mul_of_nonneg_left (hmin η (Finset.mem_univ η)) (hw η)
    rw [← Finset.sum_mul, sum_weight, one_mul, hmean] at h
    exact h
  refine ⟨selected ω, missed ω, ?_, hsmall⟩
  intro t ht
  have ht' : ∃ i ∈ neighbors t, ω i = true := by simpa [missed] using ht
  obtain ⟨i, hi, htrue⟩ := ht'
  exact ⟨i, by simp [selected, htrue], hi⟩

end FiniteBernoulliCover

/-- Exact universal alteration budget for any real selection rate in `[0,1]`. -/
noncomputable def bernoulliStarBudget (n : ℕ) (p : ℝ) : ℝ :=
  (2 : ℝ) ^ n * p + (1 - p) * (2 - p) ^ n

/-- A star cover with the exact real-rate alteration budget. -/
theorem exists_universal_starCover_bernoulli (n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hpone : p ≤ 1) :
    ∃ C : Finset (Finset (Fin n)),
      (∀ T, ∃ S ∈ C, MonomialStar S T) ∧
        (C.card : ℝ) ≤ bernoulliStarBudget n p := by
  classical
  obtain ⟨C, hcover, hcard⟩ := FiniteBernoulliCover.exists_cover_card_le
    (monomialPredecessors (n := n)) id
    (fun T ↦ Finset.mem_insert_self T _) p hp hpone
  refine ⟨C, fun T ↦ ?_, ?_⟩
  · obtain ⟨S, hS, hST⟩ := hcover T
    exact ⟨S, hS, (mem_monomialPredecessors_iff S T).mp hST⟩
  · have hsum (q : ℝ) : (∑ T : Finset (Fin n), q ^ T.card) = (1 + q) ^ n := by
      have h := Fintype.prod_add (fun _ : Fin n ↦ q) (fun _ ↦ (1 : ℝ))
      simpa [add_comm] using h.symm
    simp only [card_monomialPredecessors, pow_succ,
      Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hcard
    rw [← Finset.sum_mul, hsum] at hcard
    simpa only [show (1 : ℝ) + (1 - p) = 2 - p by ring,
      mul_comm, bernoulliStarBudget] using hcard

/-- Real-rate alteration is connected to the unchanged attention model. -/
theorem HStar_real_le_bernoulliStarBudget {n : ℕ}
    (f : (Fin n → Bool) → Bool) (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    (HStar n f : ℝ) ≤ bernoulliStarBudget n p := by
  obtain ⟨C, hcover, hcard⟩ := exists_universal_starCover_bernoulli n p hp hpone
  obtain ⟨P, _, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f)
  have hcomp := P.HStar_le_of_starCover f hP C (fun T _ ↦ hcover T)
  exact (by exact_mod_cast hcomp : (HStar n f : ℝ) ≤ C.card).trans hcard

/-- Round the exact alteration bound downward. -/
theorem HStar_le_floor_bernoulliStarBudget {n : ℕ}
    (f : (Fin n → Bool) → Bool) (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    HStar n f ≤ ⌊bernoulliStarBudget n p⌋₊ :=
  Nat.le_floor (HStar_real_le_bernoulliStarBudget f p hp hpone)

end HeadComplexity
