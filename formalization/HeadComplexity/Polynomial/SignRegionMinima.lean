import HeadComplexity.Polynomial.GenericClosestPoint
import HeadComplexity.Polynomial.ConstrainedMinimaBound
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Strict minima representing sign regions

A common squared-distance objective has one strict minimum in each nonempty
closed sign region. The active constraints at those minima will index the
quantitative sign-pattern count.
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial Set Filter Metric
open scoped Topology

/-- Orient a polynomial according to a Boolean sign. -/
noncomputable def signedPolynomial {K : Type*} (b : Bool)
    (p : MvPolynomial K ℝ) : MvPolynomial K ℝ :=
  if b then p else -p

/-- A closed sign region with strictly positive margins. -/
def closedSignRegion {J : Type*} {n : ℕ} (p : J → MvPolynomial (Fin n) ℝ)
    (ε : J → ℝ) (σ : J → Bool) : Set (Fin n → ℝ) :=
  {x | ∀ j, ε j ≤ eval x (signedPolynomial (σ j) (p j))}

theorem isClosed_closedSignRegion {J : Type*} {n : ℕ}
    (p : J → MvPolynomial (Fin n) ℝ) (ε : J → ℝ) (σ : J → Bool) :
    IsClosed (closedSignRegion p ε σ) := by
  change IsClosed {x | ∀ j, ε j ≤ eval x (signedPolynomial (σ j) (p j))}
  simp only [ofPred_forall]
  exact isClosed_iInter fun j ↦ isClosed_le continuous_const
    (continuous_eval (signedPolynomial (σ j) (p j)))

/-- Distinct sign vectors have disjoint positive-margin regions. -/
theorem signs_eq_of_common_region {J : Type*} {n : ℕ}
    (p : J → MvPolynomial (Fin n) ℝ) (ε : J → ℝ) (hε : ∀ j, 0 < ε j)
    {σ τ : J → Bool} {x : Fin n → ℝ}
    (hσ : x ∈ closedSignRegion p ε σ) (hτ : x ∈ closedSignRegion p ε τ) : σ = τ := by
  funext j
  have hs := hσ j
  have ht := hτ j
  have he := hε j
  cases hsj : σ j <;> cases htj : τ j <;>
    simp_all [signedPolynomial] <;> linarith [hε j]

/-- A common quadratic objective has distinct strict minima in all the
specified nonempty positive-margin sign regions. -/
theorem exists_strict_region_minima {J T : Type*} [Finite T] {n : ℕ}
    (p : J → MvPolynomial (Fin n) ℝ) (ε : J → ℝ) (hε : ∀ j, 0 < ε j)
    (σ : T → J → Bool) (hσ : Function.Injective σ)
    (hne : ∀ t, (closedSignRegion p ε (σ t)).Nonempty) :
    ∃ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ 2 ∧
      ∃ x : T → Fin n → ℝ, Function.Injective x ∧
        (∀ t, x t ∈ closedSignRegion p ε (σ t)) ∧
        ∀ t y, y ∈ closedSignRegion p ε (σ t) → y ≠ x t → eval (x t) q < eval y q := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let S (t : T) : Set E := {x | WithLp.ofLp x ∈ closedSignRegion p ε (σ t)}
  have hS (t : T) : IsClosed (S t) :=
    (isClosed_closedSignRegion p ε (σ t)).preimage (PiLp.continuous_ofLp 2 _)
  have hSne (t : T) : (S t).Nonempty := by
    obtain ⟨x, hx⟩ := hne t
    exact ⟨WithLp.toLp 2 x, hx⟩
  obtain ⟨b, hb⟩ := exists_common_unique_closestPoint S hS hSne
  choose a ha hauniq using hb
  let q : MvPolynomial (Fin n) ℝ := ∑ i, (C (b i) - X i) ^ 2
  have hq (z : Fin n → ℝ) : eval z q = dist b (WithLp.toLp 2 z) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp only [q, map_sum, map_pow, map_sub, eval_C, eval_X]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hqdeg : q.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i _
    apply (totalDegree_pow _ 2).trans
    have hlin : (C (b i) - X i : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (by simp)
    simpa using Nat.mul_le_mul_left 2 hlin
  let x (t : T) : Fin n → ℝ := WithLp.ofLp (a t)
  have hxregion (t : T) : x t ∈ closedSignRegion p ε (σ t) := (ha t).1
  have hxinj : Function.Injective x := by
    intro t u htu
    apply hσ
    exact signs_eq_of_common_region p ε hε (hxregion t) (htu.symm ▸ hxregion u)
  refine ⟨q, hqdeg, x, hxinj, hxregion, fun t y hy hne ↦ ?_⟩
  have hyS : WithLp.toLp 2 y ∈ S t := hy
  have hle : dist b (a t) ≤ dist b (WithLp.toLp 2 y) := by
    rw [← (ha t).2]
    exact infDist_le_dist_of_mem hyS
  have hlt : dist b (a t) < dist b (WithLp.toLp 2 y) := by
    apply lt_of_le_of_ne hle
    intro heq
    have he := hauniq t (WithLp.toLp 2 y) ⟨hyS, (ha t).2.trans heq⟩
    exact hne (congrArg WithLp.ofLp he)
  rw [hq, hq]
  change dist b (a t) ^ 2 < dist b (WithLp.toLp 2 y) ^ 2
  exact (sq_lt_sq₀ dist_nonneg dist_nonneg).mpr hlt

/-- Constraints attained at their prescribed margin. -/
noncomputable def activeConstraints {J : Type*} [Fintype J] {n : ℕ}
    (p : J → MvPolynomial (Fin n) ℝ) (ε : J → ℝ) (σ : J → Bool) (x : Fin n → ℝ) : Finset J :=
  Finset.univ.filter fun j ↦ eval x (signedPolynomial (σ j) (p j)) = ε j

@[simp]
theorem mem_activeConstraints {J : Type*} [Fintype J] {n : ℕ}
    (p : J → MvPolynomial (Fin n) ℝ) (ε : J → ℝ) (σ : J → Bool)
    (x : Fin n → ℝ) (j : J) :
    j ∈ activeConstraints p ε σ x ↔ eval x (signedPolynomial (σ j) (p j)) = ε j := by
  classical
  simp [activeConstraints]

/-- Inactive inequalities stay strict locally, so a strict minimum on a region
is a strict local minimum on the algebraic set of its active constraints. -/
theorem strict_localMin_active {J : Type*} [Fintype J] {n : ℕ}
    (p : J → MvPolynomial (Fin n) ℝ) (ε : J → ℝ) (σ : J → Bool)
    (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : x ∈ closedSignRegion p ε σ)
    (hmin : ∀ y, y ∈ closedSignRegion p ε σ → y ≠ x → eval x q < eval y q) :
    ∀ᶠ y in 𝓝 x,
      (∀ j : activeConstraints p ε σ x,
        eval y (signedPolynomial (σ j) (p j) - C (ε j)) = 0) →
      y ≠ x → eval x q < eval y q := by
  classical
  have hloc (j : J) : ∀ᶠ y in 𝓝 x, j ∉ activeConstraints p ε σ x →
      ε j < eval y (signedPolynomial (σ j) (p j)) := by
    by_cases hj : j ∈ activeConstraints p ε σ x
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hj).elim
    have hstrict : ε j < eval x (signedPolynomial (σ j) (p j)) :=
      lt_of_le_of_ne (hx j) (Ne.symm (not_congr (mem_activeConstraints p ε σ x j) |>.mp hj))
    have hc : ContinuousAt (fun y ↦ eval y (signedPolynomial (σ j) (p j))) x :=
      (continuous_eval _).continuousAt
    filter_upwards [hc.eventually (eventually_gt_nhds hstrict)] with y hy _
    exact hy
  filter_upwards [Filter.eventually_all.mpr hloc] with y hy hzero hne
  apply hmin y (fun j ↦ ?_) hne
  by_cases hj : j ∈ activeConstraints p ε σ x
  · have hh := hzero ⟨j, hj⟩
    have heq : eval y (signedPolynomial (σ j) (p j)) = ε j := by
      simpa only [map_sub, eval_C, sub_eq_zero] using hh
    exact heq.ge
  · exact (hy j hj).le

/-- Algebraically independent margins allow at most as many active constraints
as there are real variables. -/
theorem activeConstraints_card_le {J : Type*} [Fintype J] {n : ℕ}
    (F : Type*) [Field F] [CharZero F] [Algebra F ℝ]
    (p : J → MvPolynomial (Fin n) ℝ) (P : J → MvPolynomial (Fin n) F)
    (ε : J → ℝ) (hε : AlgebraicIndependent F ε) (σ : J → Bool) (x : Fin n → ℝ)
    (hP : ∀ j, eval x (p j) = aeval x (P j)) :
    (activeConstraints p ε σ x).card ≤ n := by
  classical
  let A := activeConstraints p ε σ x
  let Q (j : A) : MvPolynomial (Fin n) F := if σ j then P j else -(P j)
  have hval : (fun j : A ↦ aeval x (Q j)) = (fun j : A ↦ ε j) := by
    funext j
    have hh := (mem_activeConstraints p ε σ x j).mp j.2
    cases hs : σ j <;> simpa [Q, signedPolynomial, hs, hP] using hh
  have hi := hε.comp (fun j : A ↦ (j : J)) Subtype.val_injective
  have hlin := linearIndependent_jacobian_of_values x Q (hval.symm ▸ hi)
  simpa only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    using hlin.fintype_card_le_finrank

/-- One algebraically independent positive margin vector preserves a finite
family of strict sign realizations. -/
theorem exists_generic_positive_margins {J T : Type*} [Finite J] [Finite T] {n : ℕ}
    (F : Type*) [Field F] [Countable F] [Algebra F ℝ]
    (p : J → MvPolynomial (Fin n) ℝ) (σ : T → J → Bool) (x : T → Fin n → ℝ)
    (hx : ∀ t j, 0 < eval (x t) (signedPolynomial (σ t j) (p j))) :
    ∃ ε : J → ℝ, AlgebraicIndependent F ε ∧ (∀ j, 0 < ε j) ∧
      ∀ t, x t ∈ closedSignRegion p ε (σ t) := by
  let := Fintype.ofFinite J
  obtain ⟨η, hη, hbound⟩ := exists_pos_lt_finite
    (fun tj : T × J ↦ eval (x tj.1) (signedPolynomial (σ tj.1 tj.2) (p tj.2)))
    (fun tj ↦ hx tj.1 tj.2)
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨ε, hεball, hεind⟩ := (dense_algebraicIndependent F J).inter_open_nonempty
    (ball (fun _ : J ↦ η / 2) (η / 2)) isOpen_ball
    ⟨_, mem_ball_self hη2⟩
  have hb (j : J) : 0 < ε j ∧ ε j < η := by
    have hd := (dist_pi_lt_iff hη2).mp hεball j
    rw [Real.dist_eq, abs_lt] at hd
    constructor <;> linarith [hd.1, hd.2]
  exact ⟨ε, hεind, fun j ↦ (hb j).1, fun t j ↦
    ((hb j).2.trans (hbound (t, j))).le⟩

end HeadComplexity.PolynomialRootCount
