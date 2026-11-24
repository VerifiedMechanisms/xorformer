import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
Finite active-row certificates for compact polyhedra.  This is the analytic
compression ingredient for a partially linear polynomial sign count.
-/

noncomputable section
namespace HeadComplexity.PartialLinearCertificate
open Finset Set Matrix Module
open scoped BigOperators Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def feasible (A : Matrix ι κ ℝ) (b : ι → ℝ) : Set (κ → ℝ) :=
  {x | ∀ i, b i ≤ A i ⬝ᵥ x}

def active (A : Matrix ι κ ℝ) (b : ι → ℝ) (x : κ → ℝ) : Finset ι :=
  univ.filter (fun i => A i ⬝ᵥ x = b i)

private theorem small_perturbation (r v : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, |ε * v i| < r i := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, |t * v i| < r i := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun t : ℝ => |t * v i|) := by fun_prop
    have hi : |(0 : ℝ) * v i| < r i := by simpa using hr i
    exact hc.continuousAt.eventually (gt_mem_nhds hi)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ/2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity)]
  linarith

/-- Every direction annihilating the active rows at an extreme point vanishes. -/
theorem extreme_active_kernel_eq_zero (A : Matrix ι κ ℝ) (b : ι → ℝ)
    {x : κ → ℝ} (hx : x ∈ (feasible A b).extremePoints ℝ)
    (v : κ → ℝ) (hv : ∀ i ∈ active A b x, A i ⬝ᵥ v = 0) : v = 0 := by
  classical
  let r : ι → ℝ := fun i => if A i ⬝ᵥ x = b i then 1 else A i ⬝ᵥ x - b i
  have hr : ∀ i, 0 < r i := by
    intro i
    dsimp [r]
    split_ifs with hi
    · norm_num
    · exact sub_pos.mpr (lt_of_le_of_ne (hx.1 i) (Ne.symm hi))
  obtain ⟨ε,hε,hsmall⟩ := small_perturbation r (fun i => A i ⬝ᵥ v) hr
  have hplus : x + ε • v ∈ feasible A b := by
    intro i
    by_cases hi : A i ⬝ᵥ x = b i
    · have hz := hv i (by simp [active, hi])
      simp [dotProduct_add, dotProduct_smul, hi, hz]
    · have ht := hsmall i
      simp only [r, hi, ↓reduceIte] at ht
      have hb := neg_abs_le (ε * (A i ⬝ᵥ v))
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
  have hminus : x - ε • v ∈ feasible A b := by
    intro i
    by_cases hi : A i ⬝ᵥ x = b i
    · have hz := hv i (by simp [active, hi])
      simp [dotProduct_sub, dotProduct_smul, hi, hz]
    · have ht := hsmall i
      simp only [r, hi, ↓reduceIte] at ht
      have hb := le_abs_self (ε * (A i ⬝ᵥ v))
      simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      linarith
  have he : x + ε • v = x := hx.2 hplus hminus (mem_openSegment_add_sub _ _)
  have hz : ε • v = 0 := add_left_cancel (he.trans (add_zero x).symm)
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt hε)

/-- A nonempty compact polyhedron has a point with an injective active-row map. -/
theorem exists_active_injective (A : Matrix ι κ ℝ) (b : ι → ℝ)
    (hc : IsCompact (feasible A b)) (hne : (feasible A b).Nonempty) :
    ∃ x ∈ feasible A b,
      Function.Injective (fun v : κ → ℝ => fun i : active A b x => A i ⬝ᵥ v) := by
  obtain ⟨x,hx⟩ := hc.extremePoints_nonempty hne
  refine ⟨x,hx.1,?_⟩
  intro v w hvw
  have hz := extreme_active_kernel_eq_zero A b hx (v-w) (by
    intro i hi
    have ht := congrFun hvw ⟨i,hi⟩
    simpa [dotProduct_sub] using sub_eq_zero.mpr ht)
  exact sub_eq_zero.mp hz


variable [DecidableEq κ]

/-- An injective system of row measurements contains a nonsingular square subsystem. -/
theorem exists_nonsingular_rows (A : Matrix ι κ ℝ)
    (hA : Function.Injective A.mulVec) :
    ∃ j : κ → ι, Function.Injective j ∧ (A.submatrix j id).det ≠ 0 := by
  classical
  have hrank : A.rank = Fintype.card κ := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hA, Module.finrank_pi]
  have hspan : Submodule.span ℝ (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_pi]
  obtain ⟨α,j,hj,hsp,hli⟩ := exists_linearIndependent' ℝ A.row
  have : Finite α := Finite.of_injective j hj
  let : Fintype α := Fintype.ofFinite α
  let b : Basis α ℝ (κ → ℝ) := Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = Fintype.card α := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_pi]
  let e : κ ≃ α := Fintype.equivOfCardEq hcard
  refine ⟨j ∘ e, hj.comp e.injective, ?_⟩
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_row_iff_isUnit.mp
  change LinearIndependent ℝ (fun k => A (j (e k)))
  exact hli.comp e e.injective

/-- A compact feasible polyhedron has a feasible point fixed by a basis of active rows. -/
theorem exists_active_basis (A : Matrix ι κ ℝ) (b : ι → ℝ)
    (hc : IsCompact (feasible A b)) (hne : (feasible A b).Nonempty) :
    ∃ x ∈ feasible A b, ∃ j : κ → ι, Function.Injective j ∧
      (∀ k, A (j k) ⬝ᵥ x = b (j k)) ∧ (A.submatrix j id).det ≠ 0 := by
  classical
  obtain ⟨x,hx,hinj⟩ := exists_active_injective A b hc hne
  let M : Matrix (active A b x) κ ℝ := fun i => A i
  obtain ⟨j,hj,hdet⟩ := exists_nonsingular_rows M hinj
  refine ⟨x,hx,Subtype.val ∘ j, Subtype.val_injective.comp hj,?_,hdet⟩
  intro k
  have hk := (j k).property
  change A (j k) ⬝ᵥ x = b (j k)
  exact (Finset.mem_filter.mp hk).2


/-- Add the two coordinate box inequalities in every linear variable. -/
def boundedRows (A : Matrix ι κ ℝ) : Matrix (ι ⊕ (κ ⊕ κ)) κ ℝ :=
  Sum.elim A (Sum.elim (fun k => Pi.single k 1) (fun k => Pi.single k (-1)))

def boundedRhs (b : ι → ℝ) (T : ℝ) : ι ⊕ (κ ⊕ κ) → ℝ :=
  Sum.elim b (fun _ => -T)

omit [Fintype ι] in
theorem feasible_bounded (A : Matrix ι κ ℝ) (b : ι → ℝ) (T : ℝ) :
    feasible (boundedRows A) (boundedRhs b T) =
      feasible A b ∩ Set.Icc (fun _ => -T) (fun _ => T) := by
  ext x
  constructor
  · intro h
    refine ⟨fun i => h (Sum.inl i), ?_, ?_⟩
    · intro k
      have hk := h (Sum.inr (Sum.inl k))
      change -T ≤ Pi.single k 1 ⬝ᵥ x at hk
      simpa using hk
    · intro k
      have hk := h (Sum.inr (Sum.inr k))
      change -T ≤ Pi.single k (-1) ⬝ᵥ x at hk
      simpa using hk
  · rintro ⟨h,hlo,hhi⟩ i
    rcases i with i | (k | k)
    · exact h i
    · change -T ≤ Pi.single k 1 ⬝ᵥ x
      simpa using hlo k
    · change -T ≤ Pi.single k (-1) ⬝ᵥ x
      simpa using hhi k

omit [Fintype ι] [DecidableEq κ] in
theorem isClosed_feasible (A : Matrix ι κ ℝ) (b : ι → ℝ) :
    IsClosed (feasible A b) := by
  change IsClosed {x : κ → ℝ | ∀ i, b i ≤ A i ⬝ᵥ x}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le continuous_const
  exact continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_apply k))

omit [Fintype ι] in
theorem isCompact_feasible_bounded (A : Matrix ι κ ℝ) (b : ι → ℝ) (T : ℝ) :
    IsCompact (feasible (boundedRows A) (boundedRhs b T)) := by
  rw [feasible_bounded]
  exact isCompact_Icc.inter_left (isClosed_feasible A b)

/-- Every nonempty finite system of linear inequalities has a feasible point uniquely
specified by a nonsingular subsystem of its rows and coordinate-box rows. -/
theorem exists_bounded_active_basis (A : Matrix ι κ ℝ) (b : ι → ℝ)
    (hne : (feasible A b).Nonempty) :
    ∃ T : ℝ, ∃ x ∈ feasible A b, ∃ j : κ → ι ⊕ (κ ⊕ κ),
      Function.Injective j ∧
      (∀ k, boundedRows A (j k) ⬝ᵥ x = boundedRhs b T (j k)) ∧
      ((boundedRows A).submatrix j id).det ≠ 0 := by
  classical
  obtain ⟨a,ha⟩ := hne
  let T : ℝ := ∑ k, |a k|
  have hab : a ∈ Set.Icc (fun _ => -T) (fun _ => T) := by
    constructor
    · intro k
      have hk : |a k| ≤ T := single_le_sum (fun i _ => abs_nonneg (a i)) (mem_univ k)
      linarith [neg_abs_le (a k)]
    · intro k
      have hk : |a k| ≤ T := single_le_sum (fun i _ => abs_nonneg (a i)) (mem_univ k)
      exact (le_abs_self _).trans hk
  have hnb : (feasible (boundedRows A) (boundedRhs b T)).Nonempty := by
    rw [feasible_bounded]
    exact ⟨a,ha,hab⟩
  obtain ⟨x,hx,j,hj,hact,hdet⟩ := exists_active_basis
    (boundedRows A) (boundedRhs b T) (isCompact_feasible_bounded A b T) hnb
  refine ⟨T,x,?_,j,hj,hact,hdet⟩
  rw [feasible_bounded] at hx
  exact hx.1


/-- A nonsingular square subsystem reconstructs its solution without division by using
Cramer's numerators. -/
theorem cramer_eq_det_smul {M : Matrix κ κ ℝ} {r x : κ → ℝ}
    (hdet : M.det ≠ 0) (hsolve : M *ᵥ x = r) :
    Matrix.cramer M r = M.det • x := by
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))
  apply hinj
  rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, hsolve]

/-- Multiplying a Cramer numerator score by the determinant preserves its strict sign.
The factor is the positive square of the determinant. -/
theorem sign_cramer {M : Matrix κ κ ℝ} {r x : κ → ℝ}
    (hdet : M.det ≠ 0) (hsolve : M *ᵥ x = r) (a : κ → ℝ) :
    0 < M.det * (a ⬝ᵥ Matrix.cramer M r) ↔ 0 < a ⬝ᵥ x := by
  rw [cramer_eq_det_smul hdet hsolve, dotProduct_smul, smul_eq_mul, ← mul_assoc]
  exact mul_pos_iff_of_pos_left (mul_self_pos.mpr hdet)

omit [Fintype ι] in
/-- Reordering or replacing an injective enumeration of the same row set preserves
nonsingularity. Thus the certificate records an unordered sample subset. -/
theorem det_ne_zero_of_same_range (A : Matrix ι κ ℝ) {j k : κ → ι}
    (hdet : (A.submatrix j id).det ≠ 0) (hrange : Set.range j = Set.range k) :
    (A.submatrix k id).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hinj : Function.Injective (A.submatrix j id).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  apply hinj
  ext i
  have hi : j i ∈ Set.range k := hrange ▸ Set.mem_range_self i
  obtain ⟨i',hi'⟩ := hi
  have heq := congrFun hvw i'
  change A (j i) ⬝ᵥ v = A (j i) ⬝ᵥ w
  change A (k i') ⬝ᵥ v = A (k i') ⬝ᵥ w at heq
  simpa only [hi'] using heq

end HeadComplexity.PartialLinearCertificate
