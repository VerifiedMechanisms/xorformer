import HeadComplexity.Atoms.RoPEGeneralCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Sequences

/-!
# The compact frame obstruction in arbitrary head dimension

The low-rank relation is an explicit closed-relation parameter. Applications
must prove that relation closed and identify its source fiber with the paired
subspace. No tensor-specific conclusion is assumed implicitly.
-/

namespace HeadComplexity.RoPEGeneralFrames

open scoped BigOperators
open RoPEGeneralCoordinates

noncomputable def dot {H : ℕ} (x y : Space H) : ℝ :=
  (∑ i, x.1 i * y.1 i) + ∑ i, x.2 i * y.2 i

theorem sum_zero_of_orthogonal_paired_frame {H : ℕ}
    (w : Fin H → Space H) (v : Space H)
    (hpair : ∀ a, (w a).1 = (w a).2)
    (hgram : ∀ a b, dot (w a) (w b) = if a = b then 1 else 0)
    (horth : ∀ a, dot (w a) v = 0) : total v = 0 := by
  let B : Matrix (Fin H) (Fin H) ℝ := fun a ↦ (w a).1
  let C : Matrix (Fin H) (Fin H) ℝ := (2 : ℝ) • B.transpose
  have hBC : B * C = 1 := by
    ext a b
    have hg := hgram a b
    simp only [dot, ← hpair a, ← hpair b] at hg
    simp only [Matrix.mul_apply, C, Matrix.smul_apply, Matrix.transpose_apply,
      smul_eq_mul, B, Matrix.one_apply]
    calc
      (∑ j, (w a).1 j * (2 * (w b).1 j)) =
          2 * ∑ j, (w a).1 j * (w b).1 j := by rw [Finset.mul_sum]; congr 1; funext; ring
      _ = if a = b then 1 else 0 := by linarith only [hg]
  have hBunit : IsUnit B := by
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro y
    refine ⟨C.mulVec y, ?_⟩
    rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
  let z : Fin H → ℝ := fun i ↦ v.1 i + v.2 i
  have hBz : B.mulVec z = 0 := by
    funext a
    have ho := horth a
    simp only [dot, ← hpair a] at ho
    simpa [B, z, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] using ho
  have hz : z = 0 := Matrix.mulVec_injective_iff_isUnit.mpr hBunit
    (hBz.trans (Matrix.mulVec_zero B).symm)
  dsimp [total]
  rw [← Finset.sum_add_distrib]
  have hz' : ∀ i, v.1 i + v.2 i = 0 := fun i ↦ congrFun hz i
  simp only [hz', Finset.sum_const_zero]

theorem no_unit_sum_orthogonal_paired_frame {H : ℕ}
    (w : Fin H → Space H) (v : Space H)
    (hpair : ∀ a, (w a).1 = (w a).2)
    (hgram : ∀ a b, dot (w a) (w b) = if a = b then 1 else 0)
    (horth : ∀ a, dot (w a) v = 0) (hsum : total v = 1) : False := by
  have hz := sum_zero_of_orthogonal_paired_frame w v hpair hgram horth
  linarith

theorem coordinate_bounds_of_unit_dot {H : ℕ} (x : Space H)
    (hx : dot x x = 1) :
    (∀ i, -1 ≤ x.1 i ∧ x.1 i ≤ 1) ∧ (∀ i, -1 ≤ x.2 i ∧ x.2 i ≤ 1) := by
  have hl : 0 ≤ ∑ i, x.1 i * x.1 i :=
    Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg _)
  have hr : 0 ≤ ∑ i, x.2 i * x.2 i :=
    Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg _)
  dsimp [dot] at hx
  constructor
  · intro i
    have hs : x.1 i * x.1 i ≤ ∑ j, x.1 j * x.1 j :=
      Finset.single_le_sum (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
    constructor <;> nlinarith [sq_nonneg (x.1 i + 1), sq_nonneg (x.1 i - 1)]
  · intro i
    have hs : x.2 i * x.2 i ≤ ∑ j, x.2 j * x.2 j :=
      Finset.single_le_sum (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
    constructor <;> nlinarith [sq_nonneg (x.2 i + 1), sq_nonneg (x.2 i - 1)]

theorem coordinate_bounds_of_simplex {H : ℕ} (v : Space H)
    (hv : (∀ i, 0 ≤ v.1 i) ∧ (∀ i, 0 ≤ v.2 i)) (hsum : total v = 1) :
    (∀ i, v.1 i ≤ 1) ∧ (∀ i, v.2 i ≤ 1) := by
  have hl : 0 ≤ ∑ i, v.1 i := Finset.sum_nonneg (fun i _ ↦ hv.1 i)
  have hr : 0 ≤ ∑ i, v.2 i := Finset.sum_nonneg (fun i _ ↦ hv.2 i)
  dsimp [total] at hsum
  constructor
  · intro i
    have hs : v.1 i ≤ ∑ j, v.1 j :=
      Finset.single_le_sum (fun j _ ↦ hv.1 j) (Finset.mem_univ i)
    linarith
  · intro i
    have hs : v.2 i ≤ ∑ j, v.2 j :=
      Finset.single_le_sum (fun j _ ↦ hv.2 j) (Finset.mem_univ i)
    linarith

/-- A closed low-rank relation whose source fiber is paired excludes limits
of H-dimensional orthonormal frames carrying a nonnegative unit-sum normal. -/
theorem no_tendsto_of_closed_paired_relation {H : ℕ} {T : Type*}
    [TopologicalSpace T] (low : T → Space H → Prop)
    (hlow_closed : IsClosed {p : T × Space H | low p.1 p.2})
    (source : T) (hsource : ∀ v, low source v → v.1 = v.2)
    (t : ℕ → T) (ht : Filter.Tendsto t Filter.atTop (nhds source))
    (hframes : ∀ k, ∃ (w : Fin H → Space H) (v : Space H),
      (∀ a b, dot (w a) (w b) = if a = b then 1 else 0) ∧
      ((∀ i, 0 ≤ v.1 i) ∧ (∀ i, 0 ≤ v.2 i)) ∧ total v = 1 ∧
      (∀ a, dot (w a) v = 0) ∧ (∀ a, low (t k) (w a))) : False := by
  choose w v hgram hvpos hvsum horth hlow using hframes
  let X := (Fin H → Space H) × Space H
  let lo : X := (fun _ ↦ (fun _ ↦ -1, fun _ ↦ -1), (fun _ ↦ 0, fun _ ↦ 0))
  let hi : X := (fun _ ↦ (fun _ ↦ 1, fun _ ↦ 1), (fun _ ↦ 1, fun _ ↦ 1))
  have hbound (k : ℕ) : (w k, v k) ∈ Set.Icc lo hi := by
    have hwbound (a : Fin H) := coordinate_bounds_of_unit_dot (w k a)
      (by simpa using hgram k a a)
    have hvbound := coordinate_bounds_of_simplex (v k) (hvpos k) (hvsum k)
    constructor
    · constructor
      · intro a
        constructor
        · intro i; exact ((hwbound a).1 i).1
        · intro i; exact ((hwbound a).2 i).1
      · exact hvpos k
    · constructor
      · intro a
        constructor
        · intro i; exact ((hwbound a).1 i).2
        · intro i; exact ((hwbound a).2 i).2
      · exact hvbound
  obtain ⟨Z, _, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc lo hi)).tendsto_subseq hbound
  have hw : Filter.Tendsto (fun k ↦ w (φ k)) Filter.atTop (nhds Z.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hv : Filter.Tendsto (fun k ↦ v (φ k)) Filter.atTop (nhds Z.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  have hts : Filter.Tendsto (fun k ↦ t (φ k)) Filter.atTop (nhds source) :=
    ht.comp hφ.tendsto_atTop
  have hp (a : Fin H) : (Z.1 a).1 = (Z.1 a).2 := by
    apply hsource
    have hwa : Filter.Tendsto (fun k ↦ w (φ k) a) Filter.atTop (nhds (Z.1 a)) :=
      (continuous_apply a).continuousAt.tendsto.comp hw
    exact hlow_closed.mem_of_tendsto (hts.prodMk_nhds hwa)
      (Filter.Eventually.of_forall (fun k ↦ hlow (φ k) a))
  have hg (a b : Fin H) : dot (Z.1 a) (Z.1 b) = if a = b then 1 else 0 := by
    have hc : Continuous (fun W : Fin H → Space H ↦ dot (W a) (W b)) := by
      unfold dot
      fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hw)
    simpa only [Function.comp_def, hgram] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ (if a = b then 1 else 0 : ℝ)) Filter.atTop (nhds _))
  have ho (a : Fin H) : dot (Z.1 a) Z.2 = 0 := by
    have hc : Continuous (fun Y : X ↦ dot (Y.1 a) Y.2) := by
      change Continuous (fun Y : (Fin H → Space H) × Space H ↦ dot (Y.1 a) Y.2)
      unfold dot
      fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hlim)
    simpa only [Function.comp_def, horth] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds _))
  have hn : total Z.2 = 1 := by
    have hc : Continuous (fun V : Space H ↦ total V) := by
      unfold total
      fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hv)
    simpa only [Function.comp_def, hvsum] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds _))
  exact no_unit_sum_orthogonal_paired_frame Z.1 Z.2 hp hg ho hn

end HeadComplexity.RoPEGeneralFrames
