import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.style.header false

/-!
# Finite sign gluing for axis-zero modules

This file checks the finite strict-sign preservation argument used by the
reverse-orientation construction. It does not assume or construct the missing
small local compiler. The analytic theorem applies to arbitrary finite cells;
the geometric rank lemma below explains the axis-zero compatibility condition.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Finset Filter
open scoped BigOperators Topology

/-- One existing ratio absorbs any scalar bias without changing its denominator. -/
theorem absorb_bias {n : ℕ} (c a₀ b₀ : ℝ) (a b : Fin n → ℝ)
    (bits : Fin n → Bool) (hB : affineValue b₀ b bits ≠ 0) :
    affineValue (a₀ + c * b₀) (fun i ↦ a i + c * b i) bits /
      affineValue b₀ b bits = c + affineValue a₀ a bits / affineValue b₀ b bits := by
  rw [affineValue_add, affineValue_smul]
  field_simp
  ring

/-- A finite correctly signed module dominates any existing score after scaling. -/
theorem exists_positive_scale {X : Type*} (C : Finset X)
    (σ G F : X → ℝ) (hF : ∀ x ∈ C, 0 < σ x * F x) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ x ∈ C, 0 < σ x * (G x + scale * F x) := by
  classical
  let scale : ℝ := 1 + ∑ x ∈ C, |-(σ x * G x) / (σ x * F x)|
  have hsum : 0 ≤ ∑ x ∈ C, |-(σ x * G x) / (σ x * F x)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨scale, by dsimp [scale]; linarith, ?_⟩
  intro x hx
  have hbound := Finset.single_le_sum
    (fun y (_hy : y ∈ C) ↦ abs_nonneg (-(σ y * G y) / (σ y * F y))) hx
  have hratio : -(σ x * G x) / (σ x * F x) < scale := by
    dsimp [scale]
    have habs := le_abs_self (-(σ x * G x) / (σ x * F x))
    linarith
  have hprod := (div_lt_iff₀ (hF x hx)).mp hratio
  nlinarith

/-- The one-step argument: on the protected part of the downset the new
contribution has a nonnegative signed value; off the downset it tends to zero.
The returned parameter is nonnegative, as required for denominator penalties. -/
theorem glue_step {X : Type*} [DecidableEq X]
    (P C D : Finset X) (σ G F : X → ℝ) (Ft : ℝ → X → ℝ)
    (hCD : C ⊆ D)
    (hG : ∀ x ∈ P, 0 < σ x * G x)
    (hF : ∀ x ∈ C, 0 < σ x * F x)
    (hcompat : ∀ x ∈ P, x ∈ D → 0 ≤ σ x * F x)
    (heq : ∀ t, 0 ≤ t → ∀ x ∈ D, Ft t x = F x)
    (hzero : ∀ x ∈ P, x ∉ D → Tendsto (fun t ↦ Ft t x) atTop (𝓝 0)) :
    ∃ scale t : ℝ, 0 < scale ∧ 0 ≤ t ∧
      ∀ x ∈ P ∪ C, 0 < σ x * (G x + scale * Ft t x) := by
  obtain ⟨scale, hscale, hnew⟩ := exists_positive_scale C σ G F hF
  have hevent : ∀ᶠ t : ℝ in atTop,
      ∀ x ∈ P \ D, 0 < σ x * (G x + scale * Ft t x) := by
    apply (Finset.eventually_all (P \ D)).mpr
    intro x hx
    have hxP := (Finset.mem_sdiff.mp hx).1
    have hxD := (Finset.mem_sdiff.mp hx).2
    have hlim : Tendsto (fun t ↦ σ x * (G x + scale * Ft t x))
        atTop (𝓝 (σ x * G x)) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_const_nhds.add (tendsto_const_nhds.mul (hzero x hxP hxD)))
    exact hlim.eventually (eventually_gt_nhds (hG x hxP))
  obtain ⟨t, ht, hprotect⟩ := ((eventually_ge_atTop (0 : ℝ)).and hevent).exists
  refine ⟨scale, t, hscale, ht, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hxP | hxC
  · by_cases hxD : x ∈ D
    · rw [heq t ht x hxD]
      have hnonneg := mul_nonneg hscale.le (hcompat x hxP hxD)
      have hpos := hG x hxP
      nlinarith
    · exact hprotect x (Finset.mem_sdiff.mpr ⟨hxP, hxD⟩)
  · rw [heq t ht x (hCD hxC)]
    exact hnew x hxC

/-- Complete finite assembly of compatible local modules. Each module is used
once, with a positive numerator scale and a nonnegative denominator penalty.
No margin bound or quantitative rate of convergence is assumed. -/
theorem glue_finite {X : Type*}
    (C D : ℕ → Finset X) (σ : X → ℝ) (F : ℕ → X → ℝ)
    (Ft : ℕ → ℝ → X → ℝ) (N : ℕ)
    (hCD : ∀ i < N, C i ⊆ D i)
    (hF : ∀ i < N, ∀ x ∈ C i, 0 < σ x * F i x)
    (hcompat : ∀ i < N, ∀ j < i, ∀ x ∈ C j,
      x ∈ D i → 0 ≤ σ x * F i x)
    (heq : ∀ i < N, ∀ t, 0 ≤ t → ∀ x ∈ D i, Ft i t x = F i x)
    (hzero : ∀ i < N, ∀ x, x ∉ D i →
      Tendsto (fun t ↦ Ft i t x) atTop (𝓝 0)) :
    ∃ scale param : ℕ → ℝ,
      (∀ i < N, 0 < scale i ∧ 0 ≤ param i) ∧
      ∀ x, (∃ i < N, x ∈ C i) →
        0 < σ x * ∑ i ∈ Finset.range N, scale i * Ft i (param i) x := by
  classical
  revert hCD hF hcompat heq hzero
  induction N with
  | zero =>
      intro _ _ _ _ _
      refine ⟨fun _ ↦ 1, fun _ ↦ 0, ?_, ?_⟩
      · simp
      · intro x hx
        obtain ⟨i, hi, _⟩ := hx
        omega
  | succ N ih =>
      intro hCD hF hcompat heq hzero
      obtain ⟨scale, param, hparams, hsign⟩ := ih
        (fun i hi ↦ hCD i (by omega))
        (fun i hi ↦ hF i (by omega))
        (fun i hi ↦ hcompat i (by omega))
        (fun i hi ↦ heq i (by omega))
        (fun i hi ↦ hzero i (by omega))
      let P := (Finset.range N).biUnion C
      let G : X → ℝ := fun x ↦ ∑ i ∈ Finset.range N, scale i * Ft i (param i) x
      have hG : ∀ x ∈ P, 0 < σ x * G x := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
        exact hsign x ⟨i, Finset.mem_range.mp hi, hxi⟩
      have hcomp : ∀ x ∈ P, x ∈ D N → 0 ≤ σ x * F N x := by
        intro x hx hxD
        obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
        exact hcompat N (by omega) i (Finset.mem_range.mp hi) x hxi hxD
      obtain ⟨scaleN, paramN, hscaleN, hparamN, hstep⟩ :=
        glue_step P (C N) (D N) σ G (F N) (Ft N)
          (hCD N (by omega)) hG (hF N (by omega)) hcomp
          (heq N (by omega)) (fun x _ hx ↦ hzero N (by omega) x hx)
      refine ⟨Function.update scale N scaleN, Function.update param N paramN, ?_, ?_⟩
      · intro i hi
        by_cases he : i = N
        · subst i
          simpa using And.intro hscaleN hparamN
        · have hiN : i < N := by omega
          simpa [Function.update_of_ne he] using hparams i hiN
      · intro x hx
        have hxPC : x ∈ P ∪ C N := by
          obtain ⟨i, hi, hxi⟩ := hx
          by_cases he : i = N
          · subst i
            exact Finset.mem_union_right _ hxi
          · apply Finset.mem_union_left
            exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hxi⟩
        have hsum :
            (∑ i ∈ Finset.range (N + 1),
              Function.update scale N scaleN i *
                Ft i (Function.update param N paramN i) x) =
              G x + scaleN * Ft N paramN x := by
          rw [Finset.sum_range_succ]
          simp only [Function.update_self]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          have hne : i ≠ N := ne_of_lt (Finset.mem_range.mp hi)
          simp [Function.update_of_ne hne]
        rw [hsum]
        exact hstep x hxPC

/-- Descending center ranks leave at most two deletions at an earlier protected
vertex inside the next downset. Consequently that vertex is on an axis or in
the new product of open stars. This is the exact ordering invariant. -/
theorem deletion_counts {r s x y R S : ℕ}
    (hx : x ≤ r) (hy : y ≤ s) (horder : r + s ≤ R + S)
    (hvertex : R + S = x + y + 2) :
    r = x ∨ s = y ∨ (r = x + 1 ∧ s = y + 1) := by
  omega

/-- A finite sum of fixed numerators is suppressed by a positive penalty. -/
theorem ratios_tendsto_zero {I : Type*} [Fintype I]
    (A B : I → ℝ) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun t : ℝ ↦ ∑ h, A h / (B h + t * q)) atTop (𝓝 0) := by
  have hterm (h : I) : Tendsto (fun t : ℝ ↦ A h / (B h + t * q)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_left atTop (B h) (tendsto_id.atTop_mul_const hq)
  simpa using tendsto_finsetSum Finset.univ (fun h _ ↦ hterm h)

/-- Adding a nonnegative coordinate penalty preserves strict atom admissibility. -/
theorem penalty_admissible {n : ℕ} (a₀ b₀ t : ℝ) (a b q : Fin n → ℝ)
    (hb₀ : 0 < b₀) (hb : ∀ i, 0 < b i) (hq : ∀ i, 0 ≤ q i) (ht : 0 ≤ t) :
    ∃ φ : FracAtom n, ∀ bits,
      φ.eval bits = affineValue a₀ a bits /
        (affineValue b₀ b bits + t * affineValue 0 q bits) := by
  have hcoeff (i : Fin n) : 0 < b i + t * q i :=
    add_pos_of_pos_of_nonneg (hb i) (mul_nonneg ht (hq i))
  refine ⟨FracAtom.ofPositiveAffineRatio a₀ a b₀
    (fun i ↦ b i + t * q i) hb₀ hcoeff, ?_⟩
  intro bits
  rw [FracAtom.ofPositiveAffineRatio_eval]
  congr 1
  rw [← affineValue_smul, ← affineValue_add]
  simp

/-- Assembly produces actual original-model atoms, with one atom for each
input ratio. Biases must first be absorbed using `absorb_bias`. The downset
compatibility hypothesis is supplied by axis zeros and `deletion_counts`. -/
theorem glue_positive_affine_ratios {n : ℕ} (N : ℕ) (H : ℕ → ℕ)
    (C D : ℕ → Finset (Fin n → Bool)) (σ : (Fin n → Bool) → ℝ)
    (a₀ b₀ : (i : ℕ) → Fin (H i) → ℝ)
    (a b : (i : ℕ) → Fin (H i) → Fin n → ℝ) (q : ℕ → Fin n → ℝ)
    (hb₀ : ∀ i < N, ∀ h, 0 < b₀ i h)
    (hb : ∀ i < N, ∀ h k, 0 < b i h k)
    (hq : ∀ i < N, ∀ k, 0 ≤ q i k)
    (hCD : ∀ i < N, C i ⊆ D i)
    (hlocal : ∀ i < N, ∀ x ∈ C i,
      0 < σ x * ∑ h, affineValue (a₀ i h) (a i h) x /
        affineValue (b₀ i h) (b i h) x)
    (hcompat : ∀ i < N, ∀ j < i, ∀ x ∈ C j, x ∈ D i →
      0 ≤ σ x * ∑ h, affineValue (a₀ i h) (a i h) x /
        affineValue (b₀ i h) (b i h) x)
    (hqD : ∀ i < N, ∀ x ∈ D i, affineValue 0 (q i) x = 0)
    (hqout : ∀ i < N, ∀ x, x ∉ D i → 0 < affineValue 0 (q i) x) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom n,
      ∀ x, (∃ i < N, x ∈ C i) → 0 < σ x * ∑ h, (φ h).eval x := by
  classical
  let F (i : ℕ) (x : Fin n → Bool) : ℝ :=
    ∑ h, affineValue (a₀ i h) (a i h) x / affineValue (b₀ i h) (b i h) x
  let Ft (i : ℕ) (t : ℝ) (x : Fin n → Bool) : ℝ :=
    ∑ h, affineValue (a₀ i h) (a i h) x /
      (affineValue (b₀ i h) (b i h) x + t * affineValue 0 (q i) x)
  have heq : ∀ i < N, ∀ t, 0 ≤ t → ∀ x ∈ D i, Ft i t x = F i x := by
    intro i hi t _ x hx
    simp [Ft, F, hqD i hi x hx]
  have hzero : ∀ i < N, ∀ x, x ∉ D i →
      Tendsto (fun t ↦ Ft i t x) atTop (𝓝 0) := by
    intro i hi x hx
    exact ratios_tendsto_zero _ _ _ (hqout i hi x hx)
  obtain ⟨scale, param, hparams, hsign⟩ :=
    glue_finite C D σ F Ft N hCD hlocal hcompat heq hzero
  let φ : ((i : Fin N) × Fin (H i.val)) → FracAtom n := fun h ↦
    FracAtom.ofPositiveAffineRatio (scale h.1 * a₀ h.1 h.2)
      (fun k ↦ scale h.1 * a h.1 h.2 k) (b₀ h.1 h.2)
      (fun k ↦ b h.1 h.2 k + param h.1 * q h.1 k)
      (hb₀ h.1 h.1.isLt h.2)
      (fun k ↦ add_pos_of_pos_of_nonneg (hb h.1 h.1.isLt h.2 k)
        (mul_nonneg (hparams h.1 h.1.isLt).2 (hq h.1 h.1.isLt k)))
  have heval (i : Fin N) (h : Fin (H i.val)) (x : Fin n → Bool) :
      (φ ⟨i, h⟩).eval x = scale i *
        (affineValue (a₀ i h) (a i h) x /
          (affineValue (b₀ i h) (b i h) x + param i * affineValue 0 (q i) x)) := by
    simp only [φ, FracAtom.ofPositiveAffineRatio_eval, affineValue_smul]
    have hden : affineValue (b₀ i h)
        (fun k ↦ b i h k + param i * q i k) x =
        affineValue (b₀ i h) (b i h) x + param i * affineValue 0 (q i) x := by
      rw [← affineValue_smul, ← affineValue_add]
      simp
    rw [hden]
    ring
  refine ⟨φ, ?_⟩
  intro x hx
  have hsum : (∑ h, (φ h).eval x) =
      ∑ i ∈ Finset.range N, scale i * Ft i (param i) x := by
    rw [Fintype.sum_sigma]
    simp_rw [heval, ← Finset.mul_sum]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ scale i * Ft i (param i) x) N
  rw [hsum]
  exact hsign x hx

/-- Weakly nonnegative denominator slopes can be made strictly positive after
all assembly. Finite strict signs are preserved with exactly the same heads.
This theorem does not preserve intermediate axis zeros, which are no longer
needed at this final perturbation step. -/
theorem weak_affine_ratios_admissible {n : ℕ} {I : Type*} [Fintype I]
    (P : Finset (Fin n → Bool)) (σ : (Fin n → Bool) → ℝ) (bias : ℝ)
    (a₀ b₀ : I → ℝ) (a b : I → Fin n → ℝ)
    (hb₀ : ∀ h, 0 < b₀ h) (hb : ∀ h k, 0 ≤ b h k)
    (hsign : ∀ x ∈ P, 0 < σ x *
      (bias + ∑ h, affineValue (a₀ h) (a h) x / affineValue (b₀ h) (b h) x)) :
    ∃ φ : I → FracAtom n, ∀ x ∈ P,
      0 < σ x * (bias + ∑ h, (φ h).eval x) := by
  classical
  let delta : ℝ → ℝ := fun t ↦ 1 / (t + 1)
  have hdelta : Tendsto delta atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hden (h : I) (x : Fin n → Bool) : 0 < affineValue (b₀ h) (b h) x := by
    unfold affineValue
    apply add_pos_of_pos_of_nonneg (hb₀ h)
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (hb h k)
    cases x k <;> simp [boolToReal]
  have hrewrite (h : I) (x : Fin n → Bool) (t : ℝ) :
      affineValue (b₀ h) (fun k ↦ b h k + delta t) x =
        affineValue (b₀ h) (b h) x + delta t * ∑ k, boolToReal (x k) := by
    simp only [affineValue, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hterm (h : I) (x : Fin n → Bool) :
      Tendsto (fun t ↦ affineValue (a₀ h) (a h) x /
        affineValue (b₀ h) (fun k ↦ b h k + delta t) x) atTop
        (𝓝 (affineValue (a₀ h) (a h) x / affineValue (b₀ h) (b h) x)) := by
    simp_rw [hrewrite]
    apply Tendsto.div tendsto_const_nhds _ (ne_of_gt (hden h x))
    simpa using tendsto_const_nhds.add (hdelta.mul_const (∑ k, boolToReal (x k)))
  have hevent : ∀ᶠ t : ℝ in atTop, ∀ x ∈ P,
      0 < σ x * (bias + ∑ h, affineValue (a₀ h) (a h) x /
        affineValue (b₀ h) (fun k ↦ b h k + delta t) x) := by
    apply (Finset.eventually_all P).mpr
    intro x hx
    have hlim := ((tendsto_finsetSum Finset.univ (fun h _ ↦ hterm h x)).const_add bias).const_mul
      (σ x)
    exact hlim.eventually (eventually_gt_nhds (hsign x hx))
  obtain ⟨t, ht, hsign'⟩ := ((eventually_ge_atTop (0 : ℝ)).and hevent).exists
  have hdpos : 0 < delta t := by dsimp [delta]; positivity
  refine ⟨fun h ↦ FracAtom.ofPositiveAffineRatio (a₀ h) (a h) (b₀ h)
    (fun k ↦ b h k + delta t) (hb₀ h) (fun k ↦ add_pos_of_nonneg_of_pos (hb h k) hdpos), ?_⟩
  simpa only [FracAtom.ofPositiveAffineRatio_eval] using hsign'

/-- Flattening the assembled atom family costs exactly the sum of local heads. -/
theorem glued_head_count (N : ℕ) (H : ℕ → ℕ) :
    Fintype.card ((i : Fin N) × Fin (H i.val)) = ∑ i ∈ Finset.range N, H i := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range H N

end AxisZeroGluing
end HeadComplexity
