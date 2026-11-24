import HeadComplexity.Results.PureRoPETwoHeads
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.Continuity

set_option linter.style.header false

/-!
# Three vanilla heads compile two affine products

A strict Boolean sign representation by an affine term plus two products of
affine forms has a three-head realization. Denominators share a large common
oriented direction and approach a constant; the finite input cube provides one
positive perturbation size preserving every strict sign.
-/

namespace HeadComplexity
namespace TwoProductsThreeHeads

open scoped BigOperators Topology
open RoPETwoHead Filter

variable {n : ℕ}

/-- Strict signs of finitely many continuous functions persist together at
some strictly positive parameter. -/
theorem exists_positive_preserving {ι : Type*} [Finite ι]
    (F : ℝ → ι → ℝ) (hF : ∀ i, ContinuousAt (fun t ↦ F t i) 0)
    (h0 : ∀ i, F 0 i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (0 < F t i ↔ 0 < F 0 i) := by
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, (0 < F t i ↔ 0 < F 0 i) := by
    rw [eventually_all]
    intro i
    rcases lt_or_gt_of_ne (h0 i) with hn | hp
    · filter_upwards [(hF i).tendsto.eventually_lt_const hn] with t ht
      exact iff_of_false (not_lt_of_ge ht.le) (not_lt_of_ge hn.le)
    · filter_upwards [(hF i).tendsto.eventually_const_lt hp] with t ht
      exact iff_of_true ht hp
  obtain ⟨l, u, hlu, hsub⟩ := he.exists_Ioo_subset
  refine ⟨u / 2, by linarith [hlu.2], hsub ?_⟩
  exact ⟨by linarith [hlu.1, hlu.2], by linarith [hlu.2]⟩

/-- Arbitrary affine product factors are allowed. The only strictness
assumption concerns the target score on the finite Boolean cube. -/
theorem computable_three (r a b c d : Form n) (f : (Fin n → Bool) → Bool)
    (hne : ∀ x, r.eval x + a.eval x * b.eval x + c.eval x * d.eval x ≠ 0)
    (hf : ∀ x, (0 < r.eval x + a.eval x * b.eval x + c.eval x * d.eval x) ↔
      f x = true) :
    computableWithSharedHeadsN n 3 f := by
  classical
  let z : Form n := ⟨0, fun i ↦ 1 + |b.v i| + |d.v i|⟩
  let v : Fin 3 → Form n := ![z.lin b 1 1, z.lin d 1 1, z]
  have hv (h : Fin 3) (i) : 0 < (v h).v i := by
    have hb := neg_le_abs (b.v i)
    have hd := neg_le_abs (d.v i)
    have hb0 := abs_nonneg (b.v i)
    have hd0 := abs_nonneg (d.v i)
    fin_cases h <;> norm_num [v, Form.lin, z] <;> linarith
  let E (t : ℝ) (h : Fin 3) : Form n :=
    ⟨1 - t * (v h).c, fun i ↦ -t * (v h).v i⟩
  have hE (t : ℝ) (h : Fin 3) (x) : (E t h).eval x = 1 - t * (v h).eval x := by
    simp only [E, Form.eval, mul_assoc, ← Finset.mul_sum]
    ring
  let P (t : ℝ) (x : Fin n → Bool) :=
    a.eval x * b.eval x * (E t 1).eval x +
      c.eval x * d.eval x * (E t 0).eval x + r.eval x * (E t 0).eval x * (E t 1).eval x
  have hP0 (x) : P 0 x = r.eval x + a.eval x * b.eval x + c.eval x * d.eval x := by
    simp [P, hE]
    ring
  let F (t : ℝ) : ((Fin n → Bool) ⊕ (Fin 3 × (Fin n → Bool))) → ℝ
    | .inl x => P t x
    | .inr hx => (E t hx.1).eval hx.2
  obtain ⟨t, ht, hsign⟩ := exists_positive_preserving F (by
    intro i
    rcases i with x | ⟨h, x⟩
    · change ContinuousAt (fun t ↦ P t x) 0
      simp only [P, hE]
      fun_prop
    · change ContinuousAt (fun t ↦ (E t h).eval x) 0
      simp only [hE]
      fun_prop) (by
    intro i
    rcases i with x | ⟨h, x⟩
    · simpa only [F, hP0] using hne x
    · simp [F, hE])
  have hpos (h : Fin 3) (x) : 0 < (E t h).eval x := by
    apply (hsign (.inr (h, x))).mpr
    simp [F, hE]
  let N : Fin 3 → Form n := ![a, c, (a.lin c (-1) (-1)).lin r 1 t]
  let q (h : Fin 3) := fraction (N h) (E t h)
  have hq (h : Fin 3) : (q h).Admissible := by
    apply fraction_admissible _ _ (hpos h)
    right
    intro i
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) (hv h i)
  have hid (x) : (∑ h, (q h).eval x) *
      ((E t 0).eval x * (E t 1).eval x * (E t 2).eval x) = t * P t x := by
    have h0 := (hpos 0 x).ne'
    have h1 := (hpos 1 x).ne'
    have h2 := (hpos 2 x).ne'
    simp only [Fin.sum_univ_succ, q, fraction_eval, N, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Form.lin_eval, Fin.sum_univ_zero, add_zero]
    change (a.eval x / (E t 0).eval x +
      (c.eval x / (E t 1).eval x +
        (1 * (-1 * a.eval x + -1 * c.eval x) + t * r.eval x) / (E t 2).eval x)) *
        ((E t 0).eval x * (E t 1).eval x * (E t 2).eval x) = t * P t x
    field_simp [h0, h1, h2]
    have hv2 : v 2 = z := rfl
    simp only [P, hE, hv2]
    norm_num [v, Form.lin_eval]
    ring
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 3 f).mpr
  refine ⟨q, 0, hq, ?_⟩
  intro x
  have hprod : 0 < (E t 0).eval x * (E t 1).eval x * (E t 2).eval x :=
    mul_pos (mul_pos (hpos 0 x) (hpos 1 x)) (hpos 2 x)
  simp only [zero_add]
  rw [← mul_pos_iff_of_pos_right hprod, hid, mul_pos_iff_of_pos_left ht]
  exact (hsign (.inl x)).trans (by simpa [F, hP0] using hf x)

end TwoProductsThreeHeads

/-- Every two-head positive-affine-fraction classifier has a vanilla three-head
realization. This includes retained rotary attention with arbitrary mixed
denominator directions. -/
theorem vanilla_three_of_positiveFraction_two {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : positiveFractionComputable n 2 f) :
    computableWithSharedHeadsN n 3 f := by
  classical
  obtain ⟨q, c, hq, hsign⟩ := hf
  let S (x : Fin n → Bool) := c + (q 0).eval x + (q 1).eval x
  have hS (x) : 0 < S x ↔ f x = true := by
    simpa [S, Fin.sum_univ_two, add_assoc] using hsign x
  obtain ⟨δ, hδ, hsmall⟩ := RoPETwoHead.exists_positive_shift S f hS
  let a := (RoPETwoHead.numerator (q 0)).lin (RoPETwoHead.denominator (q 0)) 1 (c - δ)
  let b := RoPETwoHead.denominator (q 1)
  let d := RoPETwoHead.denominator (q 0)
  let e := RoPETwoHead.numerator (q 1)
  let z : RoPETwoHead.Form n := ⟨0, fun _ ↦ 0⟩
  have hb (x) : 0 < b.eval x := hq 1 x
  have hd (x) : 0 < d.eval x := hq 0 x
  have hid (x) : z.eval x + a.eval x * b.eval x + e.eval x * d.eval x =
      d.eval x * b.eval x * (S x - δ) := by
    have hb0 := (hb x).ne'
    have hd0 := (hd x).ne'
    have hq0 : (q 0).eval x = (RoPETwoHead.numerator (q 0)).eval x / d.eval x := rfl
    have hq1 : (q 1).eval x = e.eval x / b.eval x := rfl
    simp only [a, z, RoPETwoHead.Form.eval, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add] at *
    change _ = _ * _ * ((c + (q 0).eval x + (q 1).eval x) - δ)
    rw [hq0, hq1]
    field_simp [hb0, hd0]
    simp only [RoPETwoHead.Form.lin, one_mul,
      add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  apply TwoProductsThreeHeads.computable_three z a b e d f
  · intro x
    rw [hid]
    apply mul_ne_zero (mul_ne_zero (hd x).ne' (hb x).ne')
    cases hx : f x
    · have hnon : S x ≤ 0 := le_of_not_gt (by simpa [hx] using hS x)
      linarith
    · have := hsmall x hx
      linarith
  · intro x
    rw [hid, mul_pos_iff_of_pos_left (mul_pos (hd x) (hb x))]
    constructor
    · intro h
      apply (hS x).mp
      linarith
    · intro h
      exact sub_pos.mpr (hsmall x h)

/-- The retained two-head upper comparison is valid in the original vanilla
architecture through its established affine-fraction equivalence. -/
theorem vanilla_three_of_retainedRoPE_two {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : retainedRoPEComputable n 2 f) :
    computableWithSharedHeadsN n 3 f :=
  vanilla_three_of_positiveFraction_two (positiveFractionComputable_of_retained hf)

end HeadComplexity
