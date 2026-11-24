import HeadComplexity.Results.QuadraticProductUpperBound
import HeadComplexity.Results.RoPETwoHeads

set_option linter.style.header false

/-!
# Four vanilla heads for complement-invariant three-head rotary classifiers

The statement holds for arbitrary affine fractions with positive denominators,
and therefore for both scalar rotary variants. It is an upper bound of four,
not the requested head-preserving bound of three.
-/

namespace HeadComplexity

open scoped BigOperators

namespace CubeAffine

variable {n : ℕ}

noncomputable def center (L : CubeAffine n) : ℝ := L.const + (∑ i, L.slope i) / 2

noncomputable def odd (L : CubeAffine n) : CubeAffine n :=
  ⟨-(∑ i, L.slope i) / 2, L.slope⟩

theorem eval_center_odd (L : CubeAffine n) (x : Fin n → Bool) :
    L.eval x = L.center + L.odd.eval x := by
  simp only [center, odd, eval]
  ring

theorem odd_eval_flip (L : CubeAffine n) (x : Fin n → Bool) :
    L.odd.eval (fun i ↦ !(x i)) = -L.odd.eval x := by
  have hs : (∑ i, L.slope i * boolToReal (!(x i))) =
      (∑ i, L.slope i) - ∑ i, L.slope i * boolToReal (x i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [boolToReal]
  simp only [odd, eval, hs]
  ring

/-- The even part of three products, each with two denominator factors, is a
constant plus three products of affine forms. -/
theorem three_product_even_part (N D : Fin 3 → CubeAffine n) :
    ∃ (A B : Fin 3 → CubeAffine n) (c : ℝ), ∀ x,
      c + ∑ j, (A j).eval x * (B j).eval x =
        ((N 0).eval x * (D 1).eval x * (D 2).eval x +
          (N 1).eval x * (D 0).eval x * (D 2).eval x +
          (N 2).eval x * (D 0).eval x * (D 1).eval x +
          (N 0).eval (fun i ↦ !(x i)) * (D 1).eval (fun i ↦ !(x i)) *
            (D 2).eval (fun i ↦ !(x i)) +
          (N 1).eval (fun i ↦ !(x i)) * (D 0).eval (fun i ↦ !(x i)) *
            (D 2).eval (fun i ↦ !(x i)) +
          (N 2).eval (fun i ↦ !(x i)) * (D 0).eval (fun i ↦ !(x i)) *
            (D 1).eval (fun i ↦ !(x i))) / 2 := by
  let A₀ := combine 1 (combine (N 2).center (D 1).odd (N 1).center (D 2).odd)
    1 (combine (D 2).center (N 1).odd (D 1).center (N 2).odd)
  let A₁ := combine (N 0).center (D 2).odd 1
    (combine (D 2).center (N 0).odd (D 0).center (N 2).odd)
  let A₂ := combine (D 1).center (N 0).odd (D 0).center (N 1).odd
  refine ⟨![A₀, A₁, A₂], fun j ↦ (D j).odd,
    (N 0).center * (D 1).center * (D 2).center +
      (N 1).center * (D 0).center * (D 2).center +
      (N 2).center * (D 0).center * (D 1).center, fun x ↦ ?_⟩
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, A₀, A₁, A₂, combine_eval]
  conv_rhs => simp only [eval_center_odd (N 0), eval_center_odd (N 1),
    eval_center_odd (N 2), eval_center_odd (D 0), eval_center_odd (D 1),
    eval_center_odd (D 2), odd_eval_flip]
  ring

end CubeAffine

/-- Three positive affine fractions computing a complement-invariant function
can be replaced by four admissible vanilla fractions. -/
theorem vanilla_four_of_three_positive_fractions_complement
    {n : ℕ} (r : Fin 3 → AffineFraction n) (c : ℝ)
    (hpos : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true))
    (hcomp : ∀ x, f (fun i ↦ !(x i)) = f x) :
    computableWithSharedHeadsN n 4 f := by
  classical
  obtain ⟨δ, _, hδ⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (r h).eval x)
  let c' := c - δ
  let N : Fin 3 → CubeAffine n :=
    ![CubeAffine.combine 1 (r 0).numForm c' (r 0).denForm,
      (r 1).numForm, (r 2).numForm]
  let D : Fin 3 → CubeAffine n := fun h ↦ (r h).denForm
  let P (x : Fin n → Bool) :=
    (N 0).eval x * (D 1).eval x * (D 2).eval x +
      (N 1).eval x * (D 0).eval x * (D 2).eval x +
      (N 2).eval x * (D 0).eval x * (D 1).eval x
  have hclear (x : Fin n → Bool) :
      (r 0).denominator x * (r 1).denominator x * (r 2).denominator x *
        (c' + ∑ h, (r h).eval x) = P x := by
    simp [P, N, D, CubeAffine.combine_eval, Fin.sum_univ_three, AffineFraction.eval]
    field_simp [(hpos 0 x).ne', (hpos 1 x).ne', (hpos 2 x).ne']
    ring
  have hstrict (x : Fin n → Bool) :
      (0 < c' + ∑ h, (r h).eval x ↔ f x = true) ∧
        c' + ∑ h, (r h).eval x ≠ 0 := by
    have he : c' + ∑ h, (r h).eval x = (c + ∑ h, (r h).eval x) - δ := by
      dsimp [c']
      ring
    rw [he]
    exact ⟨(hδ x).1.trans (hf x), (hδ x).2⟩
  have hP (x : Fin n → Bool) : (0 < P x ↔ f x = true) ∧ P x ≠ 0 := by
    have hp := mul_pos (mul_pos (hpos 0 x) (hpos 1 x)) (hpos 2 x)
    rw [← hclear]
    exact ⟨(mul_pos_iff_of_pos_left hp).trans (hstrict x).1,
      mul_ne_zero hp.ne' (hstrict x).2⟩
  obtain ⟨A, B, T, hAB⟩ := CubeAffine.three_product_even_part N D
  have hAB' (x : Fin n → Bool) :
      T + ∑ j, (A j).eval x * (B j).eval x = (P x + P (fun i ↦ !(x i))) / 2 := by
    rw [hAB]
    dsimp [P]
    ring
  have hQ (x : Fin n → Bool) :
      (0 < T + ∑ j, (A j).eval x * (B j).eval x ↔ f x = true) ∧
        T + ∑ j, (A j).eval x * (B j).eval x ≠ 0 := by
    rw [hAB']
    have hx := hP x
    have hy := hP (fun i ↦ !(x i))
    rw [hcomp] at hy
    by_cases hftrue : f x = true
    · have hp : 0 < (P x + P (fun i ↦ !(x i))) / 2 := by
        exact div_pos (add_pos (hx.1.mpr hftrue) (hy.1.mpr hftrue)) two_pos
      exact ⟨iff_of_true hp hftrue, hp.ne'⟩
    · have hxneg : P x < 0 := lt_of_le_of_ne (le_of_not_gt (mt hx.1.mp hftrue)) hx.2
      have hyneg : P (fun i ↦ !(x i)) < 0 :=
        lt_of_le_of_ne (le_of_not_gt (mt hy.1.mp hftrue)) hy.2
      have hneg : (P x + P (fun i ↦ !(x i))) / 2 < 0 := by linarith
      exact ⟨iff_of_false (not_lt_of_gt hneg) hftrue, hneg.ne⟩
  exact CubeAffine.computable_of_strict_product_sum A B T f
    (fun x ↦ (hQ x).1) (fun x ↦ (hQ x).2)

theorem vanilla_four_of_retainedRoPE_three_complement
    {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : retainedRoPEComputable n 3 f)
    (hcomp : ∀ x, f (fun i ↦ !(x i)) = f x) :
    computableWithSharedHeadsN n 4 f := by
  obtain ⟨p, c, hp⟩ := hf
  exact vanilla_four_of_three_positive_fractions_complement
    (fun h ↦ (p h).toAffineFraction) c (fun h ↦ (p h).denominator_pos) f hp hcomp

theorem vanilla_four_of_pureRoPE_three_complement
    {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : pureRoPEComputable n 3 f)
    (hcomp : ∀ x, f (fun i ↦ !(x i)) = f x) :
    computableWithSharedHeadsN n 4 f := by
  exact vanilla_four_of_retainedRoPE_three_complement (retainedRoPEComputable_of_pure hf) hcomp

end HeadComplexity
