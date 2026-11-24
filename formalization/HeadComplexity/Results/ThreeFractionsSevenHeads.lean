import HeadComplexity.Results.TwoProductsThreeHeads

set_option linter.style.header false

/-! # Seven vanilla heads compile three affine triple products -/

namespace HeadComplexity.ThreeFractionsSevenHeads
noncomputable section
open scoped BigOperators Topology
open RoPETwoHead
variable {n : ℕ}

def normalizedSecond (r b d t : ℝ) : ℝ :=
  b * d * (2 * r + t * (b + d)) /
    (r * (r + t * b) * (r + t * d) * (r + t * (b + d)))

theorem second_difference (r b d t : ℝ) (hr : r ≠ 0)
    (hb : r + t * b ≠ 0) (hd : r + t * d ≠ 0) (hbd : r + t * (b + d) ≠ 0) :
    1 / r - 1 / (r + t * b) - 1 / (r + t * d) + 1 / (r + t * (b + d)) =
      t ^ 2 * normalizedSecond r b d t := by
  unfold normalizedSecond
  field_simp [hr, hb, hd, hbd]
  ring

theorem normalizedSecond_zero (r b d : ℝ) (hr : r ≠ 0) :
    normalizedSecond r b d 0 = 2 * b * d / r ^ 3 := by
  unfold normalizedSecond
  simp only [zero_mul, add_zero]
  field_simp [hr]

theorem normalizedSecond_continuous (r b d : ℝ) (hr : r ≠ 0) :
    ContinuousAt (normalizedSecond r b d) 0 := by
  unfold normalizedSecond
  fun_prop (disch := simpa using hr)

def cubic (U D : Fin 3 → Form n) (x : Fin n → Bool) : ℝ :=
  (U 0).eval x * (D 1).eval x * (D 2).eval x +
    (U 1).eval x * (D 0).eval x * (D 2).eval x +
    (U 2).eval x * (D 0).eval x * (D 1).eval x

/-- Denominator factors can have arbitrary signs. Strictness concerns only
 the target cubic on the finite Boolean cube. -/
theorem computable_seven (U D : Fin 3 → Form n) (f : (Fin n → Bool) → Bool)
    (hne : ∀ x, cubic U D x ≠ 0)
    (hf : ∀ x, (0 < cubic U D x) ↔ f x = true) :
    computableWithSharedHeadsN n 7 f := by
  classical
  let R : Form n := ⟨1, fun _ ↦ 1⟩
  have hR (x) : 0 < R.eval x := by
    have hs : 0 ≤ ∑ i, boolToReal (x i) := by
      apply Finset.sum_nonneg
      intro i _
      cases x i <;> norm_num [boolToReal]
    simp only [R, Form.eval, one_mul]
    linarith
  let E (t : ℝ) : Fin 7 → Form n :=
    ![R, R.lin (D 0) 1 t, R.lin (D 1) 1 t, R.lin (D 2) 1 t,
      R.lin ((D 0).lin (D 1) 1 1) 1 t,
      R.lin ((D 0).lin (D 2) 1 1) 1 t,
      R.lin ((D 1).lin (D 2) 1 1) 1 t]
  have hE0 (h : Fin 7) : E 0 h = R := by
    fin_cases h <;> ext <;> simp [E, Form.lin]
  let G (t : ℝ) (x : Fin n → Bool) :=
    (U 0).eval x * normalizedSecond (R.eval x) ((D 1).eval x) ((D 2).eval x) t +
      (U 1).eval x * normalizedSecond (R.eval x) ((D 0).eval x) ((D 2).eval x) t +
      (U 2).eval x * normalizedSecond (R.eval x) ((D 0).eval x) ((D 1).eval x) t
  have hG0 (x) : G 0 x = 2 * cubic U D x / (R.eval x) ^ 3 := by
    simp only [G, normalizedSecond_zero _ _ _ (hR x).ne', cubic]
    ring
  let F (t : ℝ) : ((Fin n → Bool) ⊕ ((Fin 7 × (Fin n → Bool)) ⊕ (Fin 7 × Fin n))) → ℝ
    | .inl x => G t x
    | .inr (.inl hx) => (E t hx.1).eval hx.2
    | .inr (.inr hi) => (E t hi.1).v hi.2
  obtain ⟨t, ht, hsign⟩ := TwoProductsThreeHeads.exists_positive_preserving F (by
    intro i
    rcases i with x | (⟨h, x⟩ | ⟨h, i⟩)
    · change ContinuousAt (fun t ↦ G t x) 0
      exact ((continuousAt_const.mul (normalizedSecond_continuous _ _ _ (hR x).ne')).add
        (continuousAt_const.mul (normalizedSecond_continuous _ _ _ (hR x).ne'))).add
          (continuousAt_const.mul (normalizedSecond_continuous _ _ _ (hR x).ne'))
    · change ContinuousAt (fun t ↦ (E t h).eval x) 0
      fin_cases h <;> dsimp [E, Form.lin, Form.eval] <;> fun_prop
    · change ContinuousAt (fun t ↦ (E t h).v i) 0
      fin_cases h <;> dsimp [E, Form.lin] <;> fun_prop) (by
    intro i
    rcases i with x | (⟨h, x⟩ | ⟨h, i⟩)
    · change G 0 x ≠ 0
      rw [hG0]
      exact div_ne_zero (mul_ne_zero (by norm_num) (hne x)) (pow_ne_zero _ (hR x).ne')
    · simpa only [F, hE0] using (hR x).ne'
    · simp only [F, hE0, R]
      norm_num)
  have hp (h : Fin 7) (x) : 0 < (E t h).eval x := by
    apply (hsign (.inr (.inl (h, x)))).mpr
    simpa only [F, hE0] using hR x
  have hv (h : Fin 7) (i) : 0 < (E t h).v i := by
    apply (hsign (.inr (.inr (h, i)))).mpr
    simp [F, hE0, R]
  let N : Fin 7 → Form n :=
    ![((U 0).lin (U 1) 1 1).lin (U 2) 1 1,
      (U 1).lin (U 2) (-1) (-1), (U 0).lin (U 2) (-1) (-1),
      (U 0).lin (U 1) (-1) (-1), U 2, U 1, U 0]
  let q (h : Fin 7) := fraction (N h) (E t h)
  have hq (h : Fin 7) : (q h).Admissible :=
    fraction_admissible _ _ (hp h) (Or.inl (hv h))
  have he1 (x) : R.eval x + t * (D 0).eval x ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 1 x).ne'
  have he2 (x) : R.eval x + t * (D 1).eval x ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 2 x).ne'
  have he3 (x) : R.eval x + t * (D 2).eval x ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 3 x).ne'
  have he4 (x) : R.eval x + t * ((D 0).eval x + (D 1).eval x) ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 4 x).ne'
  have he5 (x) : R.eval x + t * ((D 0).eval x + (D 2).eval x) ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 5 x).ne'
  have he6 (x) : R.eval x + t * ((D 1).eval x + (D 2).eval x) ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 6 x).ne'
  have hid (x) : (∑ h, (q h).eval x) = t ^ 2 * G t x := by
    calc
      _ = (U 0).eval x * (1 / R.eval x - 1 / (R.eval x + t * (D 1).eval x) -
          1 / (R.eval x + t * (D 2).eval x) +
          1 / (R.eval x + t * ((D 1).eval x + (D 2).eval x))) +
        (U 1).eval x * (1 / R.eval x - 1 / (R.eval x + t * (D 0).eval x) -
          1 / (R.eval x + t * (D 2).eval x) +
          1 / (R.eval x + t * ((D 0).eval x + (D 2).eval x))) +
        (U 2).eval x * (1 / R.eval x - 1 / (R.eval x + t * (D 0).eval x) -
          1 / (R.eval x + t * (D 1).eval x) +
          1 / (R.eval x + t * ((D 0).eval x + (D 1).eval x))) := by
        simp [q, N, E, Fin.sum_univ_succ, fraction_eval, Form.lin_eval, div_eq_mul_inv]
        ring
      _ = _ := by
        rw [second_difference _ _ _ _ (hR x).ne' (he2 x) (he3 x) (he6 x),
          second_difference _ _ _ _ (hR x).ne' (he1 x) (he3 x) (he5 x),
          second_difference _ _ _ _ (hR x).ne' (he1 x) (he2 x) (he4 x)]
        dsimp [G]
        ring
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 7 f).mpr
  refine ⟨q, 0, hq, ?_⟩
  intro x
  simp only [zero_add]
  rw [hid, mul_pos_iff_of_pos_left (pow_pos ht 2)]
  apply (hsign (.inl x)).trans
  change (0 < G 0 x) ↔ f x = true
  rw [hG0, div_pos_iff_of_pos_right (pow_pos (hR x) 3),
    mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
  exact hf x

end
end HeadComplexity.ThreeFractionsSevenHeads

namespace HeadComplexity

open scoped BigOperators
open RoPETwoHead

/-- Arbitrary positive-denominator affine fractions, including all retained
and pure rotary atoms, admit a seven-head vanilla classifier at head count three. -/
theorem vanilla_seven_of_positiveFraction_three {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : positiveFractionComputable n 3 f) :
    computableWithSharedHeadsN n 7 f := by
  classical
  obtain ⟨q, c, hq, hsign⟩ := hf
  let S (x : Fin n → Bool) := c + ∑ h, (q h).eval x
  have hS (x) : 0 < S x ↔ f x = true := hsign x
  obtain ⟨δ, hδ, hsmall⟩ := RoPETwoHead.exists_positive_shift S f hS
  let D (h : Fin 3) := denominator (q h)
  let U : Fin 3 → Form n :=
    ![(numerator (q 0)).lin (D 0) 1 (c - δ), numerator (q 1), numerator (q 2)]
  have hp (h : Fin 3) (x) : 0 < (D h).eval x := hq h x
  have heval (h : Fin 3) (x) :
      (q h).eval x = (numerator (q h)).eval x / (D h).eval x := rfl
  have hid (x) : ThreeFractionsSevenHeads.cubic U D x =
      (D 0).eval x * (D 1).eval x * (D 2).eval x * (S x - δ) := by
    have h0 := (hp 0 x).ne'
    have h1 := (hp 1 x).ne'
    have h2 := (hp 2 x).ne'
    simp [ThreeFractionsSevenHeads.cubic, U, Form.lin_eval, S, Fin.sum_univ_succ, heval]
    field_simp [h0, h1, h2]
    ring
  apply ThreeFractionsSevenHeads.computable_seven U D f
  · intro x
    rw [hid]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (hp 0 x).ne' (hp 1 x).ne') (hp 2 x).ne')
    cases hx : f x
    · have hnon : S x ≤ 0 := le_of_not_gt (by simpa [hx] using hS x)
      linarith
    · have := hsmall x hx
      linarith
  · intro x
    rw [hid, mul_pos_iff_of_pos_left (mul_pos (mul_pos (hp 0 x) (hp 1 x)) (hp 2 x))]
    constructor
    · intro h
      apply (hS x).mp
      linarith
    · intro h
      exact sub_pos.mpr (hsmall x h)

theorem vanilla_seven_of_retainedRoPE_three {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : retainedRoPEComputable n 3 f) :
    computableWithSharedHeadsN n 7 f :=
  vanilla_seven_of_positiveFraction_three (positiveFractionComputable_of_retained hf)

theorem vanilla_seven_of_pureRoPE_three {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n 3 f) :
    computableWithSharedHeadsN n 7 f :=
  vanilla_seven_of_retainedRoPE_three (retainedRoPEComputable_of_pure hf)

end HeadComplexity
