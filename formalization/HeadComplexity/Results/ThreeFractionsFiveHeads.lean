import HeadComplexity.Results.ThreeFractionsSevenHeads

set_option linter.style.header false

/-! # Five vanilla heads when two original denominators span an oriented base -/

namespace HeadComplexity.ThreeFractionsFiveHeads
noncomputable section
open scoped BigOperators Topology
open RoPETwoHead ThreeFractionsSevenHeads
variable {n : ℕ}

def normalizedFirst (r b t : ℝ) : ℝ := b / (r * (r + t * b))

theorem first_difference (r b t : ℝ) (hr : r ≠ 0) (hb : r + t * b ≠ 0) :
    1 / r - 1 / (r + t * b) = t * normalizedFirst r b t := by
  unfold normalizedFirst
  field_simp
  ring

theorem normalizedFirst_zero (r b : ℝ) (_hr : r ≠ 0) :
    normalizedFirst r b 0 = b / r ^ 2 := by
  simp [normalizedFirst, pow_two]

theorem normalizedFirst_continuous (r b : ℝ) (hr : r ≠ 0) :
    ContinuousAt (normalizedFirst r b) 0 := by
  unfold normalizedFirst
  fun_prop (disch := simpa using hr)

/-- All numerator forms are unrestricted. The oriented base may have either
strict common slope sign, independently of the original denominators. -/
theorem computable_five (U D : Fin 3 → Form n) (R : Form n) (κ : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hR : ∀ x, 0 < R.eval x)
    (hRv : (∀ i, 0 < R.v i) ∨ (∀ i, R.v i < 0))
    (hrelation : ∀ x, R.eval x = κ * (D 0).eval x - (D 1).eval x)
    (hne : ∀ x, cubic U D x ≠ 0)
    (hf : ∀ x, (0 < cubic U D x) ↔ f x = true) :
    computableWithSharedHeadsN n 5 f := by
  classical
  obtain ⟨s, hs, hsr⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i, 0 < s * R.v i := by
    rcases hRv with hp | hn
    · exact ⟨1, Or.inl rfl, by simpa using hp⟩
    · exact ⟨-1, Or.inr rfl, fun i ↦ by simpa using neg_pos.mpr (hn i)⟩
  let E (t : ℝ) : Fin 5 → Form n :=
    ![R, R.lin (D 0) 1 t, R.lin (D 0) 1 (2*t), R.lin (D 2) 1 t,
      R.lin ((D 0).lin (D 2) 1 1) 1 t]
  have hE0 (h : Fin 5) : E 0 h = R := by
    fin_cases h <;> ext <;> simp [E, Form.lin]
  let G (t : ℝ) (x : Fin n → Bool) :=
    κ * (U 2).eval x * normalizedSecond (R.eval x) ((D 0).eval x) ((D 0).eval x) t +
      (κ * (U 0).eval x + (U 1).eval x) *
        normalizedSecond (R.eval x) ((D 0).eval x) ((D 2).eval x) t -
      2 * (U 0).eval x * normalizedFirst (R.eval x) ((D 2).eval x) t -
      2 * (U 2).eval x * normalizedFirst (R.eval x) ((D 0).eval x) t
  have hG0 (x) : G 0 x = 2 * cubic U D x / (R.eval x)^3 := by
    simp only [G, normalizedSecond_zero _ _ _ (hR x).ne',
      normalizedFirst_zero _ _ (hR x).ne', cubic]
    have hr := (hR x).ne'
    field_simp
    rw [hrelation]
    ring
  let F (t : ℝ) : ((Fin n → Bool) ⊕ ((Fin 5 × (Fin n → Bool)) ⊕ (Fin 5 × Fin n))) → ℝ
    | .inl x => G t x
    | .inr (.inl hx) => (E t hx.1).eval hx.2
    | .inr (.inr hi) => s * (E t hi.1).v hi.2
  obtain ⟨t, ht, hsign⟩ := TwoProductsThreeHeads.exists_positive_preserving F (by
    intro i
    rcases i with x | (⟨h, x⟩ | ⟨h, i⟩)
    · change ContinuousAt (fun t ↦ G t x) 0
      exact (((continuousAt_const.mul (normalizedSecond_continuous _ _ _ (hR x).ne')).add
        (continuousAt_const.mul (normalizedSecond_continuous _ _ _ (hR x).ne'))).sub
          (continuousAt_const.mul (normalizedFirst_continuous _ _ (hR x).ne'))).sub
          (continuousAt_const.mul (normalizedFirst_continuous _ _ (hR x).ne'))
    · change ContinuousAt (fun t ↦ (E t h).eval x) 0
      fin_cases h <;> dsimp [E, Form.lin, Form.eval] <;> fun_prop
    · change ContinuousAt (fun t ↦ s * (E t h).v i) 0
      fin_cases h <;> dsimp [E, Form.lin] <;> fun_prop) (by
    intro i
    rcases i with x | (⟨h, x⟩ | ⟨h, i⟩)
    · change G 0 x ≠ 0
      rw [hG0]
      exact div_ne_zero (mul_ne_zero (by norm_num) (hne x)) (pow_ne_zero _ (hR x).ne')
    · simpa only [F, hE0] using (hR x).ne'
    · simpa only [F, hE0] using (hsr i).ne')
  have hp (h : Fin 5) (x) : 0 < (E t h).eval x := by
    apply (hsign (.inr (.inl (h, x)))).mpr
    simpa only [F, hE0] using hR x
  have hv (h : Fin 5) (i) : 0 < s * (E t h).v i := by
    apply (hsign (.inr (.inr (h, i)))).mpr
    simpa only [F, hE0] using hsr i
  let N : Fin 5 → Form n :=
    ![((U 0).lin (U 1) (κ-2*t) 1).lin (U 2) 1 (κ-2*t),
      ((U 0).lin (U 1) (-κ) (-1)).lin (U 2) 1 (-2*κ+2*t),
      (U 2).lin (U 2) κ 0,
      (U 0).lin (U 1) (-κ+2*t) (-1),
      (U 0).lin (U 1) κ 1]
  let q (h : Fin 5) := fraction (N h) (E t h)
  have hq (h : Fin 5) : (q h).Admissible := by
    apply fraction_admissible _ _ (hp h)
    rcases hs with he | he
    · exact Or.inl (fun i ↦ by simpa [he] using hv h i)
    · exact Or.inr (fun i ↦ neg_pos.mp (by simpa [he] using hv h i))
  have he1 (x) : R.eval x + t * (D 0).eval x ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 1 x).ne'
  have he2 (x) : R.eval x + t * ((D 0).eval x + (D 0).eval x) ≠ 0 := by
    convert (hp 2 x).ne' using 1
    simp [E, Form.lin_eval]
    ring
  have he3 (x) : R.eval x + t * (D 2).eval x ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 3 x).ne'
  have he4 (x) : R.eval x + t * ((D 0).eval x + (D 2).eval x) ≠ 0 := by
    simpa [E, Form.lin_eval] using (hp 4 x).ne'
  have hid (x) : (∑ h, (q h).eval x) = t^2 * G t x := by
    calc
      _ = κ * (U 2).eval x * (1 / R.eval x - 1 / (R.eval x + t * (D 0).eval x) -
          1 / (R.eval x + t * (D 0).eval x) +
          1 / (R.eval x + t * ((D 0).eval x + (D 0).eval x))) +
        (κ * (U 0).eval x + (U 1).eval x) *
          (1 / R.eval x - 1 / (R.eval x + t * (D 0).eval x) -
          1 / (R.eval x + t * (D 2).eval x) +
          1 / (R.eval x + t * ((D 0).eval x + (D 2).eval x))) -
        2*t*(U 0).eval x*(1 / R.eval x - 1 / (R.eval x + t * (D 2).eval x)) -
        2*t*(U 2).eval x*(1 / R.eval x - 1 / (R.eval x + t * (D 0).eval x)) := by
          simp [q, N, E, Fin.sum_univ_succ, fraction_eval, Form.lin_eval, div_eq_mul_inv]
          ring
      _ = _ := by
        rw [second_difference _ _ _ _ (hR x).ne' (he1 x) (he1 x) (he2 x),
          second_difference _ _ _ _ (hR x).ne' (he1 x) (he3 x) (he4 x),
          first_difference _ _ _ (hR x).ne' (he3 x),
          first_difference _ _ _ (hR x).ne' (he1 x)]
        dsimp [G]
        ring
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 5 f).mpr
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
end HeadComplexity.ThreeFractionsFiveHeads
