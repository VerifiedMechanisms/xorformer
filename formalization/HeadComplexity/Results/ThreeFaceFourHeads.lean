import HeadComplexity.Results.PureRoPETwoHeads

set_option linter.style.header false

/-!
# Four vanilla heads suffice for a union of three affine zero faces

The affine forms are nonnegative on the Boolean cube. Their zero sets include
arbitrary mixed-literal conjunctions. Four positive oriented denominators give
an exact reciprocal finite difference, with a finite strict threshold.
-/

namespace HeadComplexity
namespace ThreeFaceFourHeads

open scoped BigOperators
open RoPETwoHead

variable {n : ℕ}

/-- Exact mixed finite difference of the reciprocal function. -/
theorem reciprocal_difference (b u v : ℝ) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    1 / b - 1 / (b + u) - 1 / (b + v) + 1 / (b + u + v) =
      u * v * (2 * b + u + v) / (b * (b + u) * (b + v) * (b + u + v)) := by
  have hbu : b + u ≠ 0 := ne_of_gt (by linarith)
  have hbuv : b + u + v ≠ 0 := ne_of_gt (by linarith)
  have hbv : b + v ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The mixed reciprocal difference is positive exactly when both increments are. -/
theorem reciprocal_difference_pos_iff (b u v : ℝ)
    (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (0 < 1 / b - 1 / (b + u) - 1 / (b + v) + 1 / (b + u + v)) ↔
      0 < u ∧ 0 < v := by
  rw [reciprocal_difference b u v hb hu hv]
  have hd : 0 < b * (b + u) * (b + v) * (b + u + v) := by positivity
  have ht : 0 < 2 * b + u + v := by positivity
  rw [div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_right ht]
  rw [mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact h
    · linarith [h.1]
  · exact Or.inl

/-- No restriction on literal orientation or affine numerator signs is used. -/
theorem computable_four (d : Fin 3 → Form n) (f : (Fin n → Bool) → Bool)
    (hd : ∀ h x, 0 ≤ (d h).eval x)
    (hf : ∀ x, f x = true ↔ ∃ h, (d h).eval x = 0) :
    computableWithSharedHeadsN n 4 f := by
  classical
  let b : Form n := ⟨1, fun i ↦ 1 + |(d 0).v i| + |(d 1).v i|⟩
  have hb (x) : 0 < b.eval x := by
    apply add_pos_of_pos_of_nonneg one_pos
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by dsimp [b]; positivity) (by cases x i <;> simp [boolToReal])
  let e : Fin 4 → Form n :=
    ![b, b.lin (d 0) 1 1, b.lin (d 1) 1 1, (b.lin (d 0) 1 1).lin (d 1) 1 1]
  have he (h : Fin 4) (x) : 0 < (e h).eval x := by
    fin_cases h <;> norm_num [e, Form.lin_eval]
    · exact hb x
    · linarith [hb x, hd 0 x]
    · linarith [hb x, hd 1 x]
    · linarith [hb x, hd 0 x, hd 1 x]
  have hev (h : Fin 4) (i) : 0 < (e h).v i := by
    have ha := neg_le_abs ((d 0).v i)
    have hc := neg_le_abs ((d 1).v i)
    have haa := abs_nonneg ((d 0).v i)
    have hcc := abs_nonneg ((d 1).v i)
    fin_cases h <;> norm_num [e, Form.lin, b] <;> linarith
  let a := (d 2).lin (d 2) (-1) 0
  let r : Fin 4 → AffineFraction n :=
    ![fraction a (e 0), fraction (d 2) (e 1), fraction (d 2) (e 2), fraction a (e 3)]
  have hr (h : Fin 4) : (r h).Admissible := by
    fin_cases h <;> dsimp [r]
    · exact fraction_admissible _ _ (he 0) (Or.inl (hev 0))
    · exact fraction_admissible _ _ (he 1) (Or.inl (hev 1))
    · exact fraction_admissible _ _ (he 2) (Or.inl (hev 2))
    · exact fraction_admissible _ _ (he 3) (Or.inl (hev 3))
  let G (x : Fin n → Bool) := (d 2).eval x *
    (1 / b.eval x - 1 / (b.eval x + (d 0).eval x) -
      1 / (b.eval x + (d 1).eval x) + 1 / (b.eval x + (d 0).eval x + (d 1).eval x))
  have hG (x) : 0 < G x ↔ f x = false := by
    have hdiff : 0 ≤ 1 / b.eval x - 1 / (b.eval x + (d 0).eval x) -
        1 / (b.eval x + (d 1).eval x) +
          1 / (b.eval x + (d 0).eval x + (d 1).eval x) := by
      rw [reciprocal_difference _ _ _ (hb x) (hd 0 x) (hd 1 x)]
      have h0 := hd 0 x
      have h1 := hd 1 x
      have hb0 := hb x
      positivity
    dsimp [G]
    have hmul : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (0 < u * v ↔ 0 < u ∧ 0 < v) := by
      intro u v hu hv
      rw [mul_pos_iff]
      constructor
      · rintro (h | h)
        · exact h
        · linarith [h.1]
      · exact Or.inl
    rw [hmul _ _ (hd 2 x) hdiff,
      reciprocal_difference_pos_iff _ _ _ (hb x) (hd 0 x) (hd 1 x)]
    have heq : f x = false ↔ ¬ (∃ h, (d h).eval x = 0) := by
      rw [← hf x]
      exact Bool.eq_false_iff
    rw [heq, not_exists]
    constructor
    · rintro ⟨h2, h0, h1⟩ h
      fin_cases h
      · exact h0.ne'
      · exact h1.ne'
      · exact h2.ne'
    · intro h
      exact ⟨lt_of_le_of_ne (hd 2 x) (Ne.symm (h 2)),
        lt_of_le_of_ne (hd 0 x) (Ne.symm (h 0)),
        lt_of_le_of_ne (hd 1 x) (Ne.symm (h 1))⟩
  have hzero (x) (hx : f x = true) : G x = 0 := by
    obtain ⟨h, hh⟩ := (hf x).mp hx
    dsimp [G]
    rw [reciprocal_difference _ _ _ (hb x) (hd 0 x) (hd 1 x)]
    fin_cases h
    · change (d 0).eval x = 0 at hh
      simp [hh]
    · change (d 1).eval x = 0 at hh
      simp [hh]
    · change (d 2).eval x = 0 at hh
      simp [hh]
  obtain ⟨δ, hδ, hδG⟩ := exists_positive_shift G (fun x ↦ !(f x)) (by
    intro x
    cases hx : f x <;> simpa [hx] using hG x)
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 4 f).mpr
  refine ⟨r, δ, hr, ?_⟩
  intro x
  have hsum : ∑ h, (r h).eval x = -G x := by
    simp [Fin.sum_univ_succ, r, fraction_eval, e, Form.lin_eval, a, G]
    ring
  rw [hsum]
  cases hx : f x
  · have hsmall := hδG x (by simp [hx])
    simp only [Bool.false_eq_true, iff_false]
    linarith
  · rw [hzero x hx]
    simpa using hδ

end ThreeFaceFourHeads
end HeadComplexity
