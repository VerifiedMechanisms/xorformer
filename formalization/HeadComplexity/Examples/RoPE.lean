import HeadComplexity.Results.RoPEComparison

set_option linter.style.header false

/-!
# A strict exact-score separation

This does NOT separate Boolean head complexity. Every threshold of the displayed
reciprocal score is an LTF, hence has vanilla complexity at most one.
-/

namespace HeadComplexity.RoPEExamples

open scoped BigOperators

/-- Its score is `1 / (5 + x₀ + x₁ - x₂)`. -/
noncomputable def mixedReciprocal : PureRoPEAtom 3 where
  a := ![1, 1, 2]
  b := ![2, 2, 1]
  γ := 1
  η := 1
  v₀ := 0
  v₁ := 0
  ha i := by fin_cases i <;> norm_num
  hb i := by fin_cases i <;> norm_num
  hγ := by norm_num

theorem mixedReciprocal_eval (x : Fin 3 → Bool) :
    mixedReciprocal.eval x =
      1 / (5 + boolToReal (x 0) + boolToReal (x 1) - boolToReal (x 2)) := by
  rw [PureRoPEAtom.eval_eq]
  simp [mixedReciprocal, PureRoPEAtom.toAffineFraction, AffineFraction.eval,
    AffineFraction.numerator, AffineFraction.denominator, Fin.sum_univ_succ]
  ring

/-- No admissible vanilla ratio is this exact score on the eight vertices. -/
theorem mixedReciprocal_no_admissible_ratio (r : AffineFraction 3)
    (hr : r.Admissible) : ¬ (∀ x, r.eval x = mixedReciprocal.eval x) := by
  intro he
  have hc (x : Fin 3 → Bool) :
      r.numerator x * mixedReciprocal.toAffineFraction.denominator x =
        mixedReciprocal.toAffineFraction.numerator x * r.denominator x := by
    have h := (he x).trans (mixedReciprocal.eval_eq x)
    exact (div_eq_div_iff (hr.1 x).ne' (mixedReciprocal.denominator_pos x).ne').mp h
  have h000 := hc ![false, false, false]
  have h100 := hc ![true, false, false]
  have h010 := hc ![false, true, false]
  have h001 := hc ![false, false, true]
  have h110 := hc ![true, true, false]
  have h101 := hc ![true, false, true]
  have h011 := hc ![false, true, true]
  norm_num [mixedReciprocal, PureRoPEAtom.toAffineFraction, AffineFraction.numerator,
    AffineFraction.denominator, Fin.sum_univ_succ, boolToReal] at h000 h100 h010 h001 h110 h101 h011
  have hA0 : r.A 0 = 0 := by linarith
  have hA1 : r.A 1 = 0 := by linarith
  have hA2 : r.A 2 = 0 := by linarith
  have hC0 : r.C 0 = r.b := by linarith
  have hC2 : r.C 2 = -r.b := by linarith
  have hd := hr.1 ![false, false, false]
  norm_num [AffineFraction.denominator, Fin.sum_univ_succ, boolToReal] at hd
  have hb : 0 < r.b := by linarith
  rcases hr.2.1 with hpos | hneg | hzero
  · have := hpos 2
    linarith
  · have := hneg 0
    linarith
  · have := hzero 0
    linarith

/-- Adding a free readout constant does not remove the exact-score obstruction. -/
theorem mixedReciprocal_no_admissible_score (r : AffineFraction 3)
    (hr : r.Admissible) (c : ℝ) :
    ¬ (∀ x, c + r.eval x = mixedReciprocal.eval x) := by
  intro he
  let s : AffineFraction 3 := {
    A := fun i ↦ c * r.C i + r.A i
    b := c * r.d + r.b
    C := r.C
    d := r.d }
  have hs : s.Admissible := by
    refine ⟨hr.1, hr.2.1, ?_⟩
    intro hz
    have hzero : ∀ i, r.C i = 0 := hz
    simpa [s, hzero] using hr.2.2 hzero
  apply mixedReciprocal_no_admissible_ratio s hs
  intro x
  have hn : s.numerator x = c * r.denominator x + r.numerator x := by
    simp only [s, AffineFraction.numerator, AffineFraction.denominator]
    simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hx : s.eval x = c + r.eval x := by
    change s.numerator x / r.denominator x = c + r.numerator x / r.denominator x
    rw [hn]
    have hd := (hr.1 x).ne'
    field_simp
  exact hx.trans (he x)

open scoped InnerProductSpace in
/-- The obstruction for the existing literal shared-embedding vanilla model. -/
theorem mixedReciprocal_no_vanilla_one_head_score :
    ¬ (∃ d, ∃ M : SharedHeadFamily 3 d 1, ∃ (w : Vec d) (τ : ℝ),
      ∀ x, ⟪w, M.attnUpdate x⟫_ℝ - τ = mixedReciprocal.eval x) := by
  intro h
  obtain ⟨r, c, hr, he⟩ :=
    (shared_score_iff_affineFraction 1 mixedReciprocal.eval).mp h
  apply mixedReciprocal_no_admissible_score (r 0) (hr 0) c
  simpa using he

end HeadComplexity.RoPEExamples
