import HeadComplexity.Examples.RoPE

set_option linter.style.header false

/-!
# A uniform-score approximation obstruction

The mixed reciprocal already separates exact one-head scores. Here its
separation is quantitative: it cannot even be uniformly approximated by one
vanilla score to arbitrarily small error. Its Boolean thresholds remain LTFs.
This result only rules out a score-approximation route to the Boolean theorem.
-/

namespace HeadComplexity.RoPEExamples

open scoped BigOperators

theorem mixedReciprocal_no_close_admissible_ratio (r : AffineFraction 3)
    (hr : r.Admissible) :
    ¬ (∀ x, |r.eval x - mixedReciprocal.eval x| < (1 : ℝ) / 100000) := by
  intro he
  have hc (x : Fin 3 → Bool) :
      (mixedReciprocal.eval x - 1 / 100000) * r.denominator x < r.numerator x ∧
      r.numerator x < (mixedReciprocal.eval x + 1 / 100000) * r.denominator x := by
    have h := abs_lt.mp (he x)
    constructor
    · apply (lt_div_iff₀ (hr.1 x)).mp
      change mixedReciprocal.eval x - 1 / 100000 < r.eval x
      linarith
    · apply (div_lt_iff₀ (hr.1 x)).mp
      change r.eval x < mixedReciprocal.eval x + 1 / 100000
      linarith
  have h000 := hc ![false, false, false]
  have h100 := hc ![true, false, false]
  have h010 := hc ![false, true, false]
  have h001 := hc ![false, false, true]
  have h110 := hc ![true, true, false]
  have h101 := hc ![true, false, true]
  have h011 := hc ![false, true, true]
  norm_num [mixedReciprocal_eval, AffineFraction.numerator,
    AffineFraction.denominator, Fin.sum_univ_succ, boolToReal] at h000 h100 h010 h001 h110 h101 h011
  dsimp at h000 h100 h010 h001 h110 h101 h011
  norm_num at h000 h100 h010 h001 h110 h101 h011
  have hd := hr.1 ![false, false, false]
  norm_num [AffineFraction.denominator, Fin.sum_univ_succ, boolToReal] at hd
  rcases hr.2.1 with hp | hn | hz
  · have hp0 := hp 0
    have hp1 := hp 1
    have hp2 := hp 2
    linarith
  · have hn0 := hn 0
    have hn1 := hn 1
    have hn2 := hn 2
    linarith
  · have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    linarith

/-- A free affine readout constant does not remove the positive approximation
gap. The denominator orientation is unchanged when the constant is absorbed. -/
theorem mixedReciprocal_no_close_admissible_score (r : AffineFraction 3)
    (hr : r.Admissible) (c : ℝ) :
    ¬ (∀ x, |c + r.eval x - mixedReciprocal.eval x| < (1 : ℝ) / 100000) := by
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
  have hse (x : Fin 3 → Bool) : s.eval x = c + r.eval x := by
    have hn : s.numerator x = c * r.denominator x + r.numerator x := by
      simp only [s, AffineFraction.numerator, AffineFraction.denominator]
      simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    change s.numerator x / r.denominator x = c + r.numerator x / r.denominator x
    rw [hn]
    have hd := (hr.1 x).ne'
    field_simp
  apply mixedReciprocal_no_close_admissible_ratio s hs
  simpa only [hse] using he

open scoped InnerProductSpace in
/-- The score gap holds for the existing shared-embedding vanilla architecture,
at every finite width. It is not a Boolean head-count separation. -/
theorem mixedReciprocal_no_close_vanilla_one_head_score :
    ¬ (∃ d, ∃ M : SharedHeadFamily 3 d 1, ∃ (w : Vec d) (τ : ℝ),
      ∀ x, |(⟪w, M.attnUpdate x⟫_ℝ - τ) - mixedReciprocal.eval x| <
        (1 : ℝ) / 100000) := by
  rintro ⟨d, M, w, τ, he⟩
  obtain ⟨r, c, hr, hs⟩ :=
    (shared_score_iff_affineFraction 1 (fun x ↦ ⟪w, M.attnUpdate x⟫_ℝ - τ)).mp
      ⟨d, M, w, τ, fun _ ↦ rfl⟩
  apply mixedReciprocal_no_close_admissible_score (r 0) (hr 0) c
  intro x
  have hx : c + (r 0).eval x = ⟪w, M.attnUpdate x⟫_ℝ - τ := by
    simpa using hs x
  simpa only [hx] using he x

end HeadComplexity.RoPEExamples
