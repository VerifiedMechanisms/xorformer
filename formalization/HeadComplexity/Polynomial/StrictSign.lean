import HeadComplexity.Polynomial.ModelToPolynomial

set_option linter.style.header false

/-!
# Strict sign representations on the Boolean cube

`SignRepresents` uses the classifier convention `0 < P(x)` exactly on true
inputs, so its values on false inputs are only known to be nonpositive.  On the
finite Boolean cube a small downward shift makes both sides strict without
increasing total degree.  This neutral module packages that reusable margin
argument for polynomial transformations which need sign negation or
multiplication.
-/

namespace HeadComplexity

open MvPolynomial

variable {n : ℕ}

/-- A polynomial is positive on true inputs and negative on false inputs. -/
def StrictSignRep (P : MvPolynomial (Fin n) ℝ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, (f x = true → 0 < eval (cubePoint x) P) ∧
    (f x = false → eval (cubePoint x) P < 0)

/-- At a false point, a polynomial using the repository's weak-negative
classifier convention evaluates to a nonpositive number. -/
private theorem eval_nonpos_of_false
    {P : MvPolynomial (Fin n) ℝ} {f : (Fin n → Bool) → Bool}
    (hP : ∀ x, (0 < eval (cubePoint x) P ↔ f x = true))
    {x : Fin n → Bool} (hx : f x = false) :
    eval (cubePoint x) P ≤ 0 := by
  by_contra h
  push Not at h
  have := (hP x).mp h
  rw [hx] at this
  exact Bool.false_ne_true this

/-- A threshold-degree certificate can be made strict on both Boolean classes
by a constant shift, without increasing its degree. -/
theorem exists_strictSignRep_of_ThresholdDegLE
    {f : (Fin n → Bool) → Bool} {H : ℕ}
    (h : ThresholdDegLE f H) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ H ∧ StrictSignRep P f := by
  classical
  obtain ⟨P, hPdeg, hPsign⟩ := h
  set T : Finset (Fin n → Bool) := Finset.univ.filter (fun x ↦ f x = true) with hT
  obtain ⟨ε, hεpos, hεlt⟩ :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ x, f x = true → ε < eval (cubePoint x) P := by
    by_cases hTne : T.Nonempty
    · refine ⟨T.inf' hTne (fun x ↦ eval (cubePoint x) P) / 2, ?_, ?_⟩
      · apply half_pos
        rw [Finset.lt_inf'_iff]
        intro x hx
        rw [hT, Finset.mem_filter] at hx
        exact (hPsign x).mpr hx.2
      · intro x hx
        have hxT : x ∈ T := by
          rw [hT, Finset.mem_filter]
          exact ⟨Finset.mem_univ x, hx⟩
        have hle := Finset.inf'_le (fun x ↦ eval (cubePoint x) P) hxT
        have hpos : 0 < eval (cubePoint x) P := (hPsign x).mpr hx
        have : 0 < T.inf' hTne (fun x ↦ eval (cubePoint x) P) := by
          rw [Finset.lt_inf'_iff]
          intro y hy
          rw [hT, Finset.mem_filter] at hy
          exact (hPsign y).mpr hy.2
        linarith
    · refine ⟨1, one_pos, ?_⟩
      intro x hx
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
        (by rw [← hT]; exact fun hm ↦ hTne ⟨x, hm⟩)
  refine ⟨P - C ε, ?_, ?_⟩
  · exact (totalDegree_sub _ _).trans
      (by rw [totalDegree_C]; exact max_le hPdeg (Nat.zero_le _))
  · intro x
    have hev : eval (cubePoint x) (P - C ε) =
        eval (cubePoint x) P - ε := by
      rw [map_sub, eval_C]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rw [hev]
      linarith [hεlt x hx]
    · rw [hev]
      linarith [eval_nonpos_of_false hPsign hx]

end HeadComplexity
