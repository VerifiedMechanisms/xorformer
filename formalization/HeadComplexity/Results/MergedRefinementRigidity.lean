import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- A finite descending two-branch system has no nonzero function with zero
terminal data and opposite increments along its two branches. -/
theorem two_branch_boundary_rigidity {V : Type*}
    (active : V → Prop) (height : V → ℕ) (left right : V → V)
    (g t : V → ℝ)
    (hleft : ∀ v, active v → height (left v) < height v)
    (hright : ∀ v, active v → height (right v) < height v)
    (hplus : ∀ v, active v → g (left v) = g v + t v)
    (hminus : ∀ v, active v → g (right v) = g v - t v)
    (hterminal : ∀ v, ¬active v → g v = 0) :
    (∀ v, g v = 0) ∧ (∀ v, active v → t v = 0) := by
  classical
  have hz : ∀ m, ∀ v, height v = m → g v = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v hv
      by_cases ha : active v
      · have hl : g (left v) = 0 :=
          ih (height (left v)) (by simpa [hv] using hleft v ha) (left v) rfl
        have hr : g (right v) = 0 :=
          ih (height (right v)) (by simpa [hv] using hright v ha) (right v) rfl
        have hp := hplus v ha
        have hm := hminus v ha
        linarith
      · exact hterminal v ha
  have hall : ∀ v, g v = 0 := fun v ↦ hz (height v) v rfl
  refine ⟨hall, ?_⟩
  intro v hv
  have hp := hplus v hv
  rw [hall, hall] at hp
  linarith

/-- Different fixed branch rates also force zero interior data and zero steps
when the terminal data vanish. -/
theorem two_rate_boundary_rigidity {V : Type*}
    (active : V → Prop) (height : V → ℕ) (left right : V → V)
    (g t : V → ℝ) (a b : ℝ) (hab : a ≠ b)
    (hleft : ∀ v, active v → height (left v) < height v)
    (hright : ∀ v, active v → height (right v) < height v)
    (ha : ∀ v, active v → g (left v) = g v + a * t v)
    (hb : ∀ v, active v → g (right v) = g v + b * t v)
    (hterminal : ∀ v, ¬active v → g v = 0) :
    (∀ v, g v = 0) ∧ (∀ v, active v → t v = 0) := by
  classical
  have step : ∀ v, active v → g (left v) = 0 → g (right v) = 0 →
      g v = 0 ∧ t v = 0 := by
    intro v hv hl hr
    have h1 := ha v hv
    have h2 := hb v hv
    have ht : (a - b) * t v = 0 := by rw [hl] at h1; rw [hr] at h2; nlinarith
    have ht0 : t v = 0 := (mul_eq_zero.mp ht).resolve_left (sub_ne_zero.mpr hab)
    exact ⟨by rw [hl, ht0] at h1; linarith, ht0⟩
  have hz : ∀ m, ∀ v, height v = m → g v = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v hv
      by_cases hvactive : active v
      · exact (step v hvactive
          (ih (height (left v)) (by simpa [hv] using hleft v hvactive) (left v) rfl)
          (ih (height (right v)) (by simpa [hv] using hright v hvactive) (right v) rfl)).1
      · exact hterminal v hvactive
  have hall : ∀ v, g v = 0 := fun v ↦ hz (height v) v rfl
  exact ⟨hall, fun v hv ↦ (step v hv (hall (left v)) (hall (right v))).2⟩

/-- Following a descending branch that preserves a value reaches a terminal
with the same value. No finiteness assumption on the vertex type is needed. -/
theorem constant_branch_reaches_terminal {V α : Type*}
    (active : V → Prop) (height : V → ℕ) (child : V → V) (value : V → α)
    (hdesc : ∀ v, active v → height (child v) < height v)
    (hvalue : ∀ v, active v → value (child v) = value v) :
    ∀ v, ∃ w, ¬active w ∧ value w = value v := by
  classical
  have h : ∀ m, ∀ v, height v = m → ∃ w, ¬active w ∧ value w = value v := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v hv
      by_cases ha : active v
      · obtain ⟨w, hw, heq⟩ :=
          ih (height (child v)) (by simpa [hv] using hdesc v ha) (child v) rfl
        exact ⟨w, hw, heq.trans (hvalue v ha)⟩
      · exact ⟨v, ha, rfl⟩
  exact fun v ↦ h (height v) v rfl

/-- In a merged refinement graph, fixing one nontrivial coordinate difference
at every terminal forces all step variations to vanish. The remaining state
variations are equal across every edge. The parameter-dimension consequence
and the universal-sign counting argument are stated separately in the manual
note; this theorem does not assert a universal head bound. -/
theorem merged_refinement_boundary_rigidity {V ι : Type*} [DecidableEq ι]
    (active : V → Prop) (height : V → ℕ) (child : V → ι → V)
    (u : V → ι → ℝ) (t : V → ℝ) (a b : ι) (hab : a ≠ b)
    (hdesc : ∀ v, active v → ∀ i, height (child v i) < height v)
    (hedge : ∀ v, active v → ∀ i j,
      u (child v i) j = u v j + if j = i then t v else 0)
    (hterminal : ∀ v, ¬active v → u v a = u v b) :
    (∀ v, u v a = u v b) ∧ (∀ v, active v → t v = 0) ∧
      (∀ v, active v → ∀ i, u (child v i) = u v) := by
  classical
  have h := two_branch_boundary_rigidity active height
    (fun v ↦ child v a) (fun v ↦ child v b) (fun v ↦ u v a - u v b) t
    (fun v hv ↦ hdesc v hv a) (fun v hv ↦ hdesc v hv b)
    (by
      intro v hv
      rw [hedge v hv a a, hedge v hv a b]
      simp only [Ne.symm hab, ↓reduceIte, add_zero]
      ring)
    (by
      intro v hv
      rw [hedge v hv b a, hedge v hv b b]
      simp only [hab, ↓reduceIte, add_zero]
      ring)
    (by intro v hv; exact sub_eq_zero.mpr (hterminal v hv))
  refine ⟨fun v ↦ sub_eq_zero.mp (h.1 v), h.2, ?_⟩
  intro v hv i
  funext j
  rw [hedge v hv i j, h.2 v hv]
  simp

end HeadComplexity
