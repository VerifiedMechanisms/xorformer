/-!
# Swap exclusion in the tropical (dominance) sub-model

Self-contained (core Lean 4 only, no Mathlib), checkable with a bare `lean` call.  It formalizes Lemma A of
`notes/wn_order_notes.md`, Section 21, for the tropical sub-model of theorem 199.

A rule `r` has a forced-one coordinate `pos r`, forced-zero coordinates `zeros r`, and a priority `pr r`.
It is *available* at `x : Fin n → Bool` if `x (pos r) = true` and `x j = false` for every forced-zero `j`.
`top x` is the available rule of highest priority.  Parity validity: adjacent points have different `top`
(fibers are independent sets).  Lemma: two points at swap distance never share their `top`.
-/

namespace Tropical

/-- Set coordinate `a` of `x` to `v`. -/
def upd {n : Nat} (x : Fin n → Bool) (a : Fin n) (v : Bool) : Fin n → Bool :=
  fun j => if j = a then v else x j

theorem upd_same {n : Nat} (x : Fin n → Bool) (a : Fin n) (v : Bool) : upd x a v a = v := by
  simp [upd]

theorem upd_other {n : Nat} (x : Fin n → Bool) (a j : Fin n) (v : Bool) (h : j ≠ a) :
    upd x a v j = x j := by
  simp [upd, h]

/-- A tropical representation. -/
structure Model (n : Nat) (R : Type) where
  pos : R → Fin n
  zeros : R → Fin n → Bool
  pr : R → Nat
  pr_inj : ∀ r s, pr r = pr s → r = s
  top : (Fin n → Bool) → R
  top_avail : ∀ x, x (pos (top x)) = true ∧ ∀ j, zeros (top x) j = true → x j = false
  top_max : ∀ x r, (x (pos r) = true ∧ ∀ j, zeros r j = true → x j = false) → pr r ≤ pr (top x)

namespace Model

variable {n : Nat} {R : Type} (M : Model n R)

/-- Availability of a rule at a point. -/
def avail (r : R) (x : Fin n → Bool) : Prop :=
  x (M.pos r) = true ∧ ∀ j, M.zeros r j = true → x j = false

/-- Parity hypothesis: switching on a zero coordinate changes the finalizing rule. -/
def ParityValid : Prop :=
  ∀ (x : Fin n → Bool) (a : Fin n), x a = false → M.top (upd x a true) ≠ M.top x

/-- If `x a = false`, `top x` is available at `upd x a true`, and the model is parity-valid, then the
forced-one coordinate of `top (upd x a true)` is `a`. -/
theorem pos_top_upd (hpv : M.ParityValid) (x : Fin n → Bool) (a : Fin n) (hxa : x a = false)
    (hav : M.avail (M.top x) (upd x a true)) : M.pos (M.top (upd x a true)) = a := by
  have hne : M.top (upd x a true) ≠ M.top x := hpv x a hxa
  have hle : M.pr (M.top x) ≤ M.pr (M.top (upd x a true)) := M.top_max (upd x a true) (M.top x) hav
  have hlt : M.pr (M.top x) < M.pr (M.top (upd x a true)) := by
    cases Nat.lt_or_eq_of_le hle with
    | inl h => exact h
    | inr h => exact absurd (M.pr_inj _ _ h.symm) hne
  have hnot : ¬ M.avail (M.top (upd x a true)) x := by
    intro hx
    have h2 := M.top_max x (M.top (upd x a true)) hx
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h2)
  have hyav := M.top_avail (upd x a true)
  apply Classical.byContradiction
  intro hpos
  apply hnot
  refine ⟨?_, ?_⟩
  · have h1 : upd x a true (M.pos (M.top (upd x a true))) = true := hyav.1
    have h2 : upd x a true (M.pos (M.top (upd x a true))) = x (M.pos (M.top (upd x a true))) :=
      upd_other x a _ true hpos
    rw [← h2]; exact h1
  · intro j hj
    have h1 : upd x a true j = false := hyav.2 j hj
    by_cases hja : j = a
    · subst hja
      have h3 : upd x j true j = true := upd_same x j true
      rw [h3] at h1; cases h1
    · have h2 : upd x a true j = x j := upd_other x a j true hja
      rw [← h2]; exact h1

/-- Lemma A (swap exclusion). -/
theorem swap_exclusion (hpv : M.ParityValid) (x : Fin n → Bool) (a b : Fin n) (hab : a ≠ b)
    (hxa : x a = false) (hxb : x b = true) :
    M.top (upd (upd x a true) b false) ≠ M.top x := by
  intro heq
  -- the point y := upd x a true equals upd x' b true where x' := upd (upd x a true) b false
  have hy' : upd (upd (upd x a true) b false) b true = upd x a true := by
    funext j
    by_cases hjb : j = b
    · subst hjb
      rw [upd_same]
      have h3 : upd x a true j = x j := upd_other x a j true (fun h => hab h.symm)
      rw [h3]; exact hxb.symm
    · rw [upd_other _ _ _ _ hjb, upd_other _ _ _ _ hjb]
  have hρx := M.top_avail x
  have hρx' : M.avail (M.top x) (upd (upd x a true) b false) := by
    have h := M.top_avail (upd (upd x a true) b false)
    rw [heq] at h
    exact h
  have hpos_ne_a : M.pos (M.top x) ≠ a := by
    intro h
    have h1 := hρx.1
    rw [h, hxa] at h1
    cases h1
  have hzero_a : M.zeros (M.top x) a = false := by
    cases hz : M.zeros (M.top x) a with
    | false => rfl
    | true =>
      exfalso
      have h1 := hρx'.2 a hz
      have h2 : upd (upd x a true) b false a = true := by
        rw [upd_other _ _ _ _ hab, upd_same]
      rw [h2] at h1
      cases h1
  have hρy : M.avail (M.top x) (upd x a true) := by
    refine ⟨?_, ?_⟩
    · have h2 := upd_other x a (M.pos (M.top x)) true hpos_ne_a
      rw [h2]; exact hρx.1
    · intro j hj
      by_cases hja : j = a
      · subst hja; rw [hzero_a] at hj; cases hj
      · rw [upd_other _ _ _ _ hja]; exact hρx.2 j hj
  have h1 : M.pos (M.top (upd x a true)) = a := M.pos_top_upd hpv x a hxa hρy
  have hx'b : upd (upd x a true) b false b = false := upd_same _ b false
  have hρy' : M.avail (M.top (upd (upd x a true) b false)) (upd (upd (upd x a true) b false) b true) := by
    rw [hy', heq]; exact hρy
  have h2 : M.pos (M.top (upd (upd (upd x a true) b false) b true)) = b :=
    M.pos_top_upd hpv (upd (upd x a true) b false) b hx'b hρy'
  rw [hy'] at h2
  exact hab (h1.symm.trans h2)

end Model

end Tropical
