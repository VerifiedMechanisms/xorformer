import HeadComplexity.Research.OriginalMarginCapacity

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-! Unit-gap extensions are controlled by the smaller contact-sign subspace.
In particular a single minority contact determines the entire truth table. -/
noncomputable section
namespace HeadComplexity.MinorityContactCapacity
open Finset MvPolynomial
open scoped BigOperators

variable {ι : Type} {k : ℕ}

theorem unit_gap_sign_iff (A B F : ι → ℝ) (f : ι → Bool)
    (hB : ∀ x, 0 < B x) (hA : ∀ x, A x = B x - F x)
    (hgap : ∀ x, if f x then B x ≤ A x else B x ≤ -A x) (x : ι) :
    f x = true ↔ F x ≤ 0 := by
  have hx := hgap x
  have hb := hB x
  have ha := hA x
  cases hf : f x <;> simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · constructor
    · intro h; cases h
    · intro h; linarith
  · constructor
    · intro _; linarith
    · intro _; trivial

theorem one_minority_sign_iff (A B F : ι → ℝ) (f : ι → Bool) (c : ℝ)
    (hc : 0 < c) (hB : ∀ x, 0 < B x)
    (hA : ∀ x, A x = B x - c * F x)
    (hgap : ∀ x, if f x then B x ≤ A x else B x ≤ -A x) (x : ι) :
    f x = true ↔ F x ≤ 0 := by
  rw [unit_gap_sign_iff A B (fun x => c * F x) f hB hA hgap x]
  constructor
  · intro h; nlinarith
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hc.le h

theorem one_minority_unique (A B A' B' F : ι → ℝ) (f g : ι → Bool)
    (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (hB : ∀ x, 0 < B x) (hB' : ∀ x, 0 < B' x)
    (hA : ∀ x, A x = B x - c * F x)
    (hA' : ∀ x, A' x = B' x - c' * F x)
    (hf : ∀ x, if f x then B x ≤ A x else B x ≤ -A x)
    (hg : ∀ x, if g x then B' x ≤ A' x else B' x ≤ -A' x) : f = g := by
  funext x
  have hh := (one_minority_sign_iff A B F f c hc hB hA hf x).trans
    (one_minority_sign_iff A' B' F g c' hc' hB' hA' hg x).symm
  cases hf' : f x <;> cases hg' : g x <;> simp_all


def comparisonPoly (L : Fin k → ι → ℝ) (x : ι) : MvPolynomial (Option (Fin k)) ℝ :=
  X none - ∑ j, C (L j x) * X (some j)

theorem comparisonPoly_totalDegree_le (L : Fin k → ι → ℝ) (x : ι) :
    (comparisonPoly L x).totalDegree ≤ 1 := by
  unfold comparisonPoly
  apply (totalDegree_sub _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

def unitFeasiblePatterns (L : Fin k → ι → ℝ) : Set (ι → Bool) :=
  {f | ∃ (c : Fin k → ℝ) (A B : ι → ℝ),
    (∀ x, 0 < B x) ∧ (∀ x, A x = B x - ∑ j, c j * L j x) ∧
    (∀ x, if f x then B x ≤ A x else B x ≤ -A x)}

theorem mem_comparison_of_unitFeasible [Finite ι] (L : Fin k → ι → ℝ) (f : ι → Bool)
    (hf : f ∈ unitFeasiblePatterns L) :
    f ∈ strictPolynomialSignPatterns (comparisonPoly L) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨c, A, B, hB, hA, hgap⟩ := hf
  let F (x : ι) := ∑ j, c j * L j x
  have hs (x : ι) : f x = true ↔ F x ≤ 0 :=
    unit_gap_sign_iff A B F f hB hA hgap x
  let gap (x : ι) : ℝ := if 0 < F x then F x else 1
  have hg (x : ι) : 0 < gap x := by
    dsimp [gap]
    split <;> positivity
  obtain ⟨ε, hε, hεgap⟩ := PolynomialRootCount.exists_pos_lt_finite gap hg
  let θ : Option (Fin k) → ℝ := fun v => Option.elim v ε c
  have he (x : ι) : eval θ (comparisonPoly L x) = ε - F x := by
    simp [comparisonPoly, θ, F, mul_comm]
  refine ⟨θ, fun x => ?_⟩
  rw [he]
  cases hfx : f x
  · have hp : 0 < F x := lt_of_not_ge (by intro h; simpa [hfx] using (hs x).mpr h)
    simpa [gap, hp] using sub_neg.mpr (hεgap x)
  · have hn := (hs x).mp hfx
    simpa using sub_pos.mpr (lt_of_le_of_lt hn hε)

theorem card_unitFeasiblePatterns_le [Fintype ι] (L : Fin k → ι → ℝ)
    (hparameters : k + 1 ≤ Fintype.card ι) :
    ((unitFeasiblePatterns L).ncard : ℝ) ≤
      (4 * Real.exp 1 * Fintype.card ι / (k + 1)) ^ (k + 1) := by
  have hp : Fintype.card (Option (Fin k)) = k + 1 := by simp
  have hc := warrenStrictSignPatternBound (Fintype.card ι) 1 (k + 1)
    (by omega) (by omega) hparameters ι (Option (Fin k))
    (comparisonPoly L) rfl hp (comparisonPoly_totalDegree_le L)
  have hm : (unitFeasiblePatterns L).ncard ≤
      (strictPolynomialSignPatterns (comparisonPoly L)).ncard :=
    Set.ncard_mono (fun f hf => mem_comparison_of_unitFeasible L f hf)
  have hmr : ((unitFeasiblePatterns L).ncard : ℝ) ≤
      ((strictPolynomialSignPatterns (comparisonPoly L)).ncard : ℝ) := by exact_mod_cast hm
  exact hmr.trans (by simpa using hc)

end HeadComplexity.MinorityContactCapacity
