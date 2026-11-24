import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Multilinear forms detected by distinct robustly spanning columns

This is the algebraic core of a low-degree Boolean-projection injectivity argument.
It does not assert an unrestricted capacity improvement.
-/

namespace HeadComplexity.RobustCubeProjection

open Submodule

variable {R E F : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
  [AddCommMonoid F] [Module R F]

/-- Columns avoiding a prescribed list. Repetition in the list is harmless. -/
def avoiding {ι : Type*} (v : ι → E) {k : ℕ} (j : Fin k → ι) : Set E :=
  {x | ∃ i, (∀ a, i ≠ j a) ∧ v i = x}

/-- A family stays spanning after deletion of any list of at most `d` columns. -/
def RobustSpanning {ι : Type*} (v : ι → E) (d : ℕ) : Prop :=
  ∀ k ≤ d, ∀ j : Fin k → ι, span R (avoiding v j) = ⊤

lemma span_range_eq_top {ι : Type*} {v : ι → E} {d : ℕ}
    (hv : RobustSpanning (R := R) v d) : span R (Set.range v) = ⊤ := by
  simpa [avoiding, Set.range] using hv 0 (Nat.zero_le _) Fin.elim0

lemma robustSpanning_delete {ι : Type*} {v : ι → E} {d : ℕ}
    (hv : RobustSpanning (R := R) v (d + 1)) (i : ι) :
    RobustSpanning (R := R) (fun a : {a : ι // a ≠ i} => v a) d := by
  intro k hk j
  have h := hv (k + 1) (Nat.add_le_add_right hk 1)
    (Fin.cons i (fun a => (j a).val))
  convert h using 1
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.val, ?_, rfl⟩
    intro b
    refine Fin.cases a.property (fun b => ?_) b
    intro he
    exact ha b (Subtype.ext he)
  · rintro ⟨a, ha, hax⟩
    refine ⟨⟨a, ha 0⟩, ?_, hax⟩
    intro b he
    exact ha b.succ (congrArg Subtype.val he)

/-- If deletion of at most `d` columns leaves a spanning family, then a
`d+1`-linear map is determined by its values on distinct column tuples.
No symmetry assumption on the multilinear map is needed. -/
theorem eq_zero_of_distinct_columns (d : ℕ) {ι : Type*} (v : ι → E)
    (hv : RobustSpanning (R := R) v d)
    (T : MultilinearMap R (fun _ : Fin (d + 1) => E) F)
    (hT : ∀ j : Fin (d + 1) → ι, Function.Injective j →
      T (fun a => v (j a)) = 0) : T = 0 := by
  induction d generalizing ι with
  | zero =>
      have hc : T.curryLeft = 0 := by
        apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top _
          (span_range_eq_top hv)).2
        rintro ⟨_, i, rfl⟩
        ext a
        have hi := hT (fun _ => i) (fun a b _ => by
          apply Fin.ext
          have ha := a.isLt
          have hb := b.isLt
          omega)
        rw [MultilinearMap.curryLeft_apply]
        convert hi using 1
        congr 1
        funext q
        exact Fin.cases rfl (fun j => Fin.elim0 j) q
      rw [← T.uncurry_curryLeft, hc]
      rfl
  | succ d ih =>
      have hc : T.curryLeft = 0 := by
        apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top _
          (span_range_eq_top hv)).2
        rintro ⟨_, i, rfl⟩
        apply ih (fun a : {a : ι // a ≠ i} => v a)
          (robustSpanning_delete hv i) (T.curryLeft (v i))
        intro j hj
        have hji : Function.Injective (fun a => (j a).val) :=
          Subtype.val_injective.comp hj
        have hnot : i ∉ Set.range (fun a => (j a).val) := by
          rintro ⟨a, ha⟩
          exact (j a).property ha
        have hh := hT (Fin.cons i (fun a => (j a).val))
          (Fin.cons_injective_of_injective hnot hji)
        rw [MultilinearMap.curryLeft_apply]
        convert hh using 1
        congr 1
        funext q
        exact Fin.cases rfl (fun _ => rfl) q
      rw [← T.uncurry_curryLeft, hc]
      rfl

/-- A nonzero multilinear form vanishing on all distinct column tuples
certifies failure of robust spanning. -/
theorem not_robustSpanning_of_distinct_zero (d : ℕ) {ι : Type*} (v : ι → E)
    (T : MultilinearMap R (fun _ : Fin (d + 1) => E) F) (hT0 : T ≠ 0)
    (hT : ∀ j : Fin (d + 1) → ι, Function.Injective j →
      T (fun a => v (j a)) = 0) : ¬ RobustSpanning (R := R) v d := by
  intro hv
  exact hT0 (eq_zero_of_distinct_columns d v hv T hT)

/-- Over a field, failure of distinct-column detection produces a nonzero
linear functional supported on at most `d` listed columns. -/
theorem exists_sparse_functional_of_distinct_zero
    {K G U : Type*} [Field K] [AddCommGroup G] [Module K G]
    [AddCommGroup U] [Module K U]
    (d : ℕ) {ι : Type*} (v : ι → G)
    (T : MultilinearMap K (fun _ : Fin (d + 1) => G) U) (hT0 : T ≠ 0)
    (hT : ∀ j : Fin (d + 1) → ι, Function.Injective j →
      T (fun a => v (j a)) = 0) :
    ∃ k ≤ d, ∃ j : Fin k → ι, ∃ ell : G →ₗ[K] K,
      ell ≠ 0 ∧ ∀ i, (∀ a, i ≠ j a) → ell (v i) = 0 := by
  have hn := not_robustSpanning_of_distinct_zero d v T hT0 hT
  simp only [RobustSpanning, not_forall] at hn
  obtain ⟨k, hk, j, hj⟩ := hn
  obtain ⟨ell, hell, hker⟩ :=
    (span K (avoiding v j)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hj)
  refine ⟨k, hk, j, ell, hell, ?_⟩
  intro i hi
  exact hker (subset_span ⟨i, hi, rfl⟩)

end HeadComplexity.RobustCubeProjection
