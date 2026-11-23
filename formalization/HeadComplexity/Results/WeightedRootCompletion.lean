import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- Total weight in a list of weighted Boolean coordinates. -/
def rootCompletionWeight (data : List (ℕ × Bool)) : ℕ :=
  (data.map Prod.fst).sum

/-- Append a new interval to an old interval, with the two intervals
exchanged when the new Boolean coordinate is true. The construction is
written recursively from the tail of the coordinate list. -/
def weightedRootValues : List (ℕ × Bool) → List ℕ
  | [] => [0]
  | (c, b) :: data =>
      (weightedRootValues data).map (fun r => r + if b then c else 0) ++
      (List.range c).map (fun j => j + if b then 0 else rootCompletionWeight data + 1)

/-- At every Boolean vertex, the explicit weighted completion takes each
integer value between zero and the total weight exactly once. Zero weights
are allowed; they append an empty interval. This is an identity for one
constructed root list, not a universal sign-representation theorem. -/
theorem weightedRootValues_perm_range (data : List (ℕ × Bool)) :
    (weightedRootValues data).Perm (List.range (rootCompletionWeight data + 1)) := by
  induction data with
  | nil => simp [weightedRootValues, rootCompletionWeight, List.range_succ]
  | cons pair data ih =>
    rcases pair with ⟨c, b⟩
    have hw : rootCompletionWeight ((c, b) :: data) = c + rootCompletionWeight data := by
      simp [rootCompletionWeight]
    rw [hw]
    cases b with
    | false =>
      simp only [weightedRootValues, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      simp only [List.map_id']
      have hp := ih.append (List.Perm.refl
        ((List.range c).map (fun j => j + (rootCompletionWeight data + 1))))
      apply hp.trans
      apply List.Perm.of_eq
      rw [show c + rootCompletionWeight data + 1 =
        (rootCompletionWeight data + 1) + c by omega,
        List.range_add (n := rootCompletionWeight data + 1) (m := c)]
      congr 1
      apply List.map_congr_left
      intro j _
      omega
    | true =>
      simp only [weightedRootValues, ↓reduceIte, Nat.add_zero]
      simp only [List.map_id']
      have hp := (ih.map (fun r => r + c)).append (List.Perm.refl (List.range c))
      apply hp.trans
      apply List.perm_append_comm.trans
      apply List.Perm.of_eq
      rw [show c + rootCompletionWeight data + 1 =
        c + (rootCompletionWeight data + 1) by omega,
        List.range_add (n := c) (m := rootCompletionWeight data + 1)]
      congr 1
      apply List.map_congr_left
      intro j _
      omega

/-- The exact number of entries is one plus the sum of the weights. -/
theorem weightedRootValues_length (data : List (ℕ × Bool)) :
    (weightedRootValues data).length = rootCompletionWeight data + 1 := by
  simpa using (weightedRootValues_perm_range data).length_eq

/-- Every commutative product of functions of the root values is unchanged
by the Boolean choices. Applying this to `j ↦ s + j` gives the polynomial
product identity used in the root-completion construction. -/
theorem weightedRootValues_prod {M : Type*} [CommMonoid M]
    (data : List (ℕ × Bool)) (f : ℕ → M) :
    ((weightedRootValues data).map f).prod =
      ((List.range (rootCompletionWeight data + 1)).map f).prod := by
  exact ((weightedRootValues_perm_range data).map f).prod_eq

/-- Affine polynomial forms for the same construction, before assigning
Boolean values to their coordinates. Repeated coordinate indices are
permitted. -/
noncomputable def weightedRootPolynomials {ι : Type*} :
    List (ℕ × ι) → List (MvPolynomial ι ℤ)
  | [] => [0]
  | (c, i) :: data =>
      (weightedRootPolynomials data).map
        (fun p => p + MvPolynomial.C (c : ℤ) * MvPolynomial.X i) ++
      (List.range c).map (fun (j : ℕ) => MvPolynomial.C (j : ℤ) +
        MvPolynomial.C (((data.map Prod.fst).sum + 1 : ℕ) : ℤ) *
          (1 - MvPolynomial.X i))

/-- Every root form constructed above is affine. -/
theorem weightedRootPolynomials_totalDegree_le_one {ι : Type*}
    (data : List (ℕ × ι)) (p : MvPolynomial ι ℤ)
    (hp : p ∈ weightedRootPolynomials data) : p.totalDegree ≤ 1 := by
  induction data generalizing p with
  | nil =>
    have hp0 : p = 0 := by simpa [weightedRootPolynomials] using hp
    rw [hp0]
    simp
  | cons pair data ih =>
    classical
    rcases pair with ⟨c, i⟩
    simp only [weightedRootPolynomials, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨j, _, rfl⟩
    · apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (ih q hq)
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
      omega
    · apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by rw [MvPolynomial.totalDegree_C]; omega)
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
      apply (MvPolynomial.totalDegree_sub _ _).trans
      simp only [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]
      omega

/-- Evaluation of the affine forms agrees exactly with the natural-number
interval completion. -/
theorem weightedRootPolynomials_eval {ι : Type*} (data : List (ℕ × ι))
    (x : ι → Bool) :
    (weightedRootPolynomials data).map
        (MvPolynomial.eval (fun i => if x i then (1 : ℤ) else 0)) =
      (weightedRootValues (data.map (fun p => (p.1, x p.2)))).map (Nat.cast : ℕ → ℤ) := by
  induction data with
  | nil => simp [weightedRootPolynomials, weightedRootValues]
  | cons pair data ih =>
    rcases pair with ⟨c, i⟩
    have hw : rootCompletionWeight (data.map (fun p => (p.1, x p.2))) =
        (data.map Prod.fst).sum := by
      simp [rootCompletionWeight, List.map_map, Function.comp_def]
    cases hxi : x i <;>
      simp only [weightedRootPolynomials, weightedRootValues, List.map_cons,
        List.map_append, List.map_map, Function.comp_def, map_add, map_mul,
        map_sub, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, hxi,
        Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, sub_zero,
        mul_one, sub_self, hw, Nat.cast_add, Nat.cast_one]
    · congr 1
    · congr 1
      simpa only [List.map_map, Function.comp_def, Nat.cast_add] using
        congrArg (List.map (fun r : ℤ => r + c)) ih

/-- The affine forms evaluate to a permutation of the prescribed integer
root list at every Boolean vertex. -/
theorem weightedRootPolynomials_eval_perm_range {ι : Type*}
    (data : List (ℕ × ι)) (x : ι → Bool) :
    ((weightedRootPolynomials data).map
        (MvPolynomial.eval (fun i => if x i then (1 : ℤ) else 0))).Perm
      ((List.range ((data.map Prod.fst).sum + 1)).map (Nat.cast : ℕ → ℤ)) := by
  rw [weightedRootPolynomials_eval]
  have h := (weightedRootValues_perm_range
    (data.map (fun p => (p.1, x p.2)))).map (Nat.cast : ℕ → ℤ)
  simpa [rootCompletionWeight, List.map_map, Function.comp_def] using h

/-- Product identity for the actual affine root forms. The right side
does not depend on the Boolean input. -/
theorem weightedRootPolynomials_eval_prod {ι M : Type*} [CommMonoid M]
    (data : List (ℕ × ι)) (x : ι → Bool) (f : ℤ → M) :
    ((weightedRootPolynomials data).map (fun p =>
        f (MvPolynomial.eval (fun i => if x i then (1 : ℤ) else 0) p))).prod =
      ((List.range ((data.map Prod.fst).sum + 1)).map
        (fun (j : ℕ) => f (j : ℤ))).prod := by
  have h := ((weightedRootPolynomials_eval_perm_range data x).map f).prod_eq
  simpa only [List.map_map, Function.comp_def] using h

end HeadComplexity
