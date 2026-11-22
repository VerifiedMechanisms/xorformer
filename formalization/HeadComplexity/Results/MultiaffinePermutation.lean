import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Multiaffine decoding on permutations

This is an auxiliary obstruction to a generic sign-counting shortcut. It does
not prove a lower bound on attention-head complexity. On permutations of a fixed
list of distinct real numbers, a multiaffine polynomial can read an arbitrary
function of the entry in any specified position. The polynomial does not even
use the variable at that position.
-/

namespace HeadComplexity.MultiaffinePermutation

open Finset MvPolynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def denominator (a : ι → ℝ) (r : ι) : ℝ :=
  ∏ j ∈ Finset.univ.erase r, (a r - a j)

noncomputable def basis (a : ι → ℝ) (i r : ι) : MvPolynomial ι ℝ :=
  C (denominator a r)⁻¹ * ∏ j ∈ Finset.univ.erase i, (C (a r) - X j)

noncomputable def decoder (a v : ι → ℝ) (i : ι) : MvPolynomial ι ℝ :=
  ∑ r, C (v r) * basis a i r

theorem denominator_ne_zero (a : ι → ℝ) (ha : Function.Injective a) (r : ι) :
    denominator a r ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr fun h ↦ (Finset.mem_erase.mp hj).1 (ha h).symm

theorem basis_eval_permutation (a : ι → ℝ) (ha : Function.Injective a)
    (e : Equiv.Perm ι) (i r : ι) :
    MvPolynomial.eval (a ∘ e) (basis a i r) = if r = e i then 1 else 0 := by
  classical
  simp only [basis, map_mul, eval_C, map_prod, map_sub, eval_X, Function.comp_apply]
  by_cases h : r = e i
  · subst r
    have hp : (∏ j ∈ Finset.univ.erase i, (a (e i) - a (e j))) =
        denominator a (e i) := by
      unfold denominator
      apply Finset.prod_equiv e
      · intro j
        simp
      · intro j _
        rfl
    rw [hp, inv_mul_cancel₀ (denominator_ne_zero a ha (e i)), ite_eq_left rfl]
  · have hj : e.symm r ∈ Finset.univ.erase i := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro he
      apply h
      simpa using congrArg e he
    have hp : (∏ j ∈ Finset.univ.erase i, (a r - a (e j))) = 0 := by
      apply Finset.prod_eq_zero hj
      simp
    rw [hp, mul_zero, ite_eq_right h]

theorem decoder_eval_permutation (a v : ι → ℝ) (ha : Function.Injective a)
    (e : Equiv.Perm ι) (i : ι) :
    MvPolynomial.eval (a ∘ e) (decoder a v i) = v (e i) := by
  classical
  simp [decoder, basis_eval_permutation a ha e, Finset.sum_ite_eq']

theorem basis_degreeOf_le_one (a : ι → ℝ) (i r k : ι) :
    (basis a i r).degreeOf k ≤ 1 := by
  classical
  have hf (j : ι) : (C (a r) - X j : MvPolynomial ι ℝ).degreeOf k ≤
      if k = j then 1 else 0 := by
    have heq : (C (a r) - X j : MvPolynomial ι ℝ) =
        C (a r) + C (-1 : ℝ) * X j := by simp [sub_eq_add_neg]
    rw [heq]
    apply (degreeOf_add_le k _ _).trans
    simp only [degreeOf_C, zero_le, max_eq_right]
    exact (degreeOf_C_mul_le _ _ _).trans (by simp [degreeOf_X])
  unfold basis
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_prod_le k _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, if k = j then 1 else 0 :=
      Finset.sum_le_sum fun j _ ↦ hf j
    _ ≤ 1 := by by_cases h : k = i <;> simp [h]

theorem decoder_degreeOf_le_one (a v : ι → ℝ) (i k : ι) :
    (decoder a v i).degreeOf k ≤ 1 := by
  classical
  unfold decoder
  apply (degreeOf_sum_le k _ _).trans
  apply Finset.sup_le
  intro r _
  exact (degreeOf_C_mul_le _ _ _).trans (basis_degreeOf_le_one a i r k)

variable {κ β : Type*} [Fintype κ] [Fintype β] [DecidableEq β]

/-- The Hall obstruction expressed in terms of color classes contained in a
small set. This criterion is verified by the affine-plane construction in the
accompanying writeup. -/
theorem exists_color_representatives (c : κ → ι → β)
    (h : ∀ T : Finset ι, T.card < Fintype.card κ →
      (Finset.univ.filter fun k ↦ ∃ b, (Finset.univ.filter fun r ↦ c k r = b) ⊆ T).card
        ≤ T.card)
    (target : κ → β) :
    ∃ f : κ → ι, Function.Injective f ∧ ∀ k, c k (f k) = target k := by
  classical
  let t : κ → Finset ι := fun k ↦ Finset.univ.filter fun r ↦ c k r = target k
  have hhall : ∀ s : Finset κ, s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra! hbad
    let T := s.biUnion t
    have hT : T.card < Fintype.card κ :=
      hbad.trans_le (Finset.card_le_univ s)
    have hs : s ⊆ Finset.univ.filter
        (fun k ↦ ∃ b, (Finset.univ.filter fun r ↦ c k r = b) ⊆ T) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨target k, ?_⟩
      intro r hr
      exact Finset.mem_biUnion.mpr ⟨k, hk, hr⟩
    have := (Finset.card_le_card hs).trans (h T hT)
    exact (not_lt_of_ge this) hbad
  obtain ⟨f, hf, hfc⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  exact ⟨f, hf, fun k ↦ (Finset.mem_filter.mp (hfc k)).2⟩

/-- A color system with the stated Hall property yields independent exact
sign tests by multiaffine polynomials on a positive parameter domain. -/
theorem exists_positive_multiaffine_shattering {b : ℕ}
    (a : ι → ℝ) (ha : Function.Injective a) (hpos : ∀ r, 0 < a r)
    (position : κ ↪ ι) (c : κ → ι → (Fin b → Bool))
    (h : ∀ T : Finset ι, T.card < Fintype.card κ →
      (Finset.univ.filter fun k ↦
        ∃ color, (Finset.univ.filter fun r ↦ c k r = color) ⊆ T).card ≤ T.card) :
    ∃ P : κ × Fin b → MvPolynomial ι ℝ,
      (∀ j r, (P j).degreeOf r ≤ 1) ∧
      ∀ label : κ × Fin b → Bool, ∃ z : ι → ℝ,
        (∀ r, 0 < z r) ∧
        ∀ j, MvPolynomial.eval z (P j) = if label j then 1 else -1 := by
  classical
  let P : κ × Fin b → MvPolynomial ι ℝ := fun j ↦
    decoder a (fun r ↦ if c j.1 r j.2 then 1 else -1) (position j.1)
  refine ⟨P, ?_, ?_⟩
  · intro j r
    exact decoder_degreeOf_le_one _ _ _ _
  · intro label
    obtain ⟨f, hf, hfc⟩ := exists_color_representatives c h (fun k j ↦ label (k, j))
    obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair position f position.injective hf
    refine ⟨a ∘ e, fun r ↦ hpos (e r), ?_⟩
    intro j
    change MvPolynomial.eval (a ∘ e)
      (decoder a (fun r ↦ if c j.1 r j.2 then 1 else -1) (position j.1)) = _
    rw [decoder_eval_permutation a _ ha e, he, hfc]

end HeadComplexity.MultiaffinePermutation
