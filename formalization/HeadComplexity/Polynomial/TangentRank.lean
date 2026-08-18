import HeadComplexity.Polynomial.MatrixRank
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Partition rank of cleared tangent expressions

This module proves the algebraic core of the theorem 28 sign-rank bound.  A
cleared sum of `H` affine ratios has the tangent form

`c * ∏ D_h + ∑ N_h * ∏_{g ≠ h} D_g`.

When every `D_h` and `N_h` splits into a left plus a right function, expansion
by subsets gives one outer product at each endpoint subset and two at every
proper nonempty subset.  Consequently its evaluation matrix has rank at most
`2^(H+1) - 2` for `H > 0`.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace TangentRank

variable {I X Y : Type*} [DecidableEq I]

noncomputable def productValue (s : Finset I) (a b : I → ℝ) : ℝ :=
  ∏ i ∈ s, (a i + b i)

noncomputable def tangentValue (s : Finset I) (c : ℝ)
    (a b r q : I → ℝ) : ℝ :=
  c * productValue s a b +
    ∑ h ∈ s, (r h + q h) * productValue (s.erase h) a b

noncomputable def sideProduct (s : Finset I) (a : I → ℝ) : ℝ :=
  ∏ i ∈ s, a i

noncomputable def sideTangent (s : Finset I) (r a : I → ℝ) : ℝ :=
  ∑ h ∈ s, r h * sideProduct (s.erase h) a

noncomputable def subsetTerm (s t : Finset I) (c : ℝ)
    (a b r q : I → ℝ) : ℝ :=
  let left := sideProduct t a
  let right := sideProduct (s \ t) b
  let leftTan := sideTangent t r a
  let rightTan := sideTangent (s \ t) q b
  (c * left + leftTan) * right + left * rightTan

omit [DecidableEq I] in
@[simp] theorem productValue_empty (a b : I → ℝ) :
    productValue ∅ a b = 1 := by simp [productValue]

omit [DecidableEq I] in
@[simp] theorem sideProduct_empty (a : I → ℝ) :
    sideProduct ∅ a = 1 := by simp [sideProduct]

@[simp] theorem sideTangent_empty (r a : I → ℝ) :
    sideTangent ∅ r a = 0 := by simp [sideTangent]

private theorem productValue_insert {h : I} {s : Finset I} (hh : h ∉ s)
    (a b : I → ℝ) :
    productValue (insert h s) a b = (a h + b h) * productValue s a b := by
  simp [productValue, hh]

private theorem tangentValue_insert {h : I} {s : Finset I} (hh : h ∉ s)
    (c : ℝ) (a b r q : I → ℝ) :
    tangentValue (insert h s) c a b r q =
      (a h + b h) * tangentValue s c a b r q +
        (r h + q h) * productValue s a b := by
  classical
  simp only [tangentValue, productValue_insert hh, sum_insert hh,
    Finset.erase_insert hh]
  have herase (k : I) (hk : k ∈ s) :
      (insert h s).erase k = insert h (s.erase k) := by
    apply Finset.erase_insert_of_ne
    intro heq
    subst k
    exact hh hk
  have hprod (k : I) (hk : k ∈ s) :
      productValue ((insert h s).erase k) a b =
        (a h + b h) * productValue (s.erase k) a b := by
    rw [herase k hk, productValue_insert (by
      exact fun hmem ↦ hh (Finset.erase_subset _ _ hmem))]
  have hsum :
      (∑ k ∈ s, (r k + q k) * productValue ((insert h s).erase k) a b) =
        (a h + b h) *
          ∑ k ∈ s, (r k + q k) * productValue (s.erase k) a b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hprod k hk]
    ring
  rw [hsum, mul_add]
  ring

private theorem sideProduct_insert {h : I} {s : Finset I} (hh : h ∉ s)
    (a : I → ℝ) :
    sideProduct (insert h s) a = a h * sideProduct s a := by
  simp [sideProduct, hh]

private theorem sideTangent_insert {h : I} {s : Finset I} (hh : h ∉ s)
    (r a : I → ℝ) :
    sideTangent (insert h s) r a =
      r h * sideProduct s a + a h * sideTangent s r a := by
  classical
  simp only [sideTangent, sum_insert hh, Finset.erase_insert hh]
  have herase (k : I) (hk : k ∈ s) :
      (insert h s).erase k = insert h (s.erase k) := by
    apply Finset.erase_insert_of_ne
    intro heq
    subst k
    exact hh hk
  have hprod (k : I) (hk : k ∈ s) :
      sideProduct ((insert h s).erase k) a =
        a h * sideProduct (s.erase k) a := by
    rw [herase k hk, sideProduct_insert (by
      exact fun hmem ↦ hh (Finset.erase_subset _ _ hmem))]
  have hsum :
      (∑ k ∈ s, r k * sideProduct ((insert h s).erase k) a) =
        a h * ∑ k ∈ s, r k * sideProduct (s.erase k) a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hprod k hk]
    ring
  rw [hsum]

private theorem subsetTerm_notMem {h : I} {s t : Finset I}
    (hh : h ∉ s) (ht : t ⊆ s) (c : ℝ) (a b r q : I → ℝ) :
    subsetTerm (insert h s) t c a b r q =
      b h * subsetTerm s t c a b r q +
        q h * sideProduct t a * sideProduct (s \ t) b := by
  classical
  have hht : h ∉ t := fun hmem ↦ hh (ht hmem)
  have hdiff : insert h s \ t = insert h (s \ t) := by
    exact Finset.insert_sdiff_of_notMem s hht
  rw [subsetTerm, subsetTerm, hdiff,
    sideProduct_insert (by simp [hh, hht]),
    sideTangent_insert (by simp [hh, hht])]
  ring

private theorem subsetTerm_mem {h : I} {s t : Finset I}
    (hh : h ∉ s) (ht : t ⊆ s) (c : ℝ) (a b r q : I → ℝ) :
    subsetTerm (insert h s) (insert h t) c a b r q =
      a h * subsetTerm s t c a b r q +
        r h * sideProduct t a * sideProduct (s \ t) b := by
  classical
  have hht : h ∉ t := fun hmem ↦ hh (ht hmem)
  have hdiff : insert h s \ insert h t = s \ t := by
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hh]
  rw [subsetTerm, subsetTerm, hdiff,
    sideProduct_insert hht, sideTangent_insert hht]
  ring

/-- Exact subset regrouping of a cleared tangent expression. -/
theorem tangentValue_eq_sum_subsetTerm
    (s : Finset I) (c : ℝ) (a b r q : I → ℝ) :
    tangentValue s c a b r q =
      ∑ t ∈ s.powerset, subsetTerm s t c a b r q := by
  induction s using Finset.induction_on with
  | empty => simp [tangentValue, subsetTerm, productValue, sideProduct, sideTangent]
  | @insert h s hh ih =>
      rw [tangentValue_insert hh]
      rw [Finset.powerset_insert s h, Finset.sum_union]
      · rw [Finset.sum_image]
        · have hsumNot :
              (∑ t ∈ s.powerset, subsetTerm (insert h s) t c a b r q) =
                ∑ t ∈ s.powerset,
                  (b h * subsetTerm s t c a b r q +
                    q h * sideProduct t a * sideProduct (s \ t) b) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact subsetTerm_notMem hh (Finset.mem_powerset.mp ht) c a b r q
          have hsumMem :
              (∑ t ∈ s.powerset,
                subsetTerm (insert h s) (insert h t) c a b r q) =
                ∑ t ∈ s.powerset,
                  (a h * subsetTerm s t c a b r q +
                    r h * sideProduct t a * sideProduct (s \ t) b) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact subsetTerm_mem hh (Finset.mem_powerset.mp ht) c a b r q
          have hprod :
              (∑ t ∈ s.powerset, sideProduct t a * sideProduct (s \ t) b) =
                productValue s a b := by
            simpa [productValue, sideProduct] using
              (Finset.prod_add a b s).symm
          have hsplitNot :
              (∑ t ∈ s.powerset,
                (b h * subsetTerm s t c a b r q +
                  q h * sideProduct t a * sideProduct (s \ t) b)) =
                b h * (∑ t ∈ s.powerset, subsetTerm s t c a b r q) +
                  q h * productValue s a b := by
            calc
              _ = (∑ t ∈ s.powerset, b h * subsetTerm s t c a b r q) +
                    ∑ t ∈ s.powerset,
                      q h * (sideProduct t a * sideProduct (s \ t) b) := by
                rw [Finset.sum_add_distrib]
                congr 1
                apply Finset.sum_congr rfl
                intro t _
                ring
              _ = b h * (∑ t ∈ s.powerset, subsetTerm s t c a b r q) +
                    q h * (∑ t ∈ s.powerset,
                      sideProduct t a * sideProduct (s \ t) b) := by
                rw [Finset.mul_sum, Finset.mul_sum]
              _ = _ := by rw [hprod]
          have hsplitMem :
              (∑ t ∈ s.powerset,
                (a h * subsetTerm s t c a b r q +
                  r h * sideProduct t a * sideProduct (s \ t) b)) =
                a h * (∑ t ∈ s.powerset, subsetTerm s t c a b r q) +
                  r h * productValue s a b := by
            calc
              _ = (∑ t ∈ s.powerset, a h * subsetTerm s t c a b r q) +
                    ∑ t ∈ s.powerset,
                      r h * (sideProduct t a * sideProduct (s \ t) b) := by
                rw [Finset.sum_add_distrib]
                congr 1
                apply Finset.sum_congr rfl
                intro t _
                ring
              _ = a h * (∑ t ∈ s.powerset, subsetTerm s t c a b r q) +
                    r h * (∑ t ∈ s.powerset,
                      sideProduct t a * sideProduct (s \ t) b) := by
                rw [Finset.mul_sum, Finset.mul_sum]
              _ = _ := by rw [hprod]
          rw [hsumNot, hsumMem, hsplitNot, hsplitMem, ih]
          ring
        · intro t ht u hu heq
          have htn : h ∉ t :=
            Finset.notMem_of_mem_powerset_of_notMem ht hh
          have hun : h ∉ u :=
            Finset.notMem_of_mem_powerset_of_notMem hu hh
          calc
            t = (insert h t).erase h := (Finset.erase_insert htn).symm
            _ = (insert h u).erase h := congrArg (fun z : Finset I ↦ z.erase h) heq
            _ = u := Finset.erase_insert hun
      · exact Finset.disjoint_left.mpr (by
          intro t ht hti
          rcases Finset.mem_image.mp hti with ⟨u, hu, rfl⟩
          exact hh ((Finset.mem_powerset.mp ht) (Finset.mem_insert_self h u)))

variable [Fintype I] [Fintype Y]

noncomputable def tangentMatrix (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) : Matrix X Y ℝ :=
  fun x y ↦ tangentValue Finset.univ c
    (fun h ↦ a h x) (fun h ↦ b h y)
    (fun h ↦ r h x) (fun h ↦ q h y)

noncomputable def subsetTermMatrix (t : Finset I) (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) : Matrix X Y ℝ :=
  fun x y ↦ subsetTerm Finset.univ t c
    (fun h ↦ a h x) (fun h ↦ b h y)
    (fun h ↦ r h x) (fun h ↦ q h y)

omit [Fintype Y] in
theorem tangentMatrix_eq_sum_subsetTermMatrix (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) :
    tangentMatrix c a r b q =
      ∑ t ∈ (Finset.univ : Finset I).powerset,
        subsetTermMatrix t c a r b q := by
  ext x y
  simp only [tangentMatrix, Matrix.sum_apply]
  change tangentValue Finset.univ c
      (fun h ↦ a h x) (fun h ↦ b h y)
      (fun h ↦ r h x) (fun h ↦ q h y) =
    ∑ t ∈ (Finset.univ : Finset I).powerset,
      subsetTerm Finset.univ t c
        (fun h ↦ a h x) (fun h ↦ b h y)
        (fun h ↦ r h x) (fun h ↦ q h y)
  exact tangentValue_eq_sum_subsetTerm Finset.univ c
    (fun h ↦ a h x) (fun h ↦ b h y)
    (fun h ↦ r h x) (fun h ↦ q h y)

theorem subsetTermMatrix_rank_le_two (t : Finset I) (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) :
    (subsetTermMatrix t c a r b q).rank ≤ 2 := by
  let A : X → ℝ := fun x ↦ sideProduct t (fun h ↦ a h x)
  let R : X → ℝ := fun x ↦ sideTangent t (fun h ↦ r h x) (fun h ↦ a h x)
  let B : Y → ℝ := fun y ↦ sideProduct (Finset.univ \ t) (fun h ↦ b h y)
  let Q : Y → ℝ := fun y ↦ sideTangent (Finset.univ \ t)
    (fun h ↦ q h y) (fun h ↦ b h y)
  have hmatrix : subsetTermMatrix t c a r b q =
      Matrix.vecMulVec (fun x ↦ c * A x + R x) B +
        Matrix.vecMulVec A Q := by
    ext x y
    rfl
  rw [hmatrix]
  exact (Matrix.rank_add_le _ _).trans
    (Nat.add_le_add (Matrix.rank_vecMulVec_le _ _) (Matrix.rank_vecMulVec_le _ _))

theorem subsetTermMatrix_empty_rank_le_one (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) :
    (subsetTermMatrix ∅ c a r b q).rank ≤ 1 := by
  let B : Y → ℝ := fun y ↦
    c * sideProduct Finset.univ (fun h ↦ b h y) +
      sideTangent Finset.univ (fun h ↦ q h y) (fun h ↦ b h y)
  have hmatrix : subsetTermMatrix ∅ c a r b q =
      Matrix.vecMulVec (fun _ ↦ 1) B := by
    ext x y
    simp [subsetTermMatrix, subsetTerm, B, Matrix.vecMulVec]
  rw [hmatrix]
  exact Matrix.rank_vecMulVec_le _ _

theorem subsetTermMatrix_univ_rank_le_one (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) :
    (subsetTermMatrix Finset.univ c a r b q).rank ≤ 1 := by
  let A : X → ℝ := fun x ↦
    c * sideProduct Finset.univ (fun h ↦ a h x) +
      sideTangent Finset.univ (fun h ↦ r h x) (fun h ↦ a h x)
  have hmatrix : subsetTermMatrix Finset.univ c a r b q =
      Matrix.vecMulVec A (fun _ ↦ 1) := by
    ext x y
    simp [subsetTermMatrix, subsetTerm, A, Matrix.vecMulVec]
  rw [hmatrix]
  exact Matrix.rank_vecMulVec_le _ _

/-- The exact tangent rank cap.  The positivity hypothesis on the number of
factors is necessary because a zero-factor biased expression can have rank
one, whereas the displayed formula is zero at `H = 0`. -/
theorem tangentMatrix_rank_le (hI : 0 < Fintype.card I) (c : ℝ)
    (a r : I → X → ℝ) (b q : I → Y → ℝ) :
    (tangentMatrix c a r b q).rank ≤ 2 ^ (Fintype.card I + 1) - 2 := by
  classical
  letI : Nonempty I := Fintype.card_pos_iff.mp hI
  let all : Finset (Finset I) := (Finset.univ : Finset I).powerset
  let proper : Finset (Finset I) := (all.erase ∅).erase Finset.univ
  have hempty : (∅ : Finset I) ∈ all := by simp [all]
  have hne : (Finset.univ : Finset I) ≠ ∅ := by
    intro heq
    have hcard : Fintype.card I = 0 := by
      simpa only [Finset.card_univ, Finset.card_empty] using congrArg Finset.card heq
    omega
  have huniv : (Finset.univ : Finset I) ∈ all.erase ∅ := by
    simp [all, hne]
  have hsum :
      (∑ t ∈ all, subsetTermMatrix t c a r b q) =
        subsetTermMatrix ∅ c a r b q +
          subsetTermMatrix Finset.univ c a r b q +
            ∑ t ∈ proper, subsetTermMatrix t c a r b q := by
    rw [← Finset.sum_erase_add all
      (fun t ↦ subsetTermMatrix t c a r b q) hempty]
    rw [← Finset.sum_erase_add (all.erase ∅)
      (fun t ↦ subsetTermMatrix t c a r b q) huniv]
    dsimp [proper]
    abel
  rw [tangentMatrix_eq_sum_subsetTermMatrix]
  change (∑ t ∈ all, subsetTermMatrix t c a r b q).rank ≤ _
  rw [hsum]
  refine (Matrix.rank_add_le _ _).trans ?_
  refine (Nat.add_le_add
    ((Matrix.rank_add_le _ _).trans
      (Nat.add_le_add (subsetTermMatrix_empty_rank_le_one c a r b q)
        (subsetTermMatrix_univ_rank_le_one c a r b q)))
    (Matrix.rank_finset_sum_le proper (fun t ↦ subsetTermMatrix t c a r b q))).trans ?_
  have hproper : proper.card = 2 ^ Fintype.card I - 2 := by
    dsimp [proper]
    rw [Finset.card_erase_of_mem huniv, Finset.card_erase_of_mem hempty,
      Finset.card_powerset, Finset.card_univ]
    omega
  have hranks :
      (∑ t ∈ proper, (subsetTermMatrix t c a r b q).rank) ≤
        2 * proper.card := by
    calc
      (∑ t ∈ proper, (subsetTermMatrix t c a r b q).rank) ≤
          ∑ _t ∈ proper, 2 :=
        Finset.sum_le_sum fun t _ ↦ subsetTermMatrix_rank_le_two t c a r b q
      _ = 2 * proper.card := by simp [Nat.mul_comm]
  rw [hproper] at hranks
  have hpow : 2 ≤ 2 ^ Fintype.card I := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2)
      (by omega : 1 ≤ Fintype.card I)
  rw [pow_succ]
  omega

end TangentRank

end HeadComplexity
