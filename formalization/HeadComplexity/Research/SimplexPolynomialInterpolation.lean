import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

set_option linter.style.header false

/-! Polynomial interpolation on the integer simplex. -/

noncomputable section
namespace HeadComplexity.SimplexPolynomialInterpolation

open Finset MvPolynomial Module
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def falling (k : ℕ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∏ j ∈ range k, (p - C (j : ℝ))

omit [Fintype σ] in
theorem eval_falling (k : ℕ) (p : MvPolynomial σ ℝ) (w : σ → ℝ) :
    eval w (falling k p) = (descPochhammer ℝ k).eval (eval w p) := by
  induction k with
  | zero => simp [falling]
  | succ k ih =>
    simp only [falling, prod_range_succ, map_mul, map_sub, eval_C] at ih ⊢
    rw [ih, descPochhammer_succ_right]
    simp [mul_sub]

omit [Fintype σ] in
theorem totalDegree_falling_le (k : ℕ) (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ 1) : (falling k p).totalDegree ≤ k := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ j ∈ range k, (p - C (j : ℝ)).totalDegree ≤ ∑ _j ∈ range k, 1 := by
      apply sum_le_sum
      intro j _
      exact (totalDegree_sub _ _).trans (max_le hp (by rw [totalDegree_C]; omega))
    _ = k := by simp

def choosePoly (k : ℕ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  C ((k.factorial : ℝ)⁻¹) * falling k p

omit [Fintype σ] in
theorem eval_choosePoly_nat (k m : ℕ) (p : MvPolynomial σ ℝ) (w : σ → ℝ)
    (hp : eval w p = (m : ℝ)) :
    eval w (choosePoly k p) = (m.choose k : ℝ) := by
  simp only [choosePoly, map_mul, eval_C, eval_falling, hp,
    descPochhammer_eval_eq_descFactorial]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

omit [Fintype σ] in
theorem totalDegree_choosePoly_le (k : ℕ) (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ 1) : (choosePoly k p).totalDegree ≤ k := by
  exact (totalDegree_mul _ _).trans (by
    simpa [choosePoly] using totalDegree_falling_le k p hp)

def size (β : σ → ℕ) : ℕ := ∑ i, β i

def Grid (r : ℕ) := {β : σ → ℕ // size β ≤ r}

instance gridFinite (r : ℕ) : Finite (Grid (σ := σ) r) := by
  apply Set.Finite.to_subtype
  apply (Set.Finite.pi' fun _ : σ => Set.finite_le_nat r).subset
  intro β hβ i
  exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hβ

instance gridFintype (r : ℕ) : Fintype (Grid (σ := σ) r) := Fintype.ofFinite _

instance gridDecidableEq (r : ℕ) : DecidableEq (Grid (σ := σ) r) := Classical.decEq _

def gridEquivExactSum (r : ℕ) : Grid (σ := σ) r ≃
    {P : Option σ → ℕ // ∑ i, P i = r} where
  toFun β := ⟨fun i => match i with
    | none => r - size β.val
    | some j => β.val j, by
      rw [Fintype.sum_option]
      change r - size β.val + size β.val = r
      exact Nat.sub_add_cancel β.property⟩
  invFun P := ⟨fun i => P.val (some i), by
    have hP := P.property
    rw [Fintype.sum_option] at hP
    change (∑ i, P.val (some i)) ≤ r
    omega⟩
  left_inv β := by rfl
  right_inv P := by
    apply Subtype.ext
    funext i
    cases i with
    | some i => rfl
    | none =>
      have hP := P.property
      rw [Fintype.sum_option] at hP
      change r - (∑ i, P.val (some i)) = P.val none
      omega

theorem card_grid (r : ℕ) :
    Fintype.card (Grid (σ := σ) r) = Nat.choose (Fintype.card σ + r) r := by
  classical
  let e : Grid (σ := σ) r ≃ Sym (Option σ) r :=
    (gridEquivExactSum r).trans (Sym.equivNatSumOfFintype (Option σ) r).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  rw [Fintype.card_option]
  congr 1
  omega

def cardinalPoly (r : ℕ) (β : Grid (σ := σ) r) : MvPolynomial σ ℝ :=
  (∏ i, choosePoly (β.val i) (X i)) *
    choosePoly (r - size β.val) (C (r : ℝ) - ∑ i, X i)

theorem totalDegree_cardinalPoly_le (r : ℕ) (β : Grid (σ := σ) r) :
    (cardinalPoly r β).totalDegree ≤ r := by
  have hX : ∀ i : σ, (X i : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
    intro i; simp
  have hs : (C (r : ℝ) - ∑ i : σ, (X i : MvPolynomial σ ℝ)).totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · rw [totalDegree_C]; omega
    · exact totalDegree_finsetSum_le (fun i _ => hX i)
  unfold cardinalPoly
  apply (totalDegree_mul _ _).trans
  have hp : (∏ i, choosePoly (β.val i) (X i)).totalDegree ≤ size β.val := by
    apply (totalDegree_finsetProd _ _).trans
    exact sum_le_sum (fun i _ => totalDegree_choosePoly_le _ _ (hX i))
  exact (Nat.add_le_add hp (totalDegree_choosePoly_le _ _ hs)).trans
    (by have hb := β.property; omega)

theorem eval_cardinalPoly (r : ℕ) (β γ : Grid (σ := σ) r) :
    eval (fun i => (γ.val i : ℝ)) (cardinalPoly r β) = if β = γ then 1 else 0 := by
  classical
  have hs : eval (fun i => (γ.val i : ℝ))
      (C (r : ℝ) - ∑ i : σ, (X i : MvPolynomial σ ℝ)) =
      (r - size γ.val : ℕ) := by
    simp only [map_sub, eval_C, map_sum, eval_X]
    rw [Nat.cast_sub γ.property]
    simp [size]
  have hv : eval (fun i => (γ.val i : ℝ)) (cardinalPoly r β) =
      (∏ i, (Nat.choose (γ.val i) (β.val i) : ℝ)) *
        (Nat.choose (r - size γ.val) (r - size β.val) : ℝ) := by
    simp only [cardinalPoly, map_mul, map_prod]
    rw [eval_choosePoly_nat _ _ _ _ hs]
    congr 1
    apply prod_congr rfl
    intro i _
    exact eval_choosePoly_nat _ _ _ _ (eval_X ..)
  rw [hv]
  by_cases he : β = γ
  · subst γ
    simp
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (he h))]
    by_cases hle : ∀ i, β.val i ≤ γ.val i
    · have hne : β.val ≠ γ.val := fun h => he (Subtype.ext h)
      have hex : ∃ i, β.val i < γ.val i := by
        by_contra h
        push Not at h
        apply hne
        funext i
        exact Nat.le_antisymm (hle i) (h i)
      obtain ⟨i, hi⟩ := hex
      have hsz : size β.val < size γ.val :=
        sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ i, hi⟩
      have ht : r - size γ.val < r - size β.val := by
        have hg := γ.property
        omega
      rw [Nat.choose_eq_zero_of_lt ht, Nat.cast_zero, mul_zero]
    · push Not at hle
      obtain ⟨i, hi⟩ := hle
      have hz : ∏ j, (Nat.choose (γ.val j) (β.val j) : ℝ) = 0 := by
        apply prod_eq_zero (mem_univ i)
        simp [Nat.choose_eq_zero_of_lt hi]
      rw [hz, zero_mul]

def degreeIndexEquiv (r : ℕ) :
    {a : σ →₀ ℕ // a.sum (fun _ e => e) ≤ r} ≃ Grid (σ := σ) r :=
  Finsupp.equivFunOnFinite.subtypeEquiv (by
    intro a
    simp [size, Finsupp.sum_fintype])

def monomialBasis (r : ℕ) :
    Basis (Grid (σ := σ) r) ℝ (restrictTotalDegree σ ℝ r) :=
  (basisRestrictSupport ℝ {a : σ →₀ ℕ | a.sum (fun _ e => e) ≤ r}).reindex
    (degreeIndexEquiv r)

def evaluateGrid (r : ℕ) :
    restrictTotalDegree σ ℝ r →ₗ[ℝ] (Grid (σ := σ) r → ℝ) where
  toFun p β := eval (fun i => (β.val i : ℝ)) p.val
  map_add' p q := by ext β; simp
  map_smul' a p := by ext β; simp

def cardinalElement (r : ℕ) (β : Grid (σ := σ) r) : restrictTotalDegree σ ℝ r :=
  ⟨cardinalPoly r β, (mem_restrictTotalDegree σ r _).mpr (totalDegree_cardinalPoly_le r β)⟩

theorem evaluateGrid_surjective (r : ℕ) :
    Function.Surjective (evaluateGrid (σ := σ) r) := by
  classical
  intro v
  refine ⟨∑ β, v β • cardinalElement r β, ?_⟩
  ext γ
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ β, v β * eval (fun i => (γ.val i : ℝ)) (cardinalPoly r β)) = v γ
  simp [eval_cardinalPoly]

theorem evaluateGrid_injective (r : ℕ) :
    Function.Injective (evaluateGrid (σ := σ) r) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    (evaluateGrid_surjective r)
  rw [Module.finrank_eq_card_basis (monomialBasis (σ := σ) r), Module.finrank_pi]

theorem interpolation_identity (r : ℕ) (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ r) :
    p = ∑ β : Grid (σ := σ) r,
      eval (fun i => (β.val i : ℝ)) p • cardinalPoly r β := by
  classical
  let p' : restrictTotalDegree σ ℝ r :=
    ⟨p, (mem_restrictTotalDegree σ r p).mpr hp⟩
  have he : p' = ∑ β : Grid (σ := σ) r,
      eval (fun i => (β.val i : ℝ)) p • cardinalElement r β := by
    apply evaluateGrid_injective r
    ext γ
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change eval (fun i => (γ.val i : ℝ)) p =
      ∑ β, eval (fun i => (β.val i : ℝ)) p *
        eval (fun i => (γ.val i : ℝ)) (cardinalPoly r β)
    simp [eval_cardinalPoly]
  simpa [p', cardinalElement] using congrArg Subtype.val he

theorem interpolation_eval (r : ℕ) (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ r) (w : σ → ℝ) :
    eval w p = ∑ β : Grid (σ := σ) r,
      eval (fun i => (β.val i : ℝ)) p * eval w (cardinalPoly r β) := by
  conv_lhs => rw [interpolation_identity r p hp]
  simp

def translate (v : σ → ℝ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  bind₁ (fun i => X i + C (v i)) p

omit [Fintype σ] in
theorem eval_translate (v w : σ → ℝ) (p : MvPolynomial σ ℝ) :
    eval w (translate v p) = eval (fun i => w i + v i) p := by
  change eval₂Hom (RingHom.id ℝ) w (bind₁ (fun i => X i + C (v i)) p) = _
  rw [eval₂Hom_bind₁]
  have he : (fun i => eval₂Hom (RingHom.id ℝ) w (X i + C (v i))) =
      (fun i => w i + v i) := by
    funext i
    change eval w (X i + C (v i)) = w i + v i
    simp
  rw [he]
  rfl

omit [Fintype σ] in
theorem totalDegree_translate_le (v : σ → ℝ) (p : MvPolynomial σ ℝ) :
    (translate v p).totalDegree ≤ p.totalDegree := by
  have hf : ∀ i : σ, (X i + C (v i) : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
    intro i
    exact (totalDegree_add _ _).trans (max_le (by simp) (by rw [totalDegree_C]; omega))
  unfold translate
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro a ha
  rw [bind₁_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ a.support, ((X i + C (v i)) ^ a i).totalDegree) ≤
        ∑ i ∈ a.support, a i := by
      apply sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (a i) (hf i))
    _ ≤ p.totalDegree := le_totalDegree ha

theorem translated_interpolation_eval (r : ℕ) (p : MvPolynomial σ ℝ)
    (hp : p.totalDegree ≤ r) (v w : σ → ℝ) :
    eval w p = ∑ β : Grid (σ := σ) r,
      eval (fun i => v i + (β.val i : ℝ)) p *
        eval (fun i => w i - v i) (cardinalPoly r β) := by
  have h := interpolation_eval r (translate v p)
    ((totalDegree_translate_le v p).trans hp) (fun i => w i - v i)
  simpa [eval_translate, add_comm] using h

end HeadComplexity.SimplexPolynomialInterpolation
