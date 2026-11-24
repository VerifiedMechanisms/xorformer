import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Alternating moments over finite subsets

Inclusion-exclusion cancels every power below the number of directions. The
first surviving moment is a factorial times their product.
-/

namespace HeadComplexity
namespace AlternatingMoments

open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

noncomputable def power (s : Finset ι) (D : ι → R) (k : ℕ) : R :=
  ∑ I ∈ s.powerset, (-1 : R) ^ I.card * (∑ i ∈ I, D i) ^ k

theorem power_insert (s : Finset ι) (D : ι → R) (a : ι) (ha : a ∉ s) (k : ℕ) :
    power (insert a s) D k =
      - ∑ j ∈ Finset.range k, (k.choose j : R) * D a ^ (k - j) * power s D j := by
  classical
  rw [power, Finset.sum_powerset_insert ha]
  have hshift : (∑ I ∈ s.powerset,
      (-1 : R) ^ (insert a I).card * (∑ i ∈ insert a I, D i) ^ k) =
      - ∑ j ∈ Finset.range (k + 1), (k.choose j : R) * D a ^ (k - j) * power s D j := by
    have hmem (I : Finset ι) (hI : I ∈ s.powerset) : a ∉ I :=
      fun h ↦ ha (Finset.mem_powerset.mp hI h)
    calc
      _ = - ∑ I ∈ s.powerset, (-1 : R) ^ I.card *
          ((∑ i ∈ I, D i) + D a) ^ k := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro I hI
        rw [Finset.card_insert_of_notMem (hmem I hI),
          Finset.sum_insert (hmem I hI), pow_succ]
        ring
      _ = _ := by
        congr 1
        simp_rw [add_pow, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [power, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I hI
        ring
  rw [hshift, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul]
  change power s D k + (- (_ + power s D k)) = _
  ring

omit [DecidableEq ι] in
theorem power_below_and_top (s : Finset ι) (D : ι → R) :
    (∀ k < s.card, power s D k = 0) ∧
      power s D s.card = (-1 : R)^s.card * (s.card.factorial : R) * ∏ i ∈ s, D i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [power]
  | @insert a s ha ih =>
    constructor
    · intro k hk
      rw [power_insert s D a ha]
      apply neg_eq_zero.mpr
      apply Finset.sum_eq_zero
      intro j hj
      rw [ih.1 j (by rw [Finset.card_insert_of_notMem ha] at hk
                     have hjk := Finset.mem_range.mp hj
                     omega), mul_zero]
    · rw [Finset.card_insert_of_notMem ha, power_insert s D a ha]
      have hsum : (∑ j ∈ Finset.range (s.card + 1),
          ((s.card + 1).choose j : R) * D a ^ (s.card + 1 - j) * power s D j) =
          (s.card + 1 : ℕ) * D a * power s D s.card := by
        rw [Finset.sum_range_succ]
        have hz : (∑ j ∈ Finset.range s.card,
            ((s.card + 1).choose j : R) * D a ^ (s.card + 1 - j) * power s D j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [ih.1 j (Finset.mem_range.mp hj), mul_zero]
        rw [hz, zero_add, Nat.choose_succ_self_right]
        simp
      rw [hsum, ih.2, Finset.prod_insert ha, Nat.factorial_succ, Nat.cast_mul, pow_succ]
      ring

omit [DecidableEq ι] in
theorem power_below (s : Finset ι) (D : ι → R) (k : ℕ) (hk : k < s.card) :
    power s D k = 0 := (power_below_and_top s D).1 k hk

omit [DecidableEq ι] in
theorem power_top (s : Finset ι) (D : ι → R) :
    power s D s.card = (-1 : R)^s.card * (s.card.factorial : R) * ∏ i ∈ s, D i :=
  (power_below_and_top s D).2

section RealMixed

open Polynomial

variable (s : Finset ι) (D L : ι → ℝ)

noncomputable def mixed (k : ℕ) : ℝ :=
  ∑ I ∈ s.powerset, (-1 : ℝ)^I.card * (∑ i ∈ I, L i) * (∑ i ∈ I, D i)^k

omit [DecidableEq ι] in
private theorem derivative_power_eval (k : ℕ) :
    ((power s (fun i ↦ C (D i) + C (L i) * X) k).derivative).eval 0 =
      (k : ℝ) * mixed s D L (k - 1) := by
  classical
  simp only [power, derivative_sum, derivative_mul, derivative_pow, derivative_neg, derivative_one,
    derivative_add, derivative_C, derivative_X, zero_add, zero_mul,
    mul_one, add_zero, eval_finsetSum, eval_mul, eval_C,
    eval_add, eval_X, mul_zero, eval_pow, eval_neg, eval_one, eval_zero, mixed]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

omit [DecidableEq ι] in
theorem mixed_below (k : ℕ) (hk : k + 1 < s.card) : mixed s D L k = 0 := by
  have hp := congrArg (fun p : ℝ[X] ↦ p.derivative.eval 0)
    (power_below s (fun i ↦ C (D i) + C (L i) * X) (k + 1) hk)
  rw [derivative_power_eval] at hp
  simp only [Nat.add_sub_cancel, derivative_zero, eval_zero] at hp
  exact (mul_eq_zero.mp hp).resolve_left (by positivity)

theorem mixed_top (hs : 0 < s.card) :
    mixed s D L (s.card - 1) = (-1 : ℝ)^s.card * ((s.card - 1).factorial : ℝ) *
      ∑ h ∈ s, L h * ∏ j ∈ s.erase h, D j := by
  have hp := congrArg (fun p : ℝ[X] ↦ p.derivative.eval 0)
    (power_top s (fun i ↦ C (D i) + C (L i) * X))
  rw [derivative_power_eval] at hp
  simp only [derivative_mul, derivative_pow, derivative_neg, derivative_one,
    derivative_natCast, derivative_prod_finset, derivative_add, derivative_C,
    derivative_X, zero_add, zero_mul, mul_one, add_zero,
    eval_mul, eval_neg, eval_one, eval_pow, eval_natCast, eval_finsetSum,
    eval_prod, eval_add, eval_C, eval_X, mul_zero, neg_zero] at hp
  have hfac : (s.card.factorial : ℝ) = s.card * ((s.card - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred hs.ne').symm
  rw [hfac] at hp
  have hsum : (∑ i ∈ s, (∏ j ∈ s.erase i, D j) * L i) =
      ∑ i ∈ s, L i * ∏ j ∈ s.erase i, D j := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at hp
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  apply mul_left_cancel₀ hc
  calc
    _ = (-1 : ℝ)^s.card * (s.card * ((s.card - 1).factorial : ℝ)) *
        ∑ h ∈ s, L h * ∏ j ∈ s.erase h, D j := hp
    _ = _ := by ring

end RealMixed


/-- A finite geometric expansion with its exact rational remainder. -/
theorem reciprocal_expansion (B t d : ℝ) (hB : B ≠ 0) (hden : B + t * d ≠ 0)
    (H : ℕ) :
    1/(B + t * d) = (∑ k ∈ Finset.range H, (-t)^k * d^k / B^(k + 1)) +
      (-t)^H*d^H/(B^H*(B + t * d)) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    have hr : (-t)^H*d^H/(B^H*(B + t * d)) =
        (-t)^H*d^H/B^(H + 1) + (-t)^(H + 1)*d^(H + 1)/(B^(H + 1)*(B + t * d)) := by
      rw [pow_succ, pow_succ, pow_succ]
      field_simp
      ring
    rw [hr]
    ring


/-- Summing the reciprocal expansion cancels all moments below the first
nonzero one. The remainder is explicit and carries one extra power of t. -/
theorem reciprocal_sum_expansion (s : Finset ι) (D L : ι → ℝ)
    (hs : 0 < s.card) (B t : ℝ) (hB : B ≠ 0)
    (hden : ∀ I ∈ s.powerset, B + t * (∑ i ∈ I, D i) ≠ 0) :
    (∑ I ∈ s.powerset, (-1 : ℝ)^I.card * (∑ i ∈ I, L i) /
        (B + t * (∑ i ∈ I, D i))) =
      ((-t)^(s.card - 1) / B^s.card) *
        ((-1 : ℝ)^s.card * ((s.card - 1).factorial : ℝ) *
          ∑ h ∈ s, L h * ∏ j ∈ s.erase h, D j) +
      (-t)^s.card * ∑ I ∈ s.powerset,
        (-1 : ℝ)^I.card * (∑ i ∈ I, L i) * (∑ i ∈ I, D i)^s.card /
          (B^s.card * (B + t * (∑ i ∈ I, D i))) := by
  have hterm (I : Finset ι) (hI : I ∈ s.powerset) :
      (-1 : ℝ)^I.card * (∑ i ∈ I, L i) / (B + t * (∑ i ∈ I, D i)) =
      (∑ k ∈ Finset.range s.card,
        ((-t)^k / B^(k + 1)) *
          ((-1 : ℝ)^I.card * (∑ i ∈ I, L i) * (∑ i ∈ I, D i)^k)) +
      (-t)^s.card * ((-1 : ℝ)^I.card * (∑ i ∈ I, L i) *
        (∑ i ∈ I, D i)^s.card / (B^s.card * (B + t * (∑ i ∈ I, D i)))) := by
    let A := (-1 : ℝ)^I.card * (∑ i ∈ I, L i)
    let d := ∑ i ∈ I, D i
    change A / (B + t * d) =
      (∑ k ∈ Finset.range s.card, ((-t)^k / B^(k + 1)) * (A * d^k)) +
      (-t)^s.card * (A * d^s.card / (B^s.card * (B + t * d)))
    have he := congrArg (fun v : ℝ ↦ A * v)
      (reciprocal_expansion B t d hB (hden I hI) s.card)
    rw [mul_add] at he
    have hmul : A * (∑ k ∈ Finset.range s.card, (-t)^k * d^k / B^(k + 1)) =
        ∑ k ∈ Finset.range s.card, A * ((-t)^k * d^k / B^(k + 1)) :=
      Finset.mul_sum _ _ _
    rw [hmul] at he
    convert he using 1
    · ring
    · congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        ring
      · ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_comm,
    ← Finset.mul_sum]
  congr 1
  have he : (∑ k ∈ Finset.range s.card,
      ∑ I ∈ s.powerset, ((-t)^k / B^(k + 1)) *
        ((-1 : ℝ)^I.card * (∑ i ∈ I, L i) * (∑ i ∈ I, D i)^k)) =
      ∑ k ∈ Finset.range s.card, ((-t)^k / B^(k + 1)) * mixed s D L k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mixed, Finset.mul_sum]
  rw [he]
  rw [Finset.sum_eq_single (s.card - 1)]
  · rw [mixed_top s D L hs, Nat.sub_add_cancel hs]
  · intro k hk hne
    rw [mixed_below s D L k (by have := Finset.mem_range.mp hk; omega), mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

end AlternatingMoments
end HeadComplexity
