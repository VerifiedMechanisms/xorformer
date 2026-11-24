import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Coefficient bounds give Lipschitz estimates on the unit cube

The bound is the number of supported monomials times their maximum degree,
when every coefficient has absolute value at most one. This is the elementary
estimate used by the finite sign-rigidity argument.
-/

namespace HeadComplexity.PolynomialCubeLipschitz

noncomputable section

open MvPolynomial
open scoped BigOperators

theorem abs_prod_le_one {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) : |∏ i ∈ s, a i| ≤ 1 := by
  rw [Finset.abs_prod]
  simpa using Finset.prod_le_prod (fun i _ ↦ abs_nonneg (a i)) ha

theorem abs_prod_sub_prod {α : Type*} (s : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have hbs : ∀ j ∈ s, |b j| ≤ 1 := fun j hj ↦ hb j (Finset.mem_insert_of_mem hj)
    have has : ∀ j ∈ s, |a j| ≤ 1 := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
          (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
      _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
          |a i - b i| * |∏ j ∈ s, b j| := by
        simpa only [abs_mul] using abs_add_le
          (a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
          ((a i - b i) * ∏ j ∈ s, b j)
      _ ≤ 1 * (∑ j ∈ s, |a j - b j|) + |a i - b i| * 1 := by
        apply add_le_add
        · exact mul_le_mul hai (ih has hbs) (abs_nonneg _) (by norm_num)
        · exact mul_le_mul_of_nonneg_left (abs_prod_le_one s b hbs) (abs_nonneg _)
      _ = _ := by ring

theorem abs_pow_sub_pow (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (k : ℕ) :
    |a ^ k - b ^ k| ≤ (k : ℝ) * |a - b| := by
  simpa using abs_prod_sub_prod (Finset.univ : Finset (Fin k))
    (fun _ ↦ a) (fun _ ↦ b) (fun _ _ ↦ ha) (fun _ _ ↦ hb)

theorem monomial_lipschitz {α : Type*} (d : α →₀ ℕ) (x y : α → ℝ) (ε : ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) (hxy : ∀ i, |x i - y i| ≤ ε) :
    |d.prod (fun i k ↦ x i ^ k) - d.prod (fun i k ↦ y i ^ k)| ≤
      (d.sum (fun _ k ↦ k) : ℝ) * ε := by
  classical
  unfold Finsupp.prod Finsupp.sum
  calc
    _ ≤ ∑ i ∈ d.support, |x i ^ d i - y i ^ d i| := by
      apply abs_prod_sub_prod
      · intro i _
        rw [abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg _) (hx i) (d i)
      · intro i _
        rw [abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg _) (hy i) (d i)
    _ ≤ ∑ i ∈ d.support, (d i : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro i _
      exact (abs_pow_sub_pow (x i) (y i) (hx i) (hy i) (d i)).trans
        (mul_le_mul_of_nonneg_left (hxy i) (Nat.cast_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]

theorem eval_lipschitz {α : Type*} (P : MvPolynomial α ℝ) (x y : α → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (hxy : ∀ i, |x i - y i| ≤ ε) (hc : ∀ d, |P.coeff d| ≤ 1) :
    |eval x P - eval y P| ≤ (P.support.card : ℝ) * (P.totalDegree : ℝ) * ε := by
  classical
  have heval (z : α → ℝ) : eval z P =
      ∑ d ∈ P.support, P.coeff d * d.prod (fun i k ↦ z i ^ k) := by
    conv_lhs => rw [P.as_sum]
    simp only [eval_sum, eval_monomial]
  rw [heval x, heval y, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ P.support, |P.coeff d *
        (d.prod (fun i k ↦ x i ^ k) - d.prod (fun i k ↦ y i ^ k))| := by
      simpa only [mul_sub] using Finset.abs_sum_le_sum_abs
        (fun d ↦ P.coeff d * d.prod (fun i k ↦ x i ^ k) -
          P.coeff d * d.prod (fun i k ↦ y i ^ k)) P.support
    _ ≤ ∑ _d ∈ P.support, (P.totalDegree : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hdeg : (d.sum (fun _ k ↦ k) : ℝ) ≤ (P.totalDegree : ℝ) := by
        exact_mod_cast MvPolynomial.le_totalDegree hd
      calc
        _ ≤ 1 * ((d.sum (fun _ k ↦ k) : ℝ) * ε) :=
          mul_le_mul (hc d) (monomial_lipschitz d x y ε hx hy hxy) (abs_nonneg _)
            (by norm_num)
        _ ≤ (P.totalDegree : ℝ) * ε := by
          simpa using mul_le_mul_of_nonneg_right hdeg hε
    _ = _ := by simp [mul_assoc]

def monomialCode {α : Type*} (k : ℕ) (d : α →₀ ℕ)
    (hd : d.toMultiset.card ≤ k) : Sym (Option α) k :=
  ⟨d.toMultiset.map some + Multiset.replicate (k - d.toMultiset.card) none,
    by simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
       omega⟩

theorem monomialCode_injective {α : Type*} (k : ℕ) :
    Function.Injective (fun d : {d : α →₀ ℕ // d.toMultiset.card ≤ k} ↦
      monomialCode k d.val d.property) := by
  classical
  intro d e heq
  apply Subtype.ext
  ext i
  have hc := congrArg (fun s : Sym (Option α) k ↦ Multiset.count (some i) s.val) heq
  simpa only [monomialCode, Multiset.count_add, Multiset.count_map_eq_count' some
    _ (Option.some_injective α), Multiset.count_replicate, reduceCtorEq, ite_false,
    add_zero, Finsupp.count_toMultiset] using hc

theorem support_card_le_choose {α : Type*} [Fintype α] (P : MvPolynomial α ℝ)
    (k : ℕ) (hdeg : P.totalDegree ≤ k) :
    P.support.card ≤ (Fintype.card α + k).choose k := by
  classical
  let code (d : P.support) : Sym (Option α) k := monomialCode k d.val
    (by rw [Finsupp.card_toMultiset]; exact (MvPolynomial.le_totalDegree d.property).trans hdeg)
  have hcode : Function.Injective code := by
    intro d e h
    apply Subtype.ext
    ext i
    have hc := congrArg (fun s : Sym (Option α) k ↦ Multiset.count (some i) s.val) h
    simpa only [code, monomialCode, Multiset.count_add, Multiset.count_map_eq_count' some
      _ (Option.some_injective α), Multiset.count_replicate, reduceCtorEq, ite_false,
      add_zero, Finsupp.count_toMultiset] using hc
  have hcard := Fintype.card_le_of_injective code hcode
  simpa only [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_option,
    Nat.add_right_comm (Fintype.card α) 1 k, Nat.add_sub_cancel] using hcard

theorem cubic_fourteen_support_card (P : MvPolynomial (Fin 14) ℝ)
    (hdeg : P.totalDegree ≤ 3) : P.support.card ≤ 680 := by
  have h := support_card_le_choose P 3 hdeg
  norm_num [Nat.choose] at h
  exact h

theorem cubic_fourteen_lipschitz (P : MvPolynomial (Fin 14) ℝ)
    (hdeg : P.totalDegree ≤ 3) (x y : Fin 14 → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (hxy : ∀ i, |x i - y i| ≤ ε) (hc : ∀ d, |P.coeff d| ≤ 1) :
    |eval x P - eval y P| ≤ 2040 * ε := by
  have hcard : (P.support.card : ℝ) ≤ 680 := by
    exact_mod_cast cubic_fourteen_support_card P hdeg
  have hdegree : (P.totalDegree : ℝ) ≤ 3 := by exact_mod_cast hdeg
  apply (eval_lipschitz P x y ε hε hx hy hxy hc).trans
  have hmul : (P.support.card : ℝ) * (P.totalDegree : ℝ) ≤ 2040 := by
    calc
      _ ≤ 680 * (3 : ℝ) := mul_le_mul hcard hdegree (Nat.cast_nonneg _) (by norm_num)
      _ = _ := by norm_num
  exact mul_le_mul_of_nonneg_right hmul hε

end
end HeadComplexity.PolynomialCubeLipschitz
