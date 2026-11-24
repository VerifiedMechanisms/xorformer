import HeadComplexity.Polynomial.PolynomialCubeLipschitz

set_option linter.style.header false

/-! # Exactly 680 monomials of total degree at most three in fourteen variables -/

namespace HeadComplexity.CubicMonomialBasis

noncomputable section

open MvPolynomial PolynomialCubeLipschitz
open scoped BigOperators

theorem option_multiset_decomposition {α : Type*} [DecidableEq α]
    (s : Multiset (Option α)) :
    (s.filterMap id).map some + Multiset.replicate (s.count none) none = s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    cases a with
    | none => simpa [Multiset.filterMap_cons, Multiset.replicate_succ,
        Multiset.cons_add, Multiset.add_cons] using congrArg (Multiset.cons none) ih
    | some a => simpa [Multiset.filterMap_cons, Multiset.cons_add] using
        congrArg (Multiset.cons (some a)) ih

def DegreeSet (α : Type*) (k : ℕ) := {d : α →₀ ℕ // d.toMultiset.card ≤ k}

def decode {α : Type*} [DecidableEq α] {k : ℕ} (s : Sym (Option α) k) : DegreeSet α k :=
  ⟨(s.val.filterMap id).toFinsupp, by
    rw [Multiset.toFinsupp_toMultiset]
    have he := congrArg Multiset.card (option_multiset_decomposition s.val)
    simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate, s.property] at he
    omega⟩

theorem encode_decode {α : Type*} [DecidableEq α] {k : ℕ} (s : Sym (Option α) k) :
    monomialCode k (decode s).val (decode s).property = s := by
  apply Subtype.ext
  have he := congrArg Multiset.card (option_multiset_decomposition s.val)
  simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate, s.property] at he
  simp only [monomialCode, decode, Multiset.toFinsupp_toMultiset]
  rw [show k - (s.val.filterMap id).card = s.val.count none by omega]
  exact option_multiset_decomposition s.val

def degreeEquivSym (α : Type*) [DecidableEq α] (k : ℕ) :
    DegreeSet α k ≃ Sym (Option α) k :=
  Equiv.ofBijective (fun d ↦ monomialCode k d.val d.property)
    ⟨monomialCode_injective k, fun s ↦ ⟨decode s, encode_decode s⟩⟩

instance degreeSetFintype (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype (DegreeSet α k) := Fintype.ofEquiv (Sym (Option α) k) (degreeEquivSym α k).symm

theorem degreeSet_card (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card (DegreeSet α k) = (Fintype.card α + k).choose k := by
  rw [Fintype.card_congr (degreeEquivSym α k), Sym.card_sym_eq_choose]
  simp [Nat.add_right_comm]

theorem degreeSet_fourteen_three_card : Fintype.card (DegreeSet (Fin 14) 3) = 680 := by
  rw [degreeSet_card]
  norm_num [Nat.choose]

def index : Fin 680 ≃ DegreeSet (Fin 14) 3 :=
  (Fintype.equivFinOfCardEq degreeSet_fourteen_three_card).symm

def exponent (j : Fin 680) : Fin 14 →₀ ℕ := (index j).val

theorem exponent_degree (j : Fin 680) : (exponent j).sum (fun _ k ↦ k) ≤ 3 := by
  simpa only [Finsupp.card_toMultiset, Function.id_def] using
    (show (exponent j).toMultiset.card ≤ 3 from (index j).property)

theorem exponent_injective : Function.Injective exponent := by
  intro i j hij
  apply index.injective
  exact Subtype.ext hij

theorem exponent_surjective (d : Fin 14 →₀ ℕ) (hd : d.sum (fun _ k ↦ k) ≤ 3) :
    ∃ j, exponent j = d := by
  have hc : d.toMultiset.card ≤ 3 := by
    simpa only [Finsupp.card_toMultiset, Function.id_def] using hd
  exact ⟨index.symm ⟨d, hc⟩, congrArg Subtype.val (index.apply_symm_apply _)⟩

def polynomial (q : Fin 680 → ℝ) : MvPolynomial (Fin 14) ℝ :=
  ∑ j, monomial (exponent j) (q j)

theorem polynomial_degree (q : Fin 680 → ℝ) : (polynomial q).totalDegree ≤ 3 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_monomial_le _ _).trans (exponent_degree j)

theorem polynomial_coefficient (q : Fin 680 → ℝ) (j : Fin 680) :
    (polynomial q).coeff (exponent j) = q j := by
  simp only [polynomial, coeff_sum, coeff_monomial]
  simp only [exponent_injective.eq_iff]
  simp

theorem polynomial_reconstruct (P : MvPolynomial (Fin 14) ℝ) (hP : P.totalDegree ≤ 3) :
    polynomial (fun j ↦ P.coeff (exponent j)) = P := by
  ext d
  by_cases hd : d.sum (fun _ k ↦ k) ≤ 3
  · obtain ⟨j, rfl⟩ := exponent_surjective d hd
    exact polynomial_coefficient _ _
  · have hd' : 3 < ∑ i ∈ d.support, d i := Nat.lt_of_not_ge hd
    have hp : P.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt (hP.trans_lt hd')
    have h := polynomial_degree (fun j ↦ P.coeff (exponent j))
    have hq : (polynomial (fun j ↦ P.coeff (exponent j))).coeff d = 0 :=
      coeff_eq_zero_of_totalDegree_lt (h.trans_lt hd')
    rw [hq, hp]

end
end HeadComplexity.CubicMonomialBasis
