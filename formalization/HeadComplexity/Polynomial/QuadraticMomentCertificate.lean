import HeadComplexity.Polynomial.ThresholdDegree
import Mathlib.Data.Finsupp.Multiset

set_option linter.style.header false

namespace HeadComplexity.QuadraticMomentCertificate

open MvPolynomial
open scoped BigOperators

theorem exponent_le_two {σ : Type*} (d : σ →₀ ℕ)
    (hd : d.sum (fun _ a ↦ a) ≤ 2) :
    d = 0 ∨ (∃ i, d = Finsupp.single i 1) ∨
      ∃ i j, d = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  have hc : d.toMultiset.card ≤ 2 := by simpa [Function.id_def] using hd
  interval_cases he : d.toMultiset.card
  · left
    have hh := congrArg Multiset.toFinsupp (Multiset.card_eq_zero.mp he)
    simpa using hh
  · right
    left
    obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp he
    exact ⟨i, by simpa using congrArg Multiset.toFinsupp hi⟩
  · right
    right
    obtain ⟨i, j, hij⟩ := Multiset.card_eq_two.mp he
    refine ⟨i, j, ?_⟩
    have hh := congrArg Multiset.toFinsupp hij
    change Multiset.toFinsupp (Finsupp.toMultiset d) = Multiset.toFinsupp (i ::ₘ {j}) at hh
    rw [← Multiset.singleton_add] at hh
    rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      Multiset.toFinsupp_singleton, Finsupp.toMultiset_toFinsupp] at hh
    exact hh

theorem eval_sum_eq_of_moments {σ I : Type*} [Fintype I]
    (x y : I → σ → ℝ)
    (h1 : ∀ j, ∑ i, x i j = ∑ i, y i j)
    (h2 : ∀ j k, ∑ i, x i j * x i k = ∑ i, y i j * y i k)
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2) :
    ∑ i, eval (x i) P = ∑ i, eval (y i) P := by
  classical
  have hs (v : σ → ℝ) (j : σ) :
      (Finsupp.single j 1).prod (fun n e ↦ v n ^ e) = v j := by
    simpa only [pow_one] using
      (Finsupp.prod_single_index (a := j) (b := 1) (h := fun n e ↦ v n ^ e) (pow_zero (v j)))
  have hm (d : σ →₀ ℕ) (hd : d ∈ P.support) :
      ∑ i, eval (x i) (monomial d (P.coeff d)) =
        ∑ i, eval (y i) (monomial d (P.coeff d)) := by
    have hdeg := (le_totalDegree hd).trans hP
    rcases exponent_le_two d hdeg with rfl | ⟨j, rfl⟩ | ⟨j, k, rfl⟩
    · simp
    · simp only [eval_monomial, hs]
      rw [← Finset.mul_sum, ← Finset.mul_sum, h1]
    · simp only [eval_monomial, Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ ↦ pow_add _),
        hs]
      rw [← Finset.mul_sum, ← Finset.mul_sum, h2]
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  exact Finset.sum_congr rfl hm

theorem complement_moments {n : ℕ} {I : Type*} [Fintype I]
    (x : I → Fin n → Bool)
    (hx : ∀ j, ∑ i, boolToReal (x i j) = (Fintype.card I : ℝ) / 2) :
    (∀ j, ∑ i, boolToReal (x i j) = ∑ i, boolToReal (!(x i j))) ∧
      ∀ j k, ∑ i, boolToReal (x i j) * boolToReal (x i k) =
        ∑ i, boolToReal (!(x i j)) * boolToReal (!(x i k)) := by
  have hb (b : Bool) : boolToReal (!b) = 1 - boolToReal b := by
    cases b <;> norm_num [boolToReal]
  constructor
  · intro j
    simp_rw [hb]
    rw [Finset.sum_sub_distrib, hx]
    simp
    ring
  · intro j k
    have he (i : I) : boolToReal (!(x i j)) * boolToReal (!(x i k)) =
        boolToReal (x i j) * boolToReal (x i k) -
          boolToReal (x i j) - boolToReal (x i k) + 1 := by
      rw [hb, hb]
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hx, hx]
    simp
    ring

/-- A balanced family of positive inputs whose complements are all negative
is an exact obstruction to every quadratic threshold representation. -/
theorem not_thresholdDegLE_two {n : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (f : (Fin n → Bool) → Bool) (x : I → Fin n → Bool)
    (hx : ∀ j, ∑ i, boolToReal (x i j) = (Fintype.card I : ℝ) / 2)
    (hp : ∀ i, f (x i) = true) (hn : ∀ i, f (fun j ↦ !(x i j)) = false) :
    ¬ ThresholdDegLE f 2 := by
  classical
  rintro ⟨P, hdeg, hsign⟩
  obtain ⟨h1, h2⟩ := complement_moments x hx
  have he := eval_sum_eq_of_moments (fun i ↦ cubePoint (x i))
    (fun i ↦ cubePoint (fun j ↦ !(x i j))) h1 h2 P hdeg
  have hpos : 0 < ∑ i, eval (cubePoint (x i)) P := by
    apply Finset.sum_pos
    · intro i _
      exact (hsign _).mpr (hp i)
    · exact Finset.univ_nonempty
  have hneg : (∑ i, eval (cubePoint (fun j ↦ !(x i j))) P) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply le_of_not_gt
    intro hi
    have hh := (hsign _).mp hi
    rw [hn i] at hh
    cases hh
  linarith

end HeadComplexity.QuadraticMomentCertificate
