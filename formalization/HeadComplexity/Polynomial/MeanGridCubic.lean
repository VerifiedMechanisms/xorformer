import HeadComplexity.Polynomial.MeanGridSymmetrization

set_option linter.style.header false

/-!
# Averaging a cubic on replica groups

The finite-population moment polynomials give an explicit polynomial of the
same degree in the group means for every squarefree monomial of degree at most
three. The averaging is over arbitrary, independently permuted replica groups.
-/

namespace HeadComplexity.MeanGridCubic

noncomputable section

open Finset MvPolynomial
open scoped BigOperators
open MeanGridSymmetrization

def moment {n : ℕ} (m : ℕ) (i : Fin n) : ℕ → MvPolynomial (Fin n) ℝ
  | 0 => 1
  | 1 => X i
  | 2 => C ((m - 1 : ℝ)⁻¹) * (C (m : ℝ) * X i ^ 2 - 1)
  | _ => C (((m - 1 : ℝ) * (m - 2))⁻¹) *
      (C ((m : ℝ) ^ 2) * X i ^ 3 - C (3 * (m : ℝ) - 2) * X i)

theorem moment_degree {n : ℕ} (m : ℕ) (i : Fin n) (d : ℕ) :
    (moment m i d).totalDegree ≤ d := by
  rcases d with _ | _ | _ | d
  · simp [moment]
  · simp [moment]
  · simp only [moment]
    have h1 := totalDegree_pow (X i : MvPolynomial (Fin n) ℝ) 2
    have h2 := totalDegree_mul (C (m : ℝ)) (X i ^ 2 : MvPolynomial (Fin n) ℝ)
    have h3 := totalDegree_sub (C (m : ℝ) * X i ^ 2 : MvPolynomial (Fin n) ℝ) 1
    have h4 := totalDegree_mul (C ((m - 1 : ℝ)⁻¹))
      (C (m : ℝ) * X i ^ 2 - 1 : MvPolynomial (Fin n) ℝ)
    simp only [totalDegree_X, totalDegree_C, totalDegree_one, Nat.mul_one, zero_add] at *
    omega
  · simp only [moment]
    have h1 := totalDegree_pow (X i : MvPolynomial (Fin n) ℝ) 3
    have h2 := totalDegree_mul (C ((m : ℝ) ^ 2)) (X i ^ 3 : MvPolynomial (Fin n) ℝ)
    have h3 := totalDegree_mul (C (3 * (m : ℝ) - 2)) (X i : MvPolynomial (Fin n) ℝ)
    have h4 := totalDegree_sub (C ((m : ℝ) ^ 2) * X i ^ 3 : MvPolynomial (Fin n) ℝ)
      (C (3 * (m : ℝ) - 2) * X i)
    have h5 := totalDegree_mul (C (((m - 1 : ℝ) * (m - 2))⁻¹))
      (C ((m : ℝ) ^ 2) * X i ^ 3 - C (3 * (m : ℝ) - 2) * X i : MvPolynomial (Fin n) ℝ)
    simp only [totalDegree_X, totalDegree_C, Nat.mul_one, zero_add] at *
    omega

theorem average_set_eq_moment {n m : ℕ} (hm : 2 < m) (i : Fin n)
    (z : Fin m → ℝ) (hz : ∀ r, z r ^ 2 = 1) (S : Finset (Fin m))
    (hS : S.card ≤ 3) (v : Fin n → ℝ) (hv : v i = (∑ r, z r) / m) :
    average (fun σ : Equiv.Perm (Fin m) ↦ ∏ r ∈ S, z (σ r)) =
      eval v (moment m i S.card) := by
  have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hc with h | h | h | h
  · have hs := Finset.card_eq_zero.mp h
    simp [hs, average_const, moment]
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp h
    simp only [Finset.prod_singleton, Finset.card_singleton, moment, eval_X, hv]
    exact average_one_coordinate (by omega) z r
  · obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.mp h
    have hp (σ : Equiv.Perm (Fin m)) :
        (∏ a ∈ ({r, s} : Finset (Fin m)), z (σ a)) = z (σ r) * z (σ s) := by
      simp [hrs]
    simp_rw [hp]
    rw [h, average_two_mean_formula (by omega) z hz r s hrs]
    simp [moment, hv, div_eq_inv_mul]
  · obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := Finset.card_eq_three.mp h
    have hp (σ : Equiv.Perm (Fin m)) :
        (∏ a ∈ ({r, s, t} : Finset (Fin m)), z (σ a)) =
          z (σ r) * z (σ s) * z (σ t) := by
      simp [hrs, hrt, hst, mul_assoc]
    simp_rw [hp]
    rw [h, average_three_mean_formula hm z hz r s t hrs hrt hst]
    simp [moment, hv, div_eq_inv_mul]

def fibre {n m : ℕ} (S : Finset (Fin n × Fin m)) (i : Fin n) : Finset (Fin m) :=
  (S.filter (fun p ↦ p.1 = i)).image Prod.snd

theorem fibre_mem {n m : ℕ} (S : Finset (Fin n × Fin m)) (i : Fin n) (r : Fin m) :
    r ∈ fibre S i ↔ (i, r) ∈ S := by
  simp only [fibre, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨j, s⟩, ⟨hp, hij⟩, hsr⟩
    simpa only [Prod.fst, Prod.snd] using hij ▸ hsr ▸ hp
  · intro h
    exact ⟨(i, r), ⟨h, rfl⟩, rfl⟩

theorem fibre_card {n m : ℕ} (S : Finset (Fin n × Fin m)) (i : Fin n) :
    (fibre S i).card = (S.filter (fun p ↦ p.1 = i)).card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Prod.ext ((Finset.mem_filter.mp ha).2.trans
    (Finset.mem_filter.mp hb).2.symm) hab

theorem fibre_card_le {n m : ℕ} (S : Finset (Fin n × Fin m)) (i : Fin n) :
    (fibre S i).card ≤ S.card := by
  rw [fibre_card]
  exact Finset.card_filter_le _ _

theorem sum_fibre_card {n m : ℕ} (S : Finset (Fin n × Fin m)) :
    (∑ i : Fin n, (fibre S i).card) = S.card := by
  simp only [fibre_card]
  simpa using Finset.sum_card_fiberwise_eq_card_filter S Finset.univ Prod.fst

theorem prod_fibre {n m : ℕ} (S : Finset (Fin n × Fin m))
    (z : Fin n × Fin m → ℝ) :
    (∏ i : Fin n, ∏ r ∈ fibre S i, z (i, r)) = ∏ p ∈ S, z p := by
  have hi (i : Fin n) : (∏ r ∈ fibre S i, z (i, r)) =
      ∏ p ∈ S.filter (fun p ↦ p.1 = i), z p := by
    rw [fibre, Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro p hp
      congr 1
      exact Prod.ext (Finset.mem_filter.mp hp).2.symm rfl
    · intro a ha b hb hab
      exact Prod.ext ((Finset.mem_filter.mp ha).2.trans
        (Finset.mem_filter.mp hb).2.symm) hab
  simp_rw [hi]
  exact Finset.prod_fiberwise S Prod.fst z

def meanMonomial {n m : ℕ} (S : Finset (Fin n × Fin m)) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n, moment m i (fibre S i).card

theorem meanMonomial_degree {n m : ℕ} (S : Finset (Fin n × Fin m)) :
    (meanMonomial S).totalDegree ≤ S.card := by
  calc
    _ ≤ ∑ i : Fin n, (moment m i (fibre S i).card).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ i : Fin n, (fibre S i).card := Finset.sum_le_sum (fun i _ ↦ moment_degree _ _ _)
    _ = _ := sum_fibre_card S

theorem average_monomial_eq {n m : ℕ} (hm : 2 < m)
    (z : Fin n × Fin m → ℝ) (hz : ∀ p, z p ^ 2 = 1)
    (S : Finset (Fin n × Fin m)) (hS : S.card ≤ 3) :
    average (fun σ : Fin n → Equiv.Perm (Fin m) ↦
      ∏ p ∈ S, z (p.1, σ p.1 p.2)) =
        eval (fun i ↦ (∑ r, z (i, r)) / m) (meanMonomial S) := by
  simp_rw [← prod_fibre S]
  rw [average_product (fun i (τ : Equiv.Perm (Fin m)) ↦
    ∏ r ∈ fibre S i, z (i, τ r))]
  unfold meanMonomial
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact average_set_eq_moment hm i (fun r ↦ z (i, r)) (fun r ↦ hz (i, r))
    (fibre S i) ((fibre_card_le S i).trans hS) _ rfl


def oddSupport {α : Type*} (d : α →₀ ℕ) : Finset α :=
  d.support.filter (fun p ↦ d p % 2 = 1)

theorem power_on_spin (z : ℝ) (hz : z ^ 2 = 1) (d : ℕ) :
    z ^ d = if d % 2 = 1 then z else 1 := by
  conv_lhs => rw [← Nat.mod_add_div d 2, pow_add, pow_mul, hz, one_pow, mul_one]
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]

theorem monomial_on_spin {α : Type*} (d : α →₀ ℕ) (z : α → ℝ)
    (hz : ∀ p, z p ^ 2 = 1) :
    (∏ p ∈ d.support, z p ^ d p) = ∏ p ∈ oddSupport d, z p := by
  simp only [oddSupport, Finset.prod_filter, power_on_spin _ (hz _)]

theorem oddSupport_card_le {α : Type*} (d : α →₀ ℕ) :
    (oddSupport d).card ≤ d.sum (fun _ e ↦ e) := by
  calc
    _ ≤ d.support.card := Finset.card_filter_le _ _
    _ = ∑ _p ∈ d.support, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ p ∈ d.support, d p := Finset.sum_le_sum (fun p hp ↦
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
    _ = _ := rfl

theorem polynomial_on_spin {α : Type*} (P : MvPolynomial α ℝ)
    (z : α → ℝ) (hz : ∀ p, z p ^ 2 = 1) :
    eval z P = ∑ d ∈ P.support, P.coeff d * ∏ p ∈ oddSupport d, z p := by
  rw [eval_eq]
  exact Finset.sum_congr rfl (fun d _ ↦ by rw [monomial_on_spin d z hz])

def meanPolynomial {n m : ℕ} (P : MvPolynomial (Fin n × Fin m) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ d ∈ P.support, C (P.coeff d) * meanMonomial (oddSupport d)

theorem meanPolynomial_degree {n m : ℕ} (P : MvPolynomial (Fin n × Fin m) ℝ) :
    (meanPolynomial P).totalDegree ≤ P.totalDegree := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  calc
    _ ≤ (C (P.coeff d) : MvPolynomial (Fin n) ℝ).totalDegree +
        (meanMonomial (oddSupport d)).totalDegree := totalDegree_mul _ _
    _ = (meanMonomial (oddSupport d)).totalDegree := by rw [totalDegree_C, zero_add]
    _ ≤ (oddSupport d).card := meanMonomial_degree _
    _ ≤ d.sum (fun _ e ↦ e) := oddSupport_card_le d
    _ ≤ _ := le_totalDegree hd

theorem average_polynomial_eq {n m : ℕ} (hm : 2 < m)
    (P : MvPolynomial (Fin n × Fin m) ℝ) (hP : P.totalDegree ≤ 3)
    (z : Fin n × Fin m → ℝ) (hz : ∀ p, z p ^ 2 = 1) :
    average (fun σ : Fin n → Equiv.Perm (Fin m) ↦
      eval (fun p ↦ z (p.1, σ p.1 p.2)) P) =
        eval (fun i ↦ (∑ r, z (i, r)) / m) (meanPolynomial P) := by
  have he (σ : Fin n → Equiv.Perm (Fin m)) :
      eval (fun p ↦ z (p.1, σ p.1 p.2)) P =
        ∑ d ∈ P.support, P.coeff d * ∏ p ∈ oddSupport d, z (p.1, σ p.1 p.2) :=
    polynomial_on_spin P _ (fun p ↦ hz _)
  simp_rw [he]
  rw [average_finset_sum]
  unfold meanPolynomial
  rw [eval_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [average_mul, map_mul, eval_C,
    average_monomial_eq hm z hz (oddSupport d)
      ((oddSupport_card_le d).trans ((le_totalDegree hd).trans hP))]

/-- Arbitrary untied cubics have a degree-at-most-three mean-grid polynomial. -/
theorem cubic_mean_polynomial_exists {n m : ℕ} (hm : 2 < m)
    (P : MvPolynomial (Fin n × Fin m) ℝ) (hP : P.totalDegree ≤ 3) :
    ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ 3 ∧
      ∀ z : Fin n × Fin m → ℝ, (∀ p, z p ^ 2 = 1) →
        average (fun σ : Fin n → Equiv.Perm (Fin m) ↦
          eval (fun p ↦ z (p.1, σ p.1 p.2)) P) =
            eval (fun i ↦ (∑ r, z (i, r)) / m) Q :=
  ⟨meanPolynomial P, (meanPolynomial_degree P).trans hP,
    fun z hz ↦ average_polynomial_eq hm P hP z hz⟩


def spin {α : Type*} (x : α → Bool) (p : α) : ℝ := if x p then 1 else -1

theorem spin_square {α : Type*} (x : α → Bool) (p : α) : spin x p ^ 2 = 1 := by
  cases h : x p <;> norm_num [spin, h]

theorem cubic_mean_sign_exists {n m : ℕ} (hm : 2 < m)
    (f : (Fin n × Fin m → Bool) → Bool)
    (hf : ∀ x σ, f (permuted x σ) = f x)
    (P : MvPolynomial (Fin n × Fin m) ℝ) (hP : P.totalDegree ≤ 3)
    (hPf : ∀ x, 0 < eval (spin x) P ↔ f x = true) :
    ∃ Q : MvPolynomial (Fin n) ℝ, Q.totalDegree ≤ 3 ∧
      ∀ x, 0 < eval (fun i ↦ (∑ r, spin x (i, r)) / m) Q ↔ f x = true := by
  refine ⟨meanPolynomial P, (meanPolynomial_degree P).trans hP, ?_⟩
  intro x
  rw [← average_polynomial_eq hm P hP (spin x) (spin_square x)]
  apply average_sign
  intro σ
  change 0 < eval (spin (permuted x σ)) P ↔ f x = true
  rw [hPf, hf]

end

end HeadComplexity.MeanGridCubic
