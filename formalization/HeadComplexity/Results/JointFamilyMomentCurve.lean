import HeadComplexity.Results.ReverseMomentGerms
import Mathlib.Combinatorics.Pigeonhole

set_option linter.style.header false

/-!
# Large permutation fibers with shared moment-curve jets

A degree-k moment curve reduces all input-polynomial jets through order d
to only (kd+1)(d+1) integer mixed moments. The large-fiber theorem is an
entropy statement, not a claim of strict orthant coverage.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

noncomputable def jointFamilyMixedMoment {H : ℕ} (π : Equiv.Perm (Fin H))
    (a b : ℕ) : ℕ := ∑ h : Fin H, (h.val + 1) ^ a * ((π h).val + 1) ^ b

theorem jointFamilyMixedMoment_bound {H k d : ℕ} (hH : 0 < H)
    (π : Equiv.Perm (Fin H)) (a b : ℕ) (ha : a ≤ k * d) (hb : b ≤ d) :
    jointFamilyMixedMoment π a b ≤ H ^ ((k + 1) * d + 1) := by
  have he : a + b + 1 ≤ (k + 1) * d + 1 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  calc
    jointFamilyMixedMoment π a b ≤ ∑ _h : Fin H, H ^ (a + b) := by
      apply Finset.sum_le_sum
      intro h _
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : h.val + 1 ≤ H) a)
        (Nat.pow_le_pow_left (by have := (π h).isLt; omega : (π h).val + 1 ≤ H) b)
    _ = H ^ (a + b + 1) := by simp [pow_succ, Nat.mul_comm]
    _ ≤ H ^ ((k + 1) * d + 1) := Nat.pow_le_pow_right hH he

noncomputable def jointFamilyMomentSignature {H : ℕ} (k d : ℕ) (hH : 0 < H)
    (π : Equiv.Perm (Fin H)) :
    (Fin (k * d + 1) × Fin (d + 1)) → Fin (H ^ ((k + 1) * d + 1) + 1) :=
  fun ab ↦ ⟨jointFamilyMixedMoment π ab.1.val ab.2.val,
    Nat.lt_succ_of_le (jointFamilyMixedMoment_bound hH π _ _
      (Nat.le_of_lt_succ ab.1.isLt) (Nat.le_of_lt_succ ab.2.isLt))⟩

/-- An explicit lower bound on a fiber of the shared low-moment signature.
For k,d polynomially bounded and H exponential in k, the loss in the
exponent is polynomial in k,d, rather than exponential in k. -/
theorem jointFamily_large_moment_fiber (H k d L : ℕ) (hH : 0 < H)
    (hcount : (H ^ ((k + 1) * d + 1) + 1) ^ ((k * d + 1) * (d + 1)) * L ≤
      H.factorial) :
    ∃ C : Finset (Equiv.Perm (Fin H)), L ≤ C.card ∧
      ∀ π ∈ C, ∀ σ ∈ C, jointFamilyMomentSignature k d hH π =
        jointFamilyMomentSignature k d hH σ := by
  classical
  obtain ⟨y, hy⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (jointFamilyMomentSignature k d hH) (n := L) (by
      simpa [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_perm] using hcount)
  refine ⟨Finset.univ.filter (fun π ↦ jointFamilyMomentSignature k d hH π = y),
    hy, ?_⟩
  intro π hπ σ hσ
  exact (Finset.mem_filter.mp hπ).2.trans (Finset.mem_filter.mp hσ).2.symm

/-- Equality of mixed moments allows any bounded-degree polynomial in the
row parameter, simultaneously for every memory power. -/
theorem jointFamily_equal_moments_polynomial {H A d : ℕ}
    (u v : Fin H → ℝ)
    (hm : ∀ a ≤ A, ∀ b ≤ d,
      (∑ h : Fin H, (h.val + 1 : ℝ) ^ a * u h ^ b) =
        ∑ h : Fin H, (h.val + 1 : ℝ) ^ a * v h ^ b)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ A) (b : ℕ) (hb : b ≤ d) :
    (∑ h : Fin H, P.eval (h.val + 1 : ℝ) * u h ^ b) =
      ∑ h : Fin H, P.eval (h.val + 1 : ℝ) * v h ^ b := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro a ha
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hm a (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) b hb]

/-- All degree-k row polynomials share their power-sum jets through order d
on one mixed-moment fiber. The same equality holds for arbitrary real row
coefficients, so it applies in particular to every Boolean row input. -/
theorem jointFamily_equal_moments_power_sums {H k d : ℕ}
    (u v : Fin H → ℝ)
    (hm : ∀ a ≤ k * d, ∀ b ≤ d,
      (∑ h : Fin H, (h.val + 1 : ℝ) ^ a * u h ^ b) =
        ∑ h : Fin H, (h.val + 1 : ℝ) ^ a * v h ^ b)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ k) (r : ℕ) (hr : r ≤ d) :
    (∑ h : Fin H, (P.eval (h.val + 1 : ℝ) + u h) ^ r) =
      ∑ h : Fin H, (P.eval (h.val + 1 : ℝ) + v h) ^ r := by
  classical
  simp_rw [add_pow]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro m hmrange
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  have hmle : m ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hmrange)
  have hdeg : (P ^ m).natDegree ≤ k * d := by
    calc
      (P ^ m).natDegree ≤ m * P.natDegree := Polynomial.natDegree_pow_le
      _ ≤ d * k := Nat.mul_le_mul (hmle.trans hr) hP
      _ = k * d := Nat.mul_comm _ _
  simpa using jointFamily_equal_moments_polynomial u v hm (P ^ m) hdeg
    (r - m) ((Nat.sub_le _ _).trans hr)

theorem jointFamily_same_signature_power_sums {H k d : ℕ} (hH : 0 < H)
    (π σ : Equiv.Perm (Fin H))
    (hsig : jointFamilyMomentSignature k d hH π = jointFamilyMomentSignature k d hH σ)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ k) (r : ℕ) (hr : r ≤ d) :
    (∑ h : Fin H, (P.eval (h.val + 1 : ℝ) + ((π h).val + 1 : ℝ)) ^ r) =
      ∑ h : Fin H, (P.eval (h.val + 1 : ℝ) + ((σ h).val + 1 : ℝ)) ^ r := by
  apply jointFamily_equal_moments_power_sums _ _ _ P hP r hr
  intro a ha b hb
  have heq := congrArg Fin.val (congrFun hsig
    (⟨a, Nat.lt_succ_of_le ha⟩, ⟨b, Nat.lt_succ_of_le hb⟩))
  change jointFamilyMixedMoment π a b = jointFamilyMixedMoment σ a b at heq
  unfold jointFamilyMixedMoment at heq
  exact_mod_cast heq

/-- The common jets cancel in the exact reciprocal difference. No asymptotic
expansion or exchange of limits is needed. -/
theorem jointFamily_same_signature_remainder {H k d : ℕ} (hH : 0 < H)
    (π σ : Equiv.Perm (Fin H))
    (hsig : jointFamilyMomentSignature k d hH π = jointFamilyMomentSignature k d hH σ)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ k) (t ε : ℝ) (ht : t ≠ 0)
    (hπ : ∀ h, t - ε * (P.eval (h.val + 1 : ℝ) + ((π h).val + 1 : ℝ)) ≠ 0)
    (hσ : ∀ h, t - ε * (P.eval (h.val + 1 : ℝ) + ((σ h).val + 1 : ℝ)) ≠ 0) :
    (∑ h : Fin H, 1 / (t - ε * (P.eval (h.val + 1 : ℝ) + ((π h).val + 1 : ℝ)))) -
      (∑ h : Fin H, 1 / (t - ε * (P.eval (h.val + 1 : ℝ) + ((σ h).val + 1 : ℝ)))) =
      (ε / t) ^ (d + 1) *
        ((∑ h : Fin H, (P.eval (h.val + 1 : ℝ) + ((π h).val + 1 : ℝ)) ^ (d + 1) /
          (t - ε * (P.eval (h.val + 1 : ℝ) + ((π h).val + 1 : ℝ)))) -
         (∑ h : Fin H, (P.eval (h.val + 1 : ℝ) + ((σ h).val + 1 : ℝ)) ^ (d + 1) /
          (t - ε * (P.eval (h.val + 1 : ℝ) + ((σ h).val + 1 : ℝ))))) := by
  let a : Fin (H + H) → ℝ := Fin.addCases (fun _ ↦ 1) (fun _ ↦ -1)
  let p : Fin (H + H) → ℝ := Fin.addCases
    (fun h ↦ P.eval (h.val + 1 : ℝ) + ((π h).val + 1 : ℝ))
    (fun h ↦ P.eval (h.val + 1 : ℝ) + ((σ h).val + 1 : ℝ))
  have hd : ∀ h, t - ε * p h ≠ 0 := by
    intro h
    refine Fin.addCases ?_ ?_ h
    · intro i
      simpa only [p, Fin.addCases_left] using hπ i
    · intro i
      simpa only [p, Fin.addCases_right] using hσ i
  have hm : ∀ l < d + 1, ∑ h, a h * p h ^ l = 0 := by
    intro l hl
    simp only [a, p, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      one_mul, neg_one_mul, Finset.sum_neg_distrib]
    rw [jointFamily_same_signature_power_sums hH π σ hsig P hP l
      (Nat.le_of_lt_succ hl)]
    exact add_neg_cancel _
  simpa only [a, p, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    one_mul, neg_one_mul, neg_div, Finset.sum_neg_distrib, sub_eq_add_neg] using
    cauchy_moment_remainder a p (d + 1) t ε ht hd hm

end HeadComplexity.AxisZeroGluing
