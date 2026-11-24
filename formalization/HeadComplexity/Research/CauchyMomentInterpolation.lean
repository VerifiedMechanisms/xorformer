import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.WeightedAtom
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

set_option linter.style.header false

/-!
Exact finite-query reciprocal interpolation with prescribed initial moment
cancellation. The width is the number of queries plus the moment order plus
one; this is not a constant-overhead compiler for arbitrary narrow scores.
-/

noncomputable section
namespace HeadComplexity.CauchyMomentInterpolation
open Finset Polynomial
open scoped BigOperators

variable {L M D : ℕ}

def residue (a : Fin L → ℝ) (P : Polynomial ℝ) (j : Fin L) : ℝ :=
  Lagrange.nodalWeight univ (fun h ↦ -a h) j * P.eval (-a j)

/-- Barycentric partial fractions at negative poles. -/
theorem sum_residue_div (a : Fin L → ℝ) (ha : Function.Injective a)
    (P : Polynomial ℝ) (hP : P.degree < L) (t : ℝ)
    (ht : ∀ j, t + a j ≠ 0) :
    ∑ j, residue a P j / (t + a j) =
      P.eval t / ∏ j, (t + a j) := by
  classical
  have hi : Set.InjOn (fun j ↦ -a j) (univ : Finset (Fin L)) :=
    fun _ _ _ _ h ↦ ha (neg_injective h)
  have hdeg : P.degree < (univ : Finset (Fin L)).card := by simpa using hP
  have he := congrArg (Polynomial.eval t) (Lagrange.eq_interpolate hi hdeg)
  rw [Lagrange.eval_interpolate_not_at_node (fun j ↦ P.eval (-a j))] at he
  · simp only [Lagrange.eval_nodal, sub_neg_eq_add] at he
    have hn : (∏ j, (t + a j)) ≠ 0 := prod_ne_zero_iff.mpr (fun j _ ↦ ht j)
    apply (eq_div_iff hn).mpr
    calc
      _ = (∏ j, (t + a j)) *
          ∑ j, Lagrange.nodalWeight univ (fun h ↦ -a h) j *
            (t + a j)⁻¹ * P.eval (-a j) := by
        rw [mul_comm]
        congr 1
        apply sum_congr rfl
        intro j _
        simp only [residue, div_eq_mul_inv]
        ring
      _ = _ := he.symm
  · intro j _ h
    apply ht j
    linarith

/-- Vanishing high polynomial coefficients are exactly the initial signed
moments of the residue vector. -/
theorem residue_moment_zero (a : Fin L → ℝ) (ha : Function.Injective a)
    (P : Polynomial ℝ) (k : ℕ) (hdegree : P.natDegree + k < L - 1) :
    ∑ j, residue a P j * a j ^ k = 0 := by
  classical
  let Q : Polynomial ℝ := P * (-X) ^ k
  have hQ : Q.natDegree < L - 1 := by
    have hp := natDegree_mul_le (p := P) (q := (-X : Polynomial ℝ) ^ k)
    have hpow : ((-X : Polynomial ℝ) ^ k).natDegree ≤
        k * (-X : Polynomial ℝ).natDegree := natDegree_pow_le
    have hx : (-X : Polynomial ℝ).natDegree = 1 := by simp
    simp only [hx, mul_one] at hpow
    dsimp [Q]
    omega
  have hQL : Q.degree < (univ : Finset (Fin L)).card := by
    apply lt_of_le_of_lt (degree_le_natDegree)
    exact_mod_cast (show Q.natDegree < (univ : Finset (Fin L)).card by simp; omega)
  have hi : Set.InjOn (fun j ↦ -a j) (univ : Finset (Fin L)) :=
    fun _ _ _ _ h ↦ ha (neg_injective h)
  have he := Lagrange.coeff_eq_sum hi hQL
  have hc : Q.coeff ((univ : Finset (Fin L)).card - 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa using hQ
  rw [hc] at he
  calc
    _ = ∑ j, Q.eval (-a j) / ∏ i ∈ univ.erase j, (-a j - -a i) := by
      apply sum_congr rfl
      intro j _
      simp only [residue, Lagrange.nodalWeight, prod_inv_distrib, Q,
        eval_mul, eval_pow, eval_neg, eval_X, neg_neg, div_eq_mul_inv]
      ring
    _ = 0 := by simpa using he.symm

/-- Distinct positive scalar poles suffice to interpolate any finite real
score table and annihilate moments through `D`, using `M+D+1` poles. -/
theorem exists_residues (hM : 1 ≤ M) (t y : Fin M → ℝ)
    (ht : Function.Injective t) (htpos : ∀ i, 0 < t i)
    (a : Fin (M + D + 1) → ℝ) (ha : Function.Injective a)
    (hapos : ∀ j, 0 < a j) :
    ∃ c : Fin (M + D + 1) → ℝ,
      (∀ k ≤ D, ∑ j, c j * a j ^ k = 0) ∧
      (∀ i, ∑ j, c j / (t i + a j) = y i) := by
  classical
  let Q : ℝ → ℝ := fun z ↦ ∏ j, (z + a j)
  let P : Polynomial ℝ := Lagrange.interpolate univ t (fun i ↦ y i * Q (t i))
  have hi : Set.InjOn t (univ : Finset (Fin M)) := fun _ _ _ _ h ↦ ht h
  have hPdeg : P.degree ≤ (M - 1 : ℕ) := by
    simpa [P] using Lagrange.degree_interpolate_le (fun i ↦ y i * Q (t i)) hi
  have hPnat : P.natDegree ≤ M - 1 := natDegree_le_of_degree_le hPdeg
  have hPeval : ∀ i, P.eval (t i) = y i * Q (t i) := by
    intro i
    exact Lagrange.eval_interpolate_at_node _ hi (mem_univ i)
  refine ⟨residue a P, ?_, ?_⟩
  · intro k hk
    apply residue_moment_zero a ha P k
    omega
  · intro i
    have hp : P.degree < (M + D + 1 : ℕ) :=
      hPdeg.trans_lt (by exact_mod_cast (show M - 1 < M + D + 1 by omega))
    rw [sum_residue_div a ha P hp (t i) (fun j ↦ (add_pos (htpos i) (hapos j)).ne')]
    rw [hPeval]
    have hQ : Q (t i) ≠ 0 := prod_ne_zero_iff.mpr
      (fun j _ ↦ (add_pos (htpos i) (hapos j)).ne')
    exact mul_div_cancel_right₀ (y i) hQ

/-- Initial moment cancellation annihilates every polynomial of that degree. -/
theorem sum_polynomial_zero_of_moments (a c : Fin L → ℝ)
    (hz : ∀ k ≤ D, ∑ j, c j * a j ^ k = 0)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ D) :
    ∑ j, c j * P.eval (a j) = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro k hk
  have hkD : k ≤ D := (le_natDegree_of_ne_zero (mem_support_iff.mp hk)).trans hP
  calc
    _ = P.coeff k * ∑ j, c j * a j ^ k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hz k hkD, mul_zero]

/-- Moment cancellation is unchanged by translation of all scalar poles. -/
theorem translated_moment_zero (a c : Fin L → ℝ)
    (hz : ∀ k ≤ D, ∑ j, c j * a j ^ k = 0)
    (r : ℝ) (k : ℕ) (hk : k ≤ D) :
    ∑ j, c j * (r + a j) ^ k = 0 := by
  have hp : ((C r + X : Polynomial ℝ) ^ k).natDegree ≤ D := by
    have h := natDegree_pow_le (p := (C r + X : Polynomial ℝ)) (n := k)
    have hx : (C r + X : Polynomial ℝ).natDegree ≤ 1 := by
      apply natDegree_add_le_of_degree_le (by simp) (by simp)
    calc
      _ ≤ k * (C r + X : Polynomial ℝ).natDegree := h
      _ ≤ k * 1 := Nat.mul_le_mul_left _ hx
      _ ≤ D := by simpa using hk
  simpa using sum_polynomial_zero_of_moments a c hz ((C r + X) ^ k) hp

/-- Any real score table on the full Boolean cube has an exact representation
by `2^n + D + 1` admissible heads with scalar denominator moments through `D`
zero. This width is large; no narrow-repair claim is made. -/
theorem exists_original_heads_with_moment_cancellation (n D : ℕ)
    (S : (Fin n → Bool) → ℝ) :
    ∃ (c b : Fin (2 ^ n + D + 1) → ℝ)
      (lam : Fin n → ℝ) (atoms : Fin (2 ^ n + D + 1) → FracAtom n),
      (∀ j, 0 < b j) ∧ (∀ i, 0 < lam i) ∧
      (∀ j bits, (atoms j).eval bits = c j / affineValue (b j) lam bits) ∧
      (∀ k ≤ D, ∑ j, c j * b j ^ k = 0) ∧
      (∀ bits, ∑ j, (atoms j).eval bits = S bits) := by
  classical
  let e : (Fin n → Bool) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (by simp)
  let lam : Fin n → ℝ := fun i ↦ (2 : ℝ) ^ (i : ℕ)
  let t : Fin (2 ^ n) → ℝ := fun i ↦ 1 + wT lam (e.symm i)
  let a : Fin (2 ^ n + D + 1) → ℝ := fun j ↦ (j : ℕ) + 1
  have hM : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hlam : ∀ i, 0 < lam i := fun i ↦ by dsimp [lam]; positivity
  have ht : Function.Injective t := by
    intro i j hij
    apply e.symm.injective
    apply wT_two_pow_injective
    exact add_left_cancel hij
  have htpos : ∀ i, 0 < t i := by
    intro i
    dsimp [t, wT]
    have hn : 0 ≤ ∑ j, if e.symm i j then lam j else 0 :=
      sum_nonneg (fun j _ ↦ by split_ifs <;> positivity)
    linarith
  have ha : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel hij : (i.val : ℝ) = j.val)
  have hapos : ∀ j, 0 < a j := fun j ↦ by dsimp [a]; positivity
  obtain ⟨c, hm, hs⟩ := exists_residues (D := D) hM t (fun i ↦ S (e.symm i)) ht htpos a ha hapos
  let b := fun j ↦ 1 + a j
  have hb : ∀ j, 0 < b j := fun j ↦ add_pos zero_lt_one (hapos j)
  let atoms := fun j ↦ FracAtom.ofPositiveAffineRatio (c j) (fun _ ↦ 0) (b j) lam (hb j) hlam
  have heval : ∀ j bits, (atoms j).eval bits = c j / affineValue (b j) lam bits := by
    intro j bits
    simp [atoms, FracAtom.ofPositiveAffineRatio_eval, affineValue]
  refine ⟨c, b, lam, atoms, hb, hlam, heval, ?_, ?_⟩
  · intro k hk
    exact translated_moment_zero a c hm 1 k hk
  · intro bits
    rw [show S bits = S (e.symm (e bits)) by simp, ← hs (e bits)]
    apply sum_congr rfl
    intro j _
    rw [heval]
    congr 1
    simp only [affineValue, b, t, Equiv.symm_apply_apply, wT]
    have hsum : (∑ i, lam i * boolToReal (bits i)) = ∑ i, if bits i then lam i else 0 := by
      apply sum_congr rfl
      intro i _
      cases bits i <;> simp [boolToReal]
    rw [hsum]
    ring

end HeadComplexity.CauchyMomentInterpolation
