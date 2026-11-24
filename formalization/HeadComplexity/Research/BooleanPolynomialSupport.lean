import HeadComplexity.Atoms.ClearedNormalForm
import Mathlib.Algebra.MvPolynomial.Equiv

set_option linter.style.header false

/-!
A nonzero Boolean restriction of a degree-d polynomial has support at least
2^(n-d). Clearing positive denominators transfers this exact localization
obstruction to unrestricted original-model scores.
-/
noncomputable section
namespace HeadComplexity.BooleanPolynomialSupport
open Finset MvPolynomial
open scoped BigOperators

/-- Number of cube rows on which a real-valued function is nonzero. -/
def supportSize {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℕ :=
  ∑ x, if f x = 0 then 0 else 1

private def splitEquiv (n : ℕ) :
    (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by cases p; rfl

theorem supportSize_split {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    supportSize f = supportSize (fun x => f (Fin.cons false x)) +
      supportSize (fun x => f (Fin.cons true x)) := by
  classical
  unfold supportSize
  rw [Fintype.sum_equiv (splitEquiv n) _
    (fun p => if f (Fin.cons p.1 p.2) = 0 then 0 else 1)]
  · simp [Fintype.sum_prod_type, add_comm]
  · intro x
    change _ = if f ((splitEquiv n).symm ((splitEquiv n) x)) = 0 then 0 else 1
    rw [Equiv.symm_apply_apply]

theorem supportSize_sub_le {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    supportSize (fun x => f x - g x) ≤ supportSize f + supportSize g := by
  classical
  unfold supportSize
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases hf : f x = 0 <;> by_cases hg : g x = 0 <;> simp [hf, hg]
  split <;> omega

theorem supportSize_pos {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∃ x, f x ≠ 0) : 1 ≤ supportSize f := by
  classical
  rcases hf with ⟨x,hx⟩
  have h := Finset.single_le_sum (f := fun y => if f y = 0 then 0 else 1)
    (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  simpa [supportSize, hx] using h

private theorem cubePoint_cons {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    cubePoint (Fin.cons b x) = Fin.cons (boolToReal b) (cubePoint x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private def zeroSlice {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ := (finSuccEquiv ℝ n P).coeff 0

private def differenceSlice {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ k ∈ (finSuccEquiv ℝ n P).support.erase 0, (finSuccEquiv ℝ n P).coeff k

private theorem eval_zeroSlice {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (x : Fin n → Bool) :
    eval (cubePoint (Fin.cons false x)) P = eval (cubePoint x) (zeroSlice P) := by
  rw [cubePoint_cons, eval_eq_eval_mv_eval']
  simp [boolToReal, zeroSlice, ← Polynomial.coeff_zero_eq_eval_zero]

private theorem eval_oneSlice {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (x : Fin n → Bool) :
    eval (cubePoint (Fin.cons true x)) P =
      eval (cubePoint x) (zeroSlice P) + eval (cubePoint x) (differenceSlice P) := by
  classical
  rw [cubePoint_cons, eval_eq_eval_mv_eval']
  simp only [boolToReal, ↓reduceIte]
  rw [Polynomial.eval_map, Polynomial.eval₂_at_one]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  rw [← map_add]
  congr 1
  unfold zeroSlice differenceSlice
  by_cases h0 : 0 ∈ (finSuccEquiv ℝ n P).support
  · exact (Finset.add_sum_erase _ _ h0).symm
  · rw [Finset.erase_eq_of_notMem h0]
    have hz : (finSuccEquiv ℝ n P).coeff 0 = 0 :=
      Polynomial.notMem_support_iff.mp h0
    simp [hz]

private theorem zeroSlice_degree {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ d) : (zeroSlice P).totalDegree ≤ d := by
  by_cases h : (finSuccEquiv ℝ n P).coeff 0 = 0
  · simp [zeroSlice,h]
  · have hh := totalDegree_coeff_finSuccEquiv_add_le P 0 h
    simpa [zeroSlice] using hh.trans hP

private theorem differenceSlice_degree {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ d) : (differenceSlice P).totalDegree ≤ d-1 := by
  classical
  apply totalDegree_finsetSum_le
  intro k hk
  have hk0 := (mem_erase.mp hk).1
  have hkP := Polynomial.mem_support_iff.mp (mem_erase.mp hk).2
  have h := totalDegree_coeff_finSuccEquiv_add_le P k hkP
  omega

/-- Boolean minimum support bound. It is stated without truncated subtraction,
so it also covers degrees larger than the dimension. -/
theorem two_pow_le_degree_mul_support {n d : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ d)
    (hne : ∃ x, eval (cubePoint x) P ≠ 0) :
    2^n ≤ 2^d * supportSize (fun x => eval (cubePoint x) P) := by
  classical
  induction n generalizing d with
  | zero =>
    have hs := supportSize_pos hne
    have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
    simpa using Nat.mul_le_mul hp hs
  | succ n ih =>
    by_cases hd : d = 0
    · subst d
      have hP0 : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hP
      rw [totalDegree_eq_zero_iff_eq_C] at hP0
      rw [hP0] at hne ⊢
      rcases hne with ⟨x,hx⟩
      simp only [eval_C] at hx ⊢
      simp [supportSize, hx]
    · let f0 : (Fin n → Bool) → ℝ := fun x => eval (cubePoint (Fin.cons false x)) P
      let f1 : (Fin n → Bool) → ℝ := fun x => eval (cubePoint (Fin.cons true x)) P
      have he0 : (fun x => eval (cubePoint x) (zeroSlice P)) = f0 := by
        funext x
        exact (eval_zeroSlice P x).symm
      have heD : (fun x => eval (cubePoint x) (differenceSlice P)) =
          (fun x => f1 x - f0 x) := by
        funext x
        dsimp [f0,f1]
        rw [eval_zeroSlice,eval_oneSlice]
        ring
      have hs : supportSize (fun x => eval (cubePoint x) P) =
          supportSize f0 + supportSize f1 := supportSize_split _
      by_cases hD : ∃ x, eval (cubePoint x) (differenceSlice P) ≠ 0
      · have hi := ih (differenceSlice P) (differenceSlice_degree P hP) hD
        rw [heD] at hi
        have hsub := supportSize_sub_le f1 f0
        have hi' := hi.trans (Nat.mul_le_mul_left (2^(d-1)) hsub)
        have hp : 2^d = 2 * 2^(d-1) := by
          conv_lhs => rw [show d = (d-1)+1 by omega]
          rw [pow_succ, Nat.mul_comm]
        rw [hs,pow_succ,hp]
        nlinarith
      · have heq : f1 = f0 := by
          funext x
          have hz : eval (cubePoint x) (differenceSlice P) = 0 :=
            not_ne_iff.mp (fun hx => hD ⟨x,hx⟩)
          have hh := congrFun heD x
          rw [hz] at hh
          linarith
        have hn0 : ∃ x, eval (cubePoint x) (zeroSlice P) ≠ 0 := by
          rcases hne with ⟨x,hx⟩
          refine ⟨fun i => x i.succ, ?_⟩
          have hex : Fin.cons (x 0) (fun i => x i.succ) = x := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> rfl
          cases hbit : x 0
          · rw [← eval_zeroSlice, ← hbit, hex]
            exact hx
          · have hv := congrFun heq (fun i => x i.succ)
            dsimp [f0,f1] at hv
            rw [← hbit, hex] at hv
            rw [← eval_zeroSlice, ← hv]
            exact hx
        have hi := ih (zeroSlice P) (zeroSlice_degree P hP) hn0
        rw [he0] at hi
        rw [hs,heq,pow_succ]
        nlinarith

/-- Equivalent minimum-support form when the degree does not exceed dimension. -/
theorem supportSize_ge_two_pow_sub {n d : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ d) (hd : d ≤ n)
    (hne : ∃ x, eval (cubePoint x) P ≠ 0) :
    2^(n-d) ≤ supportSize (fun x => eval (cubePoint x) P) := by
  have h := two_pow_le_degree_mul_support P hP hne
  have hn : n = d + (n-d) := by omega
  have hp : 2^n = 2^d * 2^(n-d) := by
    conv_lhs => rw [hn]
    rw [pow_add]
  rw [hp] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

/-- Positive denominator clearing preserves exact support. -/
theorem atom_score_support_bound {n H : ℕ} (φ : Fin H → FracAtom n) (c : ℝ)
    (hne : ∃ x, c + ∑ h, (φ h).eval x ≠ 0) :
    2^n ≤ 2^H * supportSize (fun x => c + ∑ h, (φ h).eval x) := by
  classical
  have hs : supportSize (fun x => eval (cubePoint x) (clearedAtomPoly φ c)) =
      supportSize (fun x => c + ∑ h, (φ h).eval x) := by
    unfold supportSize
    apply sum_congr rfl
    intro x _
    dsimp only
    simp [clearedAtomPoly_eval, (atomDenProduct_eval_pos φ x).ne']
  have hp : ∃ x, eval (cubePoint x) (clearedAtomPoly φ c) ≠ 0 := by
    rcases hne with ⟨x,hx⟩
    refine ⟨x, ?_⟩
    rw [clearedAtomPoly_eval]
    exact mul_ne_zero (atomDenProduct_eval_pos φ x).ne' hx
  simpa [hs] using two_pow_le_degree_mul_support (clearedAtomPoly φ c)
    (clearedAtomPoly_totalDegree_le φ c) hp

open scoped InnerProductSpace

/-- Exact localization bound stated directly for original attention-head readouts,
with arbitrary dimension, parameters, real bias, and signed cancellation. -/
theorem original_score_support_bound {n H d : ℕ} (heads : Fin H → Head n d)
    (w : Vec d) (c : ℝ)
    (hne : ∃ x, c + ∑ h, ⟪w, (heads h).attnUpdate x⟫_ℝ ≠ 0) :
    2^n ≤ 2^H * supportSize (fun x => c + ∑ h, ⟪w, (heads h).attnUpdate x⟫_ℝ) := by
  simpa only [← head_readout_eq_eval] using
    atom_score_support_bound (fun h => headToAtom (heads h) w) c
      (by simpa only [← head_readout_eq_eval] using hne)

/-- In particular, one genuine nonzero head score cannot have exact support
smaller than half of the Boolean cube. -/
theorem one_head_support_bound {n d : ℕ} (head : Head n d) (w : Vec d) (c : ℝ)
    (hne : ∃ x, c + ⟪w, head.attnUpdate x⟫_ℝ ≠ 0) :
    2^n ≤ 2 * supportSize (fun x => c + ⟪w, head.attnUpdate x⟫_ℝ) := by
  simpa using original_score_support_bound (fun _ : Fin 1 => head) w c
    (by simpa using hne)

end HeadComplexity.BooleanPolynomialSupport
