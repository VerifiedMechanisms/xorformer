import HeadComplexity.Atoms.PartialFraction
import HeadComplexity.Results.AffineFractionNormalForm
import HeadComplexity.Foundation.FiniteSignMargin
import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.style.header false

/-!
# Polynomial thresholds of arbitrary affine statistics

The statistic may have positive, negative, and zero coefficients. A strict
polynomial sign representation of degree at most H can be computed by H vanilla
heads. The construction uses a small projective perturbation and partial
fractions, while keeping all vanilla denominator slopes strictly positive.
-/

namespace HeadComplexity

open scoped BigOperators Topology
open Polynomial

/-- A finite family of continuous strict scores retains all signs at some
positive parameter smaller than any prescribed positive upper bound. -/
theorem exists_pos_lt_sign_preserving {α : Type*} [Finite α]
    (S : ℝ → α → ℝ) (hcont : ∀ x, ContinuousAt (fun t ↦ S t x) 0)
    (hne : ∀ x, S 0 x ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ t < a ∧ ∀ x,
      (0 < S t x ↔ 0 < S 0 x) ∧ S t x ≠ 0 := by
  obtain ⟨δ, hδ, hstable⟩ := exists_sign_stability_margin (S 0) hne
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x, |S t x - S 0 x| < δ := by
    apply Filter.eventually_all.mpr
    intro x
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp (hcont x).tendsto) δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let t := min r a / 2
  have ht : 0 < t := div_pos (lt_min hr ha) (by norm_num)
  have htr : t < r := by dsimp [t]; linarith [min_le_left r a]
  have hta : t < a := by dsimp [t]; linarith [min_le_right r a]
  exact ⟨t, ht, hta, hstable (S t)
    (hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htr))⟩

namespace AffineStatistic

variable {n H : ℕ}

noncomputable def eval (w : Fin n → ℝ) (b : ℝ) (x : Fin n → Bool) : ℝ :=
  b + ∑ i, w i * boolToReal (x i)

noncomputable def base (t : ℝ) (x : Fin n → Bool) : ℝ :=
  1 + t * ∑ i, boolToReal (x i)

theorem base_pos (t : ℝ) (ht : 0 ≤ t) (x : Fin n → Bool) :
    0 < base t x := by
  have hs : 0 ≤ ∑ i, boolToReal (x i) := by
    apply Finset.sum_nonneg
    intro i _
    cases x i <;> norm_num [boolToReal]
  unfold base
  positivity

/-- The partial-fraction polynomial identity divided by its positive factors. -/
private theorem partial_fraction_score (P : ℝ[X]) (av : Fin H → ℝ)
    (hinj : Function.Injective av) (hdeg : P.natDegree ≤ H) :
    ∃ (A : ℝ) (bv : Fin H → ℝ), ∀ y : ℝ,
      (∀ h, 0 < y + av h) →
      A + ∑ h, bv h / (y + av h) = P.eval y / ∏ h, (y + av h) := by
  classical
  obtain ⟨A, bv, hpf⟩ := real_partial_fraction P av hinj hdeg
  refine ⟨A, bv, fun y hy ↦ ?_⟩
  have hprod : (∏ h, (y + av h)) ≠ 0 :=
    (Finset.prod_pos fun h _ ↦ hy h).ne'
  apply (eq_div_iff hprod).mpr
  rw [add_mul, Finset.sum_mul, hpf]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ y + av j) (Finset.mem_univ h)]
  field_simp [(hy h).ne']

/-- Every strict univariate polynomial threshold on an arbitrary affine
statistic is computable with its degree bound many vanilla heads. -/
theorem computable_of_strict_polynomial (w : Fin n → ℝ) (b : ℝ)
    (P : ℝ[X]) (hdeg : P.natDegree ≤ H) (f : (Fin n → Bool) → Bool)
    (hsign : ∀ x, (0 < P.eval (eval w b x) ↔ f x = true))
    (hne : ∀ x, P.eval (eval w b x) ≠ 0) :
    computableWithSharedHeadsN n H f := by
  classical
  let S (t : ℝ) (x : Fin n → Bool) := P.eval (eval w b x / base t x)
  have hcont (x : Fin n → Bool) : ContinuousAt (fun t ↦ S t x) 0 := by
    apply P.continuousAt.comp
    apply continuousAt_const.div
    · exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    · norm_num [base]
  have hS0 (x : Fin n → Bool) : S 0 x = P.eval (eval w b x) := by
    simp [S, base]
  obtain ⟨t, ht, ht1, hstable⟩ := exists_pos_lt_sign_preserving S hcont
    (fun x ↦ by simpa only [hS0] using hne x) 1 (by norm_num)
  let av (h : Fin H) : ℝ := 2 + |b| + ∑ i, |w i| + (h : ℕ)
  have havinj : Function.Injective av := by
    intro h j heq
    exact Fin.ext (Nat.cast_inj.mp (add_left_cancel heq))
  have havb (h : Fin H) : |b| < av h := by
    have hw : 0 ≤ ∑ i, |w i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    have hh : (0 : ℝ) ≤ (h : ℕ) := Nat.cast_nonneg _
    dsimp [av]
    linarith
  have havw (h : Fin H) (i : Fin n) : -w i < av h := by
    have hi : |w i| ≤ ∑ j, |w j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (w j)) (Finset.mem_univ i)
    have hb : 0 ≤ |b| := abs_nonneg b
    have hh : (0 : ℝ) ≤ (h : ℕ) := Nat.cast_nonneg _
    dsimp [av]
    linarith [neg_le_abs (w i)]
  have hconst (h : Fin H) : 0 < t * b + av h := by
    have htb : -|b| ≤ t * b := by
      by_cases hb : 0 ≤ b
      · exact (neg_nonpos.mpr (abs_nonneg b)).trans (mul_nonneg ht.le hb)
      · rw [abs_of_neg (lt_of_not_ge hb)]
        nlinarith
    linarith [havb h]
  let Q : ℝ[X] := P.comp (Polynomial.C t⁻¹ * Polynomial.X)
  have hQdeg : Q.natDegree ≤ H := by
    apply Polynomial.natDegree_comp_le.trans
    have hlin : (Polynomial.C t⁻¹ * Polynomial.X : ℝ[X]).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    exact (Nat.mul_le_mul_left _ hlin).trans (by simpa using hdeg)
  obtain ⟨A, bv, hpf⟩ := partial_fraction_score Q av havinj hQdeg
  let r (h : Fin H) : AffineFraction n := {
    A := fun _ ↦ bv h * t
    b := bv h
    C := fun i ↦ t * (w i + av h)
    d := t * b + av h }
  have hrden (h : Fin H) (x : Fin n → Bool) :
      (r h).denominator x = t * eval w b x + av h * base t x := by
    have hs : (∑ i, t * (w i + av h) * boolToReal (x i)) =
        t * (∑ i, w i * boolToReal (x i)) +
          (av h * t) * ∑ i, boolToReal (x i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    dsimp [r, AffineFraction.denominator, eval, base]
    rw [hs]
    ring
  have hrnum (h : Fin H) (x : Fin n → Bool) :
      (r h).numerator x = bv h * base t x := by
    dsimp [r, AffineFraction.numerator, base]
    simp only [mul_add, mul_one, Finset.mul_sum, mul_assoc]
  have hrpos (h : Fin H) (x : Fin n → Bool) : 0 < (r h).denominator x := by
    apply add_pos_of_pos_of_nonneg (hconst h)
    apply Finset.sum_nonneg
    intro i _
    have hwi : 0 < t * (w i + av h) := mul_pos ht (by linarith [havw h i])
    cases x i with
    | false => simp [boolToReal]
    | true => simpa only [r, boolToReal, ite_true, mul_one] using hwi.le
  have hradm (h : Fin H) : (r h).Admissible := by
    refine ⟨hrpos h, Or.inl (fun i ↦ mul_pos ht (by linarith [havw h i])), ?_⟩
    intro hz
    apply Or.inl
    intro i
    have hwi : 0 < (r h).C i := mul_pos ht (by linarith [havw h i])
    exact False.elim ((ne_of_gt hwi) (hz i))
  apply (computableWithSharedHeadsN_iff_affineFractionComputable H f).mpr
  refine ⟨r, A, hradm, fun x ↦ ?_⟩
  let y := t * eval w b x / base t x
  have hbpos : 0 < base t x := base_pos t ht.le x
  have hy (h : Fin H) : 0 < y + av h := by
    have heq : y + av h = (r h).denominator x / base t x := by
      rw [hrden]
      dsimp [y]
      field_simp
    rw [heq]
    exact div_pos (hrpos h x) hbpos
  have hreval (h : Fin H) : (r h).eval x = bv h / (y + av h) := by
    rw [AffineFraction.eval, hrnum, hrden]
    dsimp [y]
    field_simp
  have hQeval : Q.eval y = S t x := by
    dsimp [Q, S, y]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    congr 1
    field_simp
  rw [show (∑ h, (r h).eval x) = ∑ h, bv h / (y + av h) from
    Finset.sum_congr rfl (fun h _ ↦ hreval h), hpf y hy, hQeval,
    div_pos_iff_of_pos_right (Finset.prod_pos fun h _ ↦ hy h)]
  exact (hstable x).1.trans (by simpa only [hS0] using hsign x)

/-- The existing strict-positive classifier convention is sufficient. Zeros
on negative inputs are removed by a small constant shift of the polynomial. -/
theorem computable_of_polynomial (w : Fin n → ℝ) (b : ℝ)
    (P : ℝ[X]) (hdeg : P.natDegree ≤ H) (f : (Fin n → Bool) → Bool)
    (hsign : ∀ x, (0 < P.eval (eval w b x) ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  obtain ⟨δ, _hδ, hshift⟩ := exists_strict_shift
    (fun x ↦ P.eval (eval w b x))
  let Q := P - Polynomial.C δ
  have hQdeg : Q.natDegree ≤ H := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le hdeg (by simp)
  apply computable_of_strict_polynomial w b Q hQdeg f
  · intro x
    simpa only [Q, Polynomial.eval_sub, Polynomial.eval_C] using
      (hshift x).1.trans (hsign x)
  · intro x
    simpa only [Q, Polynomial.eval_sub, Polynomial.eval_C] using (hshift x).2

end AffineStatistic
end HeadComplexity
