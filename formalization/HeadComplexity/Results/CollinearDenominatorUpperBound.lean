import HeadComplexity.Results.AffineStatisticUpperBound
import HeadComplexity.Atoms.RoPE

set_option linter.style.header false

/-!
# Head-preserving simulation for collinear denominator slopes

The numerator slopes remain unrestricted. These theorems therefore apply to
pure and retained rotary scalar atoms whenever their denominator slopes are
collinear. No architectural definition is modified.
-/

namespace HeadComplexity

open scoped BigOperators Topology
open Polynomial

namespace AffineStatistic

variable {n H m : ℕ}

/-- The proper partial-fraction identity has no constant polynomial part. -/
private theorem proper_partial_fraction (P : ℝ[X]) (av : Fin H → ℝ)
    (hinj : Function.Injective av) (hdeg : P.natDegree < H) :
    ∃ bv : Fin H → ℝ, ∀ y : ℝ, (∀ h, 0 < y + av h) →
      (∑ h, bv h / (y + av h)) = P.eval y / ∏ h, (y + av h) := by
  classical
  obtain ⟨A, bv, hpf⟩ := real_partial_fraction P av hinj hdeg.le
  let Q : ℝ[X] := ∏ h, (X + C (av h))
  let L (h : Fin H) : ℝ[X] := ∏ j ∈ Finset.univ.erase h, (X + C (av j))
  have hQdeg : Q.natDegree = H := by
    dsimp [Q]
    rw [natDegree_prod _ _ (fun i _ ↦ (monic_X_add_C _).ne_zero)]
    simp
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun i _ ↦ monic_X_add_C _
  have hLdeg (h : Fin H) : (L h).natDegree < H := by
    dsimp [L]
    rw [natDegree_prod _ _ (fun i _ ↦ (monic_X_add_C _).ne_zero)]
    simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ, Fintype.card_fin]
    omega
  have hpoly : P = C A * Q + ∑ h, C (bv h) * L h := by
    apply Polynomial.funext
    intro y
    simpa [Q, L, eval_prod, eval_finsetSum] using hpf y
  have hA : A = 0 := by
    have hc := congrArg (fun R : ℝ[X] ↦ R.coeff H) hpoly
    have hsum : (∑ h, C (bv h) * L h).coeff H = 0 := by
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro h _
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (hLdeg h), mul_zero]
    rw [coeff_eq_zero_of_natDegree_lt hdeg, coeff_add, coeff_C_mul,
      show Q.coeff H = 1 by rw [← hQdeg]; exact hQmonic.coeff_natDegree,
      hsum, mul_one, add_zero] at hc
    exact hc.symm
  refine ⟨bv, fun y hy ↦ ?_⟩
  have hprod : (∏ h, (y + av h)) ≠ 0 :=
    (Finset.prod_pos fun h _ ↦ hy h).ne'
  apply (eq_div_iff hprod).mpr
  rw [Finset.sum_mul, hpf, hA, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ y + av j) (Finset.mem_univ h)]
  field_simp [(hy h).ne']

/-- A sum of affine functions times proper univariate polynomials, evaluated at
one arbitrary affine statistic, has an H-head vanilla realization whenever
it has a strict sign on every input. -/
theorem computable_of_affine_polynomial_sum
    (w : Fin n → ℝ) (b : ℝ) (W : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (p : Fin m → ℝ[X]) (hdeg : ∀ j, (p j).natDegree < H)
    (f : (Fin n → Bool) → Bool)
    (hsign : ∀ x, (0 < ∑ j, eval (W j) (a j) x * (p j).eval (eval w b x)
      ↔ f x = true))
    (hne : ∀ x, (∑ j, eval (W j) (a j) x * (p j).eval (eval w b x)) ≠ 0) :
    computableWithSharedHeadsN n H f := by
  classical
  let S (t : ℝ) (x : Fin n → Bool) :=
    (∑ j, eval (W j) (a j) x * (p j).eval (eval w b x / base t x)) / base t x
  have hbase (x : Fin n → Bool) : ContinuousAt (fun t : ℝ ↦ base t x) 0 := by
    exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hcont (x : Fin n → Bool) : ContinuousAt (fun t ↦ S t x) 0 := by
    apply ContinuousAt.div _ (hbase x) (by norm_num [base])
    apply tendsto_finsetSum
    intro j _
    apply continuousAt_const.mul
    exact (p j).continuousAt.comp (continuousAt_const.div (hbase x) (by norm_num [base]))
  have hS0 (x : Fin n → Bool) : S 0 x =
      ∑ j, eval (W j) (a j) x * (p j).eval (eval w b x) := by simp [S, base]
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
  let Q (j : Fin m) : ℝ[X] := (p j).comp (Polynomial.C t⁻¹ * Polynomial.X)
  have hQdeg (j : Fin m) : (Q j).natDegree < H := by
    apply lt_of_le_of_lt Polynomial.natDegree_comp_le
    have hlin : (Polynomial.C t⁻¹ * Polynomial.X : ℝ[X]).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hlin) (by simpa using hdeg j)
  choose bv hpf using fun j ↦ proper_partial_fraction (Q j) av havinj (hQdeg j)
  let r (h : Fin H) : AffineFraction n := {
    A := fun i ↦ ∑ j, bv j h * W j i
    b := ∑ j, bv j h * a j
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
      (r h).numerator x = ∑ j, bv j h * eval (W j) (a j) x := by
    dsimp [r, AffineFraction.numerator, eval]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
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
  refine ⟨r, 0, hradm, fun x ↦ ?_⟩
  let y := t * eval w b x / base t x
  have hbpos : 0 < base t x := base_pos t ht.le x
  have heq (h : Fin H) : y + av h = (r h).denominator x / base t x := by
    rw [hrden]
    dsimp [y]
    field_simp
  have hy (h : Fin H) : 0 < y + av h := by
    rw [heq]
    exact div_pos (hrpos h x) hbpos
  have hreval (h : Fin H) : (r h).eval x =
      ∑ j, (eval (W j) (a j) x / base t x) * (bv j h / (y + av h)) := by
    rw [AffineFraction.eval, hrnum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [heq]
    field_simp
  have hQeval (j : Fin m) : (Q j).eval y = (p j).eval (eval w b x / base t x) := by
    dsimp [Q, y]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    congr 1
    field_simp
  have hscore : (∑ h, (r h).eval x) = S t x / ∏ h, (y + av h) := by
    simp_rw [hreval]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hpf _ y hy, hQeval]
    dsimp [S]
    rw [Finset.sum_div, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [zero_add, hscore,
    div_pos_iff_of_pos_right (Finset.prod_pos fun h _ ↦ hy h)]
  exact (hstable x).1.trans (by simpa only [hS0] using hsign x)

/-- Positive affine ratios whose denominator slope vectors are all collinear
have a head-preserving vanilla realization of their Boolean classifier. -/
theorem computable_of_collinear_denominators
    (r : Fin H → AffineFraction n) (c : ℝ)
    (w : Fin n → ℝ) (k : Fin H → ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (hcol : ∀ h i, (r h).C i = k h * w i)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  classical
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst H
    apply (computableWithSharedHeadsN_iff_affineFractionComputable 0 f).mpr
    exact ⟨r, c, fun h ↦ Fin.elim0 h, hf⟩
  let first : Fin H := ⟨0, hH⟩
  obtain ⟨δ, _hδ, hshift⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (r h).eval x)
  let shift (h : Fin H) : ℝ := if h = first then c - δ else 0
  have hshiftsum : (∑ h, shift h) = c - δ := by simp [shift]
  let W (h : Fin H) (i : Fin n) := (r h).A i + shift h * (r h).C i
  let a (h : Fin H) := (r h).b + shift h * (r h).d
  let D (h : Fin H) : ℝ[X] := C (k h) * X + C (r h).d
  let p (h : Fin H) : ℝ[X] := ∏ j ∈ Finset.univ.erase h, D j
  have hDdegree (h : Fin H) : (D h).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · simp
  have hpdegree (h : Fin H) : (p h).natDegree < H := by
    have hle : (p h).natDegree ≤ H - 1 := by
      apply (Polynomial.natDegree_prod_le _ _).trans
      apply le_trans (Finset.sum_le_sum fun j _ ↦ hDdegree j)
      simp
    omega
  have hDvalue (h : Fin H) (x : Fin n → Bool) :
      (D h).eval (eval w 0 x) = (r h).denominator x := by
    simp only [D, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, eval, zero_add, AffineFraction.denominator, hcol]
    rw [Finset.mul_sum]
    simp only [mul_assoc]
    ring
  have hpvalue (h : Fin H) (x : Fin n → Bool) :
      (p h).eval (eval w 0 x) = ∏ j ∈ Finset.univ.erase h, (r j).denominator x := by
    simp only [p, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun j _ ↦ hDvalue j x
  have hLvalue (h : Fin H) (x : Fin n → Bool) :
      eval (W h) (a h) x = (r h).numerator x + shift h * (r h).denominator x := by
    dsimp [eval, W, a, AffineFraction.numerator, AffineFraction.denominator]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    ring
  have hcleared (x : Fin n → Bool) :
      (∑ h, eval (W h) (a h) x * (p h).eval (eval w 0 x)) =
        (c + ∑ h, (r h).eval x - δ) * ∏ h, (r h).denominator x := by
    have hterm (h : Fin H) :
        eval (W h) (a h) x * (p h).eval (eval w 0 x) =
          ((r h).eval x + shift h) * ∏ j, (r j).denominator x := by
      rw [hLvalue, hpvalue,
        ← Finset.mul_prod_erase Finset.univ (fun j ↦ (r j).denominator x)
          (Finset.mem_univ h), AffineFraction.eval]
      field_simp [(hden h x).ne']
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hshiftsum]
    ring
  apply computable_of_affine_polynomial_sum w 0 W a p hpdegree f
  · intro x
    rw [hcleared, mul_pos_iff_of_pos_right (Finset.prod_pos fun h _ ↦ hden h x)]
    exact (hshift x).1.trans (hf x)
  · intro x
    rw [hcleared]
    exact mul_ne_zero (hshift x).2 (Finset.prod_ne_zero_iff.mpr fun h _ ↦ (hden h x).ne')

end AffineStatistic

/-- Pure rotary scalar families with collinear denominator slopes require no
additional vanilla heads, at any head count. -/
theorem pureRoPEFamily_vanilla_of_collinear_denominators {n H : ℕ}
    (p : Fin H → PureRoPEAtom n) (c : ℝ) (w : Fin n → ℝ) (k : Fin H → ℝ)
    (hcol : ∀ h i, (p h).b i - (p h).a i = k h * w i)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  apply AffineStatistic.computable_of_collinear_denominators
    (fun h ↦ (p h).toAffineFraction) c w k
    (fun h x ↦ (p h).denominator_pos x) hcol f
  intro x
  simpa only [PureRoPEAtom.eval_eq] using hf x

/-- The collinear-denominator result also applies to retained rotary scalar
families, because it does not restrict the affine numerator coefficients. -/
theorem retainedRoPEFamily_vanilla_of_collinear_denominators {n H : ℕ}
    (p : Fin H → RetainedRoPEAtom n) (c : ℝ) (w : Fin n → ℝ) (k : Fin H → ℝ)
    (hcol : ∀ h i, (p h).b i - (p h).a i = k h * w i)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  apply AffineStatistic.computable_of_collinear_denominators
    (fun h ↦ (p h).toAffineFraction) c w k
    (fun h x ↦ (p h).denominator_pos x) hcol f
  exact hf

end HeadComplexity
