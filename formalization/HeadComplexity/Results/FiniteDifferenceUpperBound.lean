import HeadComplexity.Foundation.AlternatingMoments
import HeadComplexity.Results.CollinearDenominatorUpperBound
import Mathlib.Data.Fintype.Powerset

set_option linter.style.header false

/-!
# Finite-difference simulation of positive affine ratios

A sum of H arbitrary affine ratios with denominators positive on the Boolean
cube has a vanilla realization with at most 2^H - 1 heads. This does not prove
the head-preserving pure rotary conjecture. The construction selects a finite
positive perturbation using strict sign margins.
-/

namespace HeadComplexity

open scoped BigOperators Topology

namespace FiniteDifference

variable {n H : ℕ}

/-- The cleared numerator of a family with arbitrary affine denominators. -/
noncomputable def cleared (r : Fin H → AffineFraction n)
    (W : Fin H → Fin n → ℝ) (a : Fin H → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ h, AffineStatistic.eval (W h) (a h) x *
    ∏ j ∈ Finset.univ.erase h, (r j).denominator x

/-- Any strict cleared affine-ratio sign pattern has a finite vanilla
realization with 2^H - 1 heads. -/
theorem computable_of_strict_cleared (hH : 0 < H)
    (r : Fin H → AffineFraction n) (W : Fin H → Fin n → ℝ) (a : Fin H → ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < cleared r W a x ↔ f x = true))
    (hne : ∀ x, cleared r W a x ≠ 0) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  classical
  let B (x : Fin n → Bool) := AffineStatistic.base 1 x
  let D (I : Finset (Fin H)) (x : Fin n → Bool) := ∑ h ∈ I, (r h).denominator x
  let L (I : Finset (Fin H)) (x : Fin n → Bool) :=
    ∑ h ∈ I, AffineStatistic.eval (W h) (a h) x
  let K : ℝ := (-1)^H * ((H - 1).factorial : ℝ)
  have hK : K ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hB (x : Fin n → Bool) : 0 < B x := AffineStatistic.base_pos 1 (by norm_num) x
  let T (t : ℝ) (x : Fin n → Bool) :=
    cleared r W a x / B x^H - (t / K) *
      ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L I x * D I x^H /
        (B x^H * (B x + t * D I x))
  have hcont (x : Fin n → Bool) : ContinuousAt (fun t ↦ T t x) 0 := by
    apply continuousAt_const.sub
    apply ContinuousAt.mul (continuousAt_id.div_const K)
    apply tendsto_finsetSum
    intro I hI
    apply continuousAt_const.div
    · exact continuousAt_const.mul (continuousAt_const.add
        (continuousAt_id.mul continuousAt_const))
    · simpa using mul_ne_zero (pow_ne_zero H (hB x).ne') (hB x).ne'
  have hT0 (x : Fin n → Bool) : T 0 x = cleared r W a x / B x^H := by simp [T]
  obtain ⟨bound, hbound, hbsmall⟩ := finite_positive_lower_bound
    (fun p : Finset (Fin H) × Fin n ↦ 1 / (|∑ h ∈ p.1, (r h).C p.2| + 1))
    (fun p ↦ by positivity)
  obtain ⟨t, ht, htbound, hstable⟩ := exists_pos_lt_sign_preserving T hcont
    (fun x ↦ by rw [hT0]; exact div_ne_zero (hne x) (pow_ne_zero H (hB x).ne'))
    bound hbound
  have hslopes (I : Finset (Fin H)) (i : Fin n) : 0 < 1 + t*(∑ h ∈ I, (r h).C i) := by
    have hs := htbound.trans (hbsmall (I, i))
    have hb : 0 < |∑ h ∈ I, (r h).C i| + 1 := by positivity
    have hm : t * (|∑ h ∈ I, (r h).C i| + 1) < 1 := (lt_div_iff₀ hb).mp hs
    have hc := neg_le_abs (∑ h ∈ I, (r h).C i)
    nlinarith
  let scale : ℝ := ((-t)^(H - 1) * K)⁻¹
  let R (I : Finset (Fin H)) : AffineFraction n := {
    A := fun i ↦ scale * (-1)^I.card * ∑ h ∈ I, W h i
    b := scale * (-1)^I.card * ∑ h ∈ I, a h
    C := fun i ↦ 1 + t * ∑ h ∈ I, (r h).C i
    d := 1 + t * ∑ h ∈ I, (r h).d }
  have hRnum (I : Finset (Fin H)) (x : Fin n → Bool) :
      (R I).numerator x = scale * (-1)^I.card * L I x := by
    dsimp [R, AffineFraction.numerator, L, AffineStatistic.eval]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hRden (I : Finset (Fin H)) (x : Fin n → Bool) :
      (R I).denominator x = B x + t * D I x := by
    dsimp [R, AffineFraction.denominator, B, AffineStatistic.base, D]
    simp only [add_mul, mul_add, one_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    ring
  have hD (I : Finset (Fin H)) (x : Fin n → Bool) : 0 ≤ D I x :=
    Finset.sum_nonneg fun h hh ↦ (hden h x).le
  have hRpos (I : Finset (Fin H)) (x : Fin n → Bool) : 0 < (R I).denominator x := by
    rw [hRden]
    exact add_pos_of_pos_of_nonneg (hB x) (mul_nonneg ht.le (hD I x))
  have hRadm (I : Finset (Fin H)) : (R I).Admissible := by
    refine ⟨hRpos I, Or.inl (hslopes I), ?_⟩
    intro hz
    exact Or.inl (fun i ↦ False.elim ((hslopes I i).ne' (hz i)))
  have hscore (x : Fin n → Bool) : (∑ I : Finset (Fin H), (R I).eval x) = T t x := by
    have hexp := AlternatingMoments.reciprocal_sum_expansion
      (Finset.univ : Finset (Fin H)) (fun h ↦ (r h).denominator x)
      (fun h ↦ AffineStatistic.eval (W h) (a h) x)
      (by simpa using hH) (B x) t (hB x).ne'
      (fun I hI ↦ by
        change B x + t * D I x ≠ 0
        rw [← hRden]
        exact (hRpos I x).ne')
    simp only [Finset.card_univ, Fintype.card_fin, Finset.powerset_univ] at hexp
    change (∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L I x / (B x + t * D I x)) =
      ((-t)^(H - 1) / B x^H) * (K * cleared r W a x) +
      (-t)^H * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L I x * D I x^H /
        (B x^H * (B x + t * D I x)) at hexp
    have hsum : (∑ I : Finset (Fin H), (R I).eval x) =
        scale * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L I x / (B x + t * D I x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      rw [AffineFraction.eval, hRnum, hRden]
      ring
    rw [hsum, hexp]
    have hpow : (-t)^H = (-t)^(H - 1) * (-t) := by
      rw [← pow_succ, Nat.sub_add_cancel hH]
    rw [hpow]
    dsimp only [T, scale]
    field_simp [hK, pow_ne_zero (H - 1) (neg_ne_zero.mpr ht.ne'),
      pow_ne_zero H (hB x).ne']
    ring
  let S : Finset (Finset (Fin H)) := Finset.univ.erase ∅
  have hScard : Fintype.card S = 2 ^ H - 1 := by
    simp [S, Fintype.card_finset]
  let e : S ≃ Fin (2 ^ H - 1) := Fintype.equivFinOfCardEq hScard
  apply (computableWithSharedHeadsN_iff_affineFractionComputable _ f).mpr
  refine ⟨fun h ↦ R (e.symm h), 0, fun h ↦ hRadm _, fun x ↦ ?_⟩
  have hsum : (∑ h : Fin (2 ^ H - 1), (R (e.symm h)).eval x) =
      ∑ I : Finset (Fin H), (R I).eval x := by
    rw [e.symm.sum_comp (fun I : S ↦ (R I).eval x)]
    rw [Finset.sum_coe_sort S (fun I ↦ (R I).eval x)]
    have hempty : (R ∅).eval x = 0 := by simp [AffineFraction.eval, hRnum, L]
    simpa only [S, hempty, add_zero] using
      Finset.sum_erase_add Finset.univ (fun I ↦ (R I).eval x) (Finset.mem_univ ∅)
  rw [zero_add, hsum, hscore]
  exact (hstable x).1.trans (by rw [hT0, div_pos_iff_of_pos_right (pow_pos (hB x) H)]; exact hf x)

/-- Positive affine ratios, without any slope restrictions, admit Boolean
simulation by 2^H - 1 vanilla heads. Zero heads and zero input bits are included. -/
theorem computable_of_positive_denominators
    (r : Fin H → AffineFraction n) (c : ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  classical
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst H
    simp only [pow_zero, Nat.sub_self]
    apply (computableWithSharedHeadsN_iff_affineFractionComputable 0 f).mpr
    exact ⟨r, c, fun h ↦ Fin.elim0 h, hf⟩
  let first : Fin H := ⟨0, hH⟩
  obtain ⟨δ, _hδ, hshift⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (r h).eval x)
  let shift (h : Fin H) : ℝ := if h = first then c - δ else 0
  have hshiftsum : (∑ h, shift h) = c - δ := by simp [shift]
  let W (h : Fin H) (i : Fin n) := (r h).A i + shift h * (r h).C i
  let a (h : Fin H) := (r h).b + shift h * (r h).d
  have hLvalue (h : Fin H) (x : Fin n → Bool) :
      AffineStatistic.eval (W h) (a h) x =
        (r h).numerator x + shift h * (r h).denominator x := by
    dsimp [AffineStatistic.eval, W, a, AffineFraction.numerator, AffineFraction.denominator]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    ring
  have hcleared (x : Fin n → Bool) : cleared r W a x =
      (c + ∑ h, (r h).eval x - δ) * ∏ h, (r h).denominator x := by
    have hterm (h : Fin H) :
        AffineStatistic.eval (W h) (a h) x *
          (∏ j ∈ Finset.univ.erase h, (r j).denominator x) =
          ((r h).eval x + shift h) * ∏ j, (r j).denominator x := by
      rw [hLvalue,
        ← Finset.mul_prod_erase Finset.univ (fun j ↦ (r j).denominator x)
          (Finset.mem_univ h), AffineFraction.eval]
      field_simp [(hden h x).ne']
    dsimp only [cleared]
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hshiftsum]
    ring
  apply computable_of_strict_cleared hH r W a hden f
  · intro x
    rw [hcleared, mul_pos_iff_of_pos_right (Finset.prod_pos fun h _ ↦ hden h x)]
    exact (hshift x).1.trans (hf x)
  · intro x
    rw [hcleared]
    exact mul_ne_zero (hshift x).2 (Finset.prod_ne_zero_iff.mpr fun h _ ↦ (hden h x).ne')

end FiniteDifference

/-- An all-head-count bound for pure rotary scalar families. This exponential
bound is not the conjectured head-preserving simulation. -/
theorem pureRoPEFamily_vanilla_exponential_bound {n H : ℕ}
    (p : Fin H → PureRoPEAtom n) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  apply FiniteDifference.computable_of_positive_denominators
    (fun h ↦ (p h).toAffineFraction) c (fun h x ↦ (p h).denominator_pos x) f
  intro x
  simpa only [PureRoPEAtom.eval_eq] using hf x

/-- The finite-difference bound also applies to retained rotary scalar atoms;
no pure-atom numerator condition is needed for this larger head budget. -/
theorem retainedRoPEFamily_vanilla_exponential_bound {n H : ℕ}
    (p : Fin H → RetainedRoPEAtom n) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  apply FiniteDifference.computable_of_positive_denominators
    (fun h ↦ (p h).toAffineFraction) c (fun h x ↦ (p h).denominator_pos x) f
  exact hf

end HeadComplexity
