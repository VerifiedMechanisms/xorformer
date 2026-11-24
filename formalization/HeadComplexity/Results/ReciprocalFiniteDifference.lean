import HeadComplexity.Foundation.AlternatingReciprocals
import HeadComplexity.Results.ReciprocalUpperBound

set_option linter.style.header false

namespace HeadComplexity

open scoped BigOperators Topology

namespace FiniteDifference

/-- A product plus an affine multiple of its weighted derivative. -/
noncomputable def reciprocalCleared {n H : ℕ} (r : Fin H → AffineFraction n)
    (a : Fin H → ℝ) (w v : Fin n → ℝ) (b d : ℝ) (x : Fin n → Bool) : ℝ :=
  AffineStatistic.eval w b x * ∏ h, (r h).denominator x +
    AffineStatistic.eval v d x *
      ∑ h, a h * ∏ j ∈ Finset.univ.erase h, (r j).denominator x

/-- Two alternating differences share the same subset denominators. -/
theorem computable_of_strict_reciprocalCleared {n H : ℕ} (hH : 0 < H)
    (r : Fin H → AffineFraction n) (a : Fin H → ℝ)
    (w v : Fin n → ℝ) (b d : ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < reciprocalCleared r a w v b d x ↔ f x = true))
    (hne : ∀ x, reciprocalCleared r a w v b d x ≠ 0) :
    computableWithSharedHeadsN n (2 ^ H) f := by
  classical
  let L (x : Fin n → Bool) := AffineStatistic.eval w b x
  let R (x : Fin n → Bool) := AffineStatistic.eval v d x
  let B (t : ℝ) (x : Fin n → Bool) := AffineStatistic.base t x
  let D (I : Finset (Fin H)) (x : Fin n → Bool) := ∑ h ∈ I, (r h).denominator x
  let A (I : Finset (Fin H)) := ∑ h ∈ I, a h
  let Q (x : Fin n → Bool) := ∑ h, a h * ∏ j ∈ Finset.univ.erase h, (r j).denominator x
  let K₀ : ℝ := (-1)^H * (H.factorial : ℝ)
  let K₁ : ℝ := (-1)^H * ((H - 1).factorial : ℝ)
  have hK₀ : K₀ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hK₁ : K₁ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  let T (t : ℝ) (x : Fin n → Bool) :=
    L x * (∏ h, (r h).denominator x) / B t x^(H + 1) + R x * Q x / B t x^H -
      (t^2 / K₀) * L x *
        (∑ I : Finset (Fin H), (-1 : ℝ)^I.card * D I x^(H + 1) /
          (B t x^(H + 1) * (B t x + t^2 * D I x))) -
      (t^2 / K₁) * R x *
        (∑ I : Finset (Fin H), (-1 : ℝ)^I.card * A I * D I x^H /
          (B t x^H * (B t x + t^2 * D I x)))
  have hBcont (x : Fin n → Bool) : ContinuousAt (fun t ↦ B t x) 0 := by
    exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hB0 (x : Fin n → Bool) : B 0 x = 1 := by simp [B, AffineStatistic.base]
  have hcont (x : Fin n → Bool) : ContinuousAt (fun t ↦ T t x) 0 := by
    have hp : ∀ k : ℕ, ContinuousAt (fun t ↦ B t x^k) 0 :=
      fun k ↦ (hBcont x).pow k
    have hpow : ∀ k : ℕ, B 0 x^k ≠ 0 := by simp [hB0]
    have hrem (k : ℕ) (F : Finset (Fin H) → ℝ) :
        ContinuousAt (fun t ↦ ∑ I : Finset (Fin H), F I /
          (B t x^k * (B t x + t^2 * D I x))) 0 := by
      apply tendsto_finsetSum
      intro I hI
      apply continuousAt_const.div
      · exact (hp k).mul ((hBcont x).add
          ((continuousAt_id.pow 2).mul continuousAt_const))
      · simp [hB0]
    exact (((continuousAt_const.div (hp (H + 1)) (hpow _)).add
      (continuousAt_const.div (hp H) (hpow _))).sub
      ((((continuousAt_id.pow 2).div_const K₀).mul continuousAt_const).mul
        (hrem _ _))).sub
      ((((continuousAt_id.pow 2).div_const K₁).mul continuousAt_const).mul (hrem _ _))
  have hT0 (x : Fin n → Bool) : T 0 x = reciprocalCleared r a w v b d x := by
    simp [T, hB0, reciprocalCleared, L, R, Q]
  obtain ⟨bound, hbound, hbsmall⟩ := finite_positive_lower_bound
    (fun p : Finset (Fin H) × Fin n ↦ 1 / (|∑ h ∈ p.1, (r h).C p.2| + 1))
    (fun p ↦ by positivity)
  obtain ⟨t, ht, htbound, hstable⟩ := exists_pos_lt_sign_preserving T hcont
    (fun x ↦ by rw [hT0]; exact hne x) bound hbound
  have hslopes (I : Finset (Fin H)) (i : Fin n) :
      0 < t + t^2 * (∑ h ∈ I, (r h).C i) := by
    have hs := htbound.trans (hbsmall (I, i))
    have hb : 0 < |∑ h ∈ I, (r h).C i| + 1 := by positivity
    have hm : t * (|∑ h ∈ I, (r h).C i| + 1) < 1 := (lt_div_iff₀ hb).mp hs
    have hc := neg_le_abs (∑ h ∈ I, (r h).C i)
    have hp : 0 < 1 + t * (∑ h ∈ I, (r h).C i) := by nlinarith
    nlinarith [mul_pos ht hp]
  let scale₀ : ℝ := ((-(t^2))^H * K₀)⁻¹
  let scale₁ : ℝ := ((-(t^2))^(H - 1) * K₁)⁻¹
  let E (I : Finset (Fin H)) : AffineFraction n := {
    A := fun i ↦ (-1)^I.card * (scale₀ * w i + scale₁ * A I * v i)
    b := (-1)^I.card * (scale₀ * b + scale₁ * A I * d)
    C := fun i ↦ t + t^2 * ∑ h ∈ I, (r h).C i
    d := 1 + t^2 * ∑ h ∈ I, (r h).d }
  have hEnum (I : Finset (Fin H)) (x : Fin n → Bool) :
      (E I).numerator x = (-1)^I.card * (scale₀ * L x + scale₁ * A I * R x) := by
    dsimp [E, AffineFraction.numerator, L, R, AffineStatistic.eval]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    ring
  have hEden (I : Finset (Fin H)) (x : Fin n → Bool) :
      (E I).denominator x = B t x + t^2 * D I x := by
    dsimp [E, AffineFraction.denominator, B, AffineStatistic.base, D]
    simp only [add_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    ring
  have hB (x : Fin n → Bool) : 0 < B t x := AffineStatistic.base_pos t ht.le x
  have hD (I : Finset (Fin H)) (x : Fin n → Bool) : 0 ≤ D I x :=
    Finset.sum_nonneg fun h hh ↦ (hden h x).le
  have hEpos (I : Finset (Fin H)) (x : Fin n → Bool) : 0 < (E I).denominator x := by
    rw [hEden]
    exact add_pos_of_pos_of_nonneg (hB x) (mul_nonneg (sq_nonneg t) (hD I x))
  have hEadm (I : Finset (Fin H)) : (E I).Admissible := by
    refine ⟨hEpos I, Or.inl (hslopes I), ?_⟩
    intro hz
    exact Or.inl (fun i ↦ False.elim ((hslopes I i).ne' (hz i)))
  have hscore (x : Fin n → Bool) : (∑ I : Finset (Fin H), (E I).eval x) = T t x := by
    have hden' (I : Finset (Fin H)) (_hI : I ∈ (Finset.univ : Finset (Fin H)).powerset) :
        B t x + t^2 * (∑ h ∈ I, (r h).denominator x) ≠ 0 := by
      change B t x + t^2 * D I x ≠ 0
      rw [← hEden]
      exact (hEpos I x).ne'
    have hexp₀ := AlternatingMoments.reciprocal_power_expansion
      (Finset.univ : Finset (Fin H)) (fun h ↦ (r h).denominator x)
      (B t x) (t^2) (hB x).ne' hden'
    have hexp₁ := AlternatingMoments.reciprocal_sum_expansion
      (Finset.univ : Finset (Fin H)) (fun h ↦ (r h).denominator x) a
      (by simpa using hH) (B t x) (t^2) (hB x).ne' hden'
    simp only [Finset.card_univ, Fintype.card_fin, Finset.powerset_univ] at hexp₀ hexp₁
    change (∑ I : Finset (Fin H), (-1 : ℝ)^I.card / (B t x + t^2 * D I x)) =
      ((-(t^2))^H / B t x^(H + 1)) * (K₀ * ∏ h, (r h).denominator x) +
      (-(t^2))^(H + 1) * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * D I x^(H + 1) /
        (B t x^(H + 1) * (B t x + t^2 * D I x)) at hexp₀
    change (∑ I : Finset (Fin H), (-1 : ℝ)^I.card * A I / (B t x + t^2 * D I x)) =
      ((-(t^2))^(H - 1) / B t x^H) * (K₁ * Q x) +
      (-(t^2))^H * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * A I * D I x^H /
        (B t x^H * (B t x + t^2 * D I x)) at hexp₁
    have hsum : (∑ I : Finset (Fin H), (E I).eval x) =
        scale₀ * L x * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card / (B t x + t^2 * D I x) +
        scale₁ * R x * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * A I /
          (B t x + t^2 * D I x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro I hI
      rw [AffineFraction.eval, hEnum, hEden]
      ring
    rw [hsum, hexp₀, hexp₁]
    have hpow : (-(t^2))^H = (-(t^2))^(H - 1) * (-(t^2)) := by
      rw [← pow_succ, Nat.sub_add_cancel hH]
    have hpow' : (-(t^2))^(H + 1) = (-(t^2))^H * (-(t^2)) := pow_succ _ _
    dsimp only [T, scale₀, scale₁]
    rw [hpow']
    have hn : -(t^2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 ht.ne')
    field_simp [hK₀, hK₁, pow_ne_zero H hn, pow_ne_zero (H - 1) hn,
      pow_ne_zero H (hB x).ne', pow_ne_zero (H + 1) (hB x).ne']
    rw [hpow]
    ring
  let e : Finset (Fin H) ≃ Fin (2 ^ H) := Fintype.equivFinOfCardEq (by simp)
  apply (computableWithSharedHeadsN_iff_affineFractionComputable _ f).mpr
  refine ⟨fun h ↦ E (e.symm h), 0, fun h ↦ hEadm _, fun x ↦ ?_⟩
  rw [zero_add, e.symm.sum_comp (fun I ↦ (E I).eval x), hscore]
  exact (hstable x).1.trans (by rw [hT0]; exact hf x)

end FiniteDifference

/-- H+1 reciprocal heads with an arbitrary free constant need at most 2^H
vanilla heads. The coefficient signs are unrestricted. -/
theorem vanilla_of_reciprocals {n H : ℕ}
    (r : Fin (H + 1) → AffineFraction n) (a : Fin (H + 1) → ℝ) (c : ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, a h / (r h).denominator x ↔ f x = true)) :
    computableWithSharedHeadsN n (2 ^ H) f := by
  classical
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst H
    let R (h : Fin 1) : AffineFraction n := {
      A := 0
      b := a h
      C := (r h).C
      d := (r h).d }
    have hnum (h : Fin 1) (x : Fin n → Bool) : (R h).numerator x = a h := by
      simp [R, AffineFraction.numerator]
    have hden' (h : Fin 1) (x : Fin n → Bool) :
        (R h).denominator x = (r h).denominator x := rfl
    have hcomp := FiniteDifference.computable_of_positive_denominators R c hden f
      (fun x ↦ by simpa only [AffineFraction.eval, hnum, hden'] using hf x)
    simpa using hcomp
  obtain ⟨δ, _hδ, hshift⟩ := exists_strict_shift
    (fun x ↦ c + ∑ h, a h / (r h).denominator x)
  let last := Fin.last H
  let small (h : Fin H) := r h.castSucc
  let coeff (h : Fin H) := a h.castSucc
  let w (i : Fin n) := (c - δ) * (r last).C i
  let v := (r last).C
  let b := a last + (c - δ) * (r last).d
  let d := (r last).d
  have hL (x : Fin n → Bool) : AffineStatistic.eval w b x =
      a last + (c - δ) * (r last).denominator x := by
    simp [AffineStatistic.eval, AffineFraction.denominator, w, b,
      Finset.mul_sum, mul_add, mul_assoc]
    ring
  have hR (x : Fin n → Bool) :
      AffineStatistic.eval v d x = (r last).denominator x := rfl
  have hP (x : Fin n → Bool) :
      FiniteDifference.reciprocalCleared small coeff w v b d x =
        (c + ∑ h, a h / (r h).denominator x - δ) *
          ((r last).denominator x * ∏ h, (small h).denominator x) := by
    have hterm (h : Fin H) : coeff h *
        (∏ j ∈ Finset.univ.erase h, (small j).denominator x) =
        (coeff h / (small h).denominator x) * ∏ j, (small j).denominator x := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ (small j).denominator x)
        (Finset.mem_univ h)]
      have hd : (small h).denominator x ≠ 0 := (hden h.castSucc x).ne'
      field_simp [hd]
    rw [FiniteDifference.reciprocalCleared, hL, hR]
    simp_rw [hterm]
    rw [← Finset.sum_mul, Fin.sum_univ_castSucc]
    change (a last + (c - δ) * (r last).denominator x) *
        (∏ h, (small h).denominator x) + (r last).denominator x *
        ((∑ h : Fin H, a h.castSucc / (r h.castSucc).denominator x) *
          ∏ h, (small h).denominator x) =
        (c + ((∑ h : Fin H, a h.castSucc / (r h.castSucc).denominator x) +
          a last / (r last).denominator x) - δ) *
          ((r last).denominator x * ∏ h, (small h).denominator x)
    field_simp [(hden last x).ne']
    ring
  apply FiniteDifference.computable_of_strict_reciprocalCleared hH small coeff w v b d
    (fun h x ↦ hden h.castSucc x) f
  · intro x
    rw [hP, mul_pos_iff_of_pos_right
      (mul_pos (hden last x) (Finset.prod_pos fun h _ ↦ hden h.castSucc x))]
    exact (hshift x).1.trans (hf x)
  · intro x
    rw [hP]
    exact mul_ne_zero (hshift x).2 (mul_ne_zero (hden last x).ne'
      (Finset.prod_ne_zero_iff.mpr fun h _ ↦ (hden h.castSucc x).ne'))

/-- Three reciprocal heads, including a free constant, need at most four
vanilla heads. -/
theorem vanilla_four_of_three_reciprocals {n : ℕ}
    (r : Fin 3 → AffineFraction n) (a : Fin 3 → ℝ) (c : ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, a h / (r h).denominator x ↔ f x = true)) :
    computableWithSharedHeadsN n 4 f := by
  simpa using vanilla_of_reciprocals (H := 2) r a c hden f hf

end HeadComplexity
