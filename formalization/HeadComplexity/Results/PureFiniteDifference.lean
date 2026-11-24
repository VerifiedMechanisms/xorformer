import HeadComplexity.Results.FiniteDifferenceUpperBound
import HeadComplexity.Results.RoPETwoHeads

set_option linter.style.header false

namespace HeadComplexity

open scoped BigOperators Topology

namespace CubeAffine

/-- A positive uniformly oriented numerator permits deletion of its singleton
term from the alternating subset construction. -/
theorem computable_of_strict_tangent_uniform_numerator {n H : ℕ}
    (N D : Fin H → CubeAffine n) (first : Fin H) (F : CubeAffine n) (σ : ℝ)
    (hD : ∀ h x, 0 < (D h).eval x) (hF : ∀ x, 0 < F.eval x)
    (hFs : (∀ i, 0 < F.slope i) ∨ (∀ i, F.slope i < 0))
    (hN : ∀ x, (N first).eval x = σ * F.eval x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < ∑ h, (N h).eval x *
        ∏ j ∈ Finset.univ.erase h, (D j).eval x ↔ f x = true))
    (hne : ∀ x, (∑ h, (N h).eval x *
        ∏ j ∈ Finset.univ.erase h, (D j).eval x) ≠ 0) :
    computableWithSharedHeadsN n (2 ^ H - 2) f := by
  classical
  have hH : 0 < H := Fin.pos first
  let P (x : Fin n → Bool) := ∑ h, (N h).eval x *
    ∏ j ∈ Finset.univ.erase h, (D j).eval x
  let Z (I : Finset (Fin H)) (x : Fin n → Bool) := ∑ h ∈ I, (D h).eval x
  let M (t : ℝ) (h : Fin H) := combine 1 (N h) (if h = first then σ*t else 0) (D first)
  let L (t : ℝ) (I : Finset (Fin H)) (x : Fin n → Bool) := ∑ h ∈ I, (M t h).eval x
  let K : ℝ := (-1)^H * ((H - 1).factorial : ℝ)
  have hK : K ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hclear (t : ℝ) (x : Fin n → Bool) :
      (∑ h, (M t h).eval x * ∏ j ∈ Finset.univ.erase h, (D j).eval x) =
        P x + σ*t * ∏ h, (D h).eval x := by
    simp only [M, combine_eval, one_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [← mul_assoc, Finset.mul_prod_erase Finset.univ
      (fun j ↦ (D j).eval x) (Finset.mem_univ first)]
    dsimp only [P]
    ring
  let T (t : ℝ) (x : Fin n → Bool) :=
    (P x + σ*t * ∏ h, (D h).eval x) / F.eval x^H - (t / K) *
      ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L t I x * Z I x^H /
        (F.eval x^H * (F.eval x + t * Z I x))
  have hLcont (I : Finset (Fin H)) (x : Fin n → Bool) :
      ContinuousAt (fun t ↦ L t I x) 0 := by
    apply tendsto_finsetSum
    intro h hh
    simp only [M, combine_eval, one_mul]
    by_cases he : h = first
    · simp only [he, if_true]
      exact continuousAt_const.add ((continuousAt_const.mul continuousAt_id).mul continuousAt_const)
    · simp only [he, if_false, zero_mul, add_zero]
      exact continuousAt_const
  have hcont (x : Fin n → Bool) : ContinuousAt (fun t ↦ T t x) 0 := by
    apply ContinuousAt.sub
    · exact (continuousAt_const.add
        ((continuousAt_const.mul continuousAt_id).mul continuousAt_const)).div_const _
    · apply ContinuousAt.mul (continuousAt_id.div_const K)
      apply tendsto_finsetSum
      intro I hI
      apply ((continuousAt_const.mul (hLcont I x)).mul continuousAt_const).div
      · exact continuousAt_const.mul (continuousAt_const.add
          (continuousAt_id.mul continuousAt_const))
      · simpa using mul_ne_zero (pow_ne_zero H (hF x).ne') (hF x).ne'
  have hT0 (x : Fin n → Bool) : T 0 x = P x / F.eval x^H := by simp [T]
  have hFsne (i : Fin n) : F.slope i ≠ 0 := hFs.elim
    (fun hs ↦ (hs i).ne') (fun hs ↦ (hs i).ne)
  obtain ⟨bound, hbound, hbsmall⟩ := finite_positive_lower_bound
    (fun p : Finset (Fin H) × Fin n ↦
      |F.slope p.2| / (|∑ h ∈ p.1, (D h).slope p.2| + 1))
    (fun p ↦ div_pos (abs_pos.mpr (hFsne p.2)) (by positivity))
  obtain ⟨t, ht, htbound, hstable⟩ := exists_pos_lt_sign_preserving T hcont
    (fun x ↦ by rw [hT0]; exact div_ne_zero (hne x) (pow_ne_zero H (hF x).ne'))
    bound hbound
  have hslopebound (I : Finset (Fin H)) (i : Fin n) :
      t * |∑ h ∈ I, (D h).slope i| < |F.slope i| := by
    have hs := htbound.trans (hbsmall (I, i))
    have hb : 0 < |∑ h ∈ I, (D h).slope i| + 1 := by positivity
    have hm := (lt_div_iff₀ hb).mp hs
    nlinarith
  have hslopes (I : Finset (Fin H)) :
      (∀ i, 0 < F.slope i + t * ∑ h ∈ I, (D h).slope i) ∨
        (∀ i, F.slope i + t * ∑ h ∈ I, (D h).slope i < 0) := by
    rcases hFs with hs | hs
    · left
      intro i
      have hb := hslopebound I i
      rw [abs_of_pos (hs i)] at hb
      have hc := neg_le_abs (∑ h ∈ I, (D h).slope i)
      nlinarith
    · right
      intro i
      have hb := hslopebound I i
      rw [abs_of_neg (hs i)] at hb
      have hc := le_abs_self (∑ h ∈ I, (D h).slope i)
      nlinarith
  let scale : ℝ := ((-t)^(H - 1) * K)⁻¹
  let R (I : Finset (Fin H)) : AffineFraction n := {
    A := fun i ↦ scale * (-1)^I.card * ∑ h ∈ I, (M t h).slope i
    b := scale * (-1)^I.card * ∑ h ∈ I, (M t h).const
    C := fun i ↦ F.slope i + t * ∑ h ∈ I, (D h).slope i
    d := F.const + t * ∑ h ∈ I, (D h).const }
  have hRnum (I : Finset (Fin H)) (x : Fin n → Bool) :
      (R I).numerator x = scale * (-1)^I.card * L t I x := by
    dsimp [R, AffineFraction.numerator, L, eval]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hRden (I : Finset (Fin H)) (x : Fin n → Bool) :
      (R I).denominator x = F.eval x + t * Z I x := by
    dsimp [R, AffineFraction.denominator, eval, Z]
    simp only [add_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    ring
  have hZ (I : Finset (Fin H)) (x : Fin n → Bool) : 0 ≤ Z I x :=
    Finset.sum_nonneg fun h hh ↦ (hD h x).le
  have hRpos (I : Finset (Fin H)) (x : Fin n → Bool) : 0 < (R I).denominator x := by
    rw [hRden]
    exact add_pos_of_pos_of_nonneg (hF x) (mul_nonneg ht.le (hZ I x))
  have hRadm (I : Finset (Fin H)) : (R I).Admissible := by
    refine ⟨hRpos I, ?_, ?_⟩
    · exact (hslopes I).elim Or.inl (fun hs ↦ Or.inr (Or.inl hs))
    · intro hz
      left
      intro i
      rcases hslopes I with hs | hs
      · exact False.elim ((hs i).ne' (hz i))
      · exact False.elim ((hs i).ne (hz i))
  have hscore (x : Fin n → Bool) : (∑ I : Finset (Fin H), (R I).eval x) = T t x := by
    have hexp := AlternatingMoments.reciprocal_sum_expansion
      (Finset.univ : Finset (Fin H)) (fun h ↦ (D h).eval x)
      (fun h ↦ (M t h).eval x) (by simpa using hH) (F.eval x) t (hF x).ne'
      (fun I hI ↦ by
        change F.eval x + t * Z I x ≠ 0
        rw [← hRden]
        exact (hRpos I x).ne')
    simp only [Finset.card_univ, Fintype.card_fin, Finset.powerset_univ] at hexp
    rw [hclear] at hexp
    change (∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L t I x / (F.eval x + t * Z I x)) =
      ((-t)^(H - 1) / F.eval x^H) * (K * (P x + σ*t * ∏ h, (D h).eval x)) +
      (-t)^H * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L t I x * Z I x^H /
        (F.eval x^H * (F.eval x + t * Z I x)) at hexp
    have hsum : (∑ I : Finset (Fin H), (R I).eval x) =
        scale * ∑ I : Finset (Fin H), (-1 : ℝ)^I.card * L t I x /
          (F.eval x + t * Z I x) := by
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
      pow_ne_zero H (hF x).ne']
    ring
  have hsingle (x : Fin n → Bool) : (R {first}).eval x = -scale * σ := by
    rw [AffineFraction.eval, hRnum, hRden]
    simp only [L, Z, Finset.sum_singleton, Finset.card_singleton, pow_one,
      M, combine_eval, one_mul, if_true, hN]
    have hd : F.eval x + t * (D first).eval x ≠ 0 := by
      exact (add_pos_of_pos_of_nonneg (hF x) (mul_nonneg ht.le (hD first x).le)).ne'
    field_simp [hd]
  have hempty (x : Fin n → Bool) : (R ∅).eval x = 0 := by
    simp [AffineFraction.eval, hRnum, L]
  let S : Finset (Finset (Fin H)) := (Finset.univ.erase ∅).erase {first}
  have hSmem : {first} ∈ (Finset.univ : Finset (Finset (Fin H))).erase ∅ := by simp
  have hScard : Fintype.card S = 2 ^ H - 2 := by
    simp only [Fintype.card_coe, S, Finset.card_erase_of_mem hSmem,
      Finset.card_erase_of_mem (Finset.mem_univ ∅), Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
    omega
  let e : S ≃ Fin (2 ^ H - 2) := Fintype.equivFinOfCardEq hScard
  apply (computableWithSharedHeadsN_iff_affineFractionComputable _ f).mpr
  refine ⟨fun h ↦ R (e.symm h), -scale * σ, fun h ↦ hRadm _, fun x ↦ ?_⟩
  have hsum : -scale * σ + (∑ h : Fin (2 ^ H - 2), (R (e.symm h)).eval x) =
      ∑ I : Finset (Fin H), (R I).eval x := by
    rw [e.symm.sum_comp (fun I : S ↦ (R I).eval x)]
    rw [Finset.sum_coe_sort S (fun I ↦ (R I).eval x)]
    have h1 := Finset.sum_erase_add (Finset.univ.erase ∅) (fun I ↦ (R I).eval x) hSmem
    have h2 := Finset.sum_erase_add Finset.univ (fun I ↦ (R I).eval x) (Finset.mem_univ ∅)
    rw [hsingle] at h1
    rw [hempty, add_zero] at h2
    dsimp only [S]
    linarith
  rw [hsum, hscore]
  exact (hstable x).1.trans (by rw [hT0, div_pos_iff_of_pos_right (pow_pos (hF x) H)]; exact hf x)

end CubeAffine

/-- One positive uniformly oriented numerator-denominator pencil suffices for
the improved subset bound, even if every other numerator is arbitrary. -/
theorem vanilla_of_positive_fractions_with_uniform_endpoint {n H : ℕ}
    (r : Fin H → AffineFraction n) (first second : Fin H) (hneq : first ≠ second)
    (F : CubeAffine n) (t σ c : ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x) (hF : ∀ x, 0 < F.eval x)
    (hFs : (∀ i, 0 < F.slope i) ∨ (∀ i, F.slope i < 0))
    (hN : ∀ x, (r first).numerator x = t * (r first).denominator x + σ * F.eval x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true))
    (hne : ∀ x, c + ∑ h, (r h).eval x ≠ 0) :
    computableWithSharedHeadsN n (2 ^ H - 2) f := by
  classical
  let shift (h : Fin H) := (if h = first then -t else 0) +
    (if h = second then c + t else 0)
  let N (h : Fin H) := CubeAffine.combine 1 (r h).numForm (shift h) (r h).denForm
  let D (h : Fin H) := (r h).denForm
  have hshift : (∑ h, shift h) = c := by simp [shift, Finset.sum_add_distrib]
  have hfirst (x : Fin n → Bool) : (N first).eval x = σ * F.eval x := by
    simp only [N, CubeAffine.combine_eval, one_mul, AffineFraction.numForm_eval,
      AffineFraction.denForm_eval, shift, if_true, hneq, if_false, add_zero]
    rw [hN]
    ring
  have hP (x : Fin n → Bool) :
      (∑ h, (N h).eval x * ∏ j ∈ Finset.univ.erase h, (D j).eval x) =
        (c + ∑ h, (r h).eval x) * ∏ h, (D h).eval x := by
    have hterm (h : Fin H) : (N h).eval x *
        (∏ j ∈ Finset.univ.erase h, (D j).eval x) =
        ((r h).eval x + shift h) * ∏ j, (D j).eval x := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ (D j).eval x)
        (Finset.mem_univ h)]
      simp only [N, CubeAffine.combine_eval, one_mul, AffineFraction.numForm_eval,
        AffineFraction.denForm_eval, D, AffineFraction.eval]
      field_simp [(hden h x).ne']
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hshift]
    ring
  apply CubeAffine.computable_of_strict_tangent_uniform_numerator N D first F σ hden hF hFs
    hfirst f
  · intro x
    have hprod : 0 < ∏ h, (D h).eval x := Finset.prod_pos fun h _ ↦ hden h x
    rw [hP, mul_pos_iff_of_pos_right hprod]
    exact hf x
  · intro x
    rw [hP]
    exact mul_ne_zero (hne x) (Finset.prod_ne_zero_iff.mpr fun h _ ↦ (hden h x).ne')

/-- One pure head and H+1 arbitrary positive affine ratios have a vanilla
realization with 2^(H+2)-2 heads. -/
theorem vanilla_of_pure_add_positive_fractions {n H : ℕ}
    (p : PureRoPEAtom n) (q : Fin (H + 1) → AffineFraction n)
    (hq : ∀ h x, 0 < (q h).denominator x) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + p.eval x + ∑ h, (q h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n (2 ^ (H + 2) - 2) f := by
  classical
  obtain ⟨p', c', hp', hs⟩ := p.exists_nondegenerate_addend (fun x ↦ ∑ h, (q h).eval x) c
  obtain ⟨F, t, σ, _hσ, hF, hFs, hN⟩ := p'.exists_uniform_endpoint hp'
  let r : Fin (H + 2) → AffineFraction n := Fin.cons p'.toAffineFraction q
  have hrden (h : Fin (H + 2)) (x : Fin n → Bool) : 0 < (r h).denominator x := by
    refine Fin.cases ?_ (fun h ↦ ?_) h
    · exact p'.denominator_pos x
    · exact hq h x
  apply vanilla_of_positive_fractions_with_uniform_endpoint r 0 (0 : Fin (H + 1)).succ
    (by intro he; have hc := congrArg Fin.val he; simp at hc)
    F t σ c' hrden hF hFs hN f
  · intro x
    have he : c' + ∑ h, (r h).eval x = c' + p'.eval x + ∑ h, (q h).eval x := by
      simp only [Fin.sum_univ_succ, r, Fin.cons_zero, Fin.cons_succ, ← p'.eval_eq]
      ring
    rw [he]
    exact (hs x).1.trans (hf x)
  · intro x
    have he : c' + ∑ h, (r h).eval x = c' + p'.eval x + ∑ h, (q h).eval x := by
      simp only [Fin.sum_univ_succ, r, Fin.cons_zero, Fin.cons_succ, ← p'.eval_eq]
      ring
    rw [he]
    exact (hs x).2

/-- The special pure numerator saves one head from the general exponential
bound at every head count of at least two. -/
theorem pureRoPEComputable_vanilla_improved_exponential_bound {n H : ℕ}
    (hH : 2 ≤ H) {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 2) f := by
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 2 := ⟨H - 2, by omega⟩
  obtain ⟨p, c, hp⟩ := hf
  apply vanilla_of_pure_add_positive_fractions (p 0)
    (fun h : Fin (K + 1) ↦ (p h.succ).toAffineFraction)
    (fun h x ↦ (p h.succ).denominator_pos x) c f
  intro x
  have hs := hp x
  rw [Fin.sum_univ_succ] at hs
  simpa only [← PureRoPEAtom.eval_eq, add_assoc] using hs

end HeadComplexity
