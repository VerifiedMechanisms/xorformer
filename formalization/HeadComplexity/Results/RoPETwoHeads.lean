import HeadComplexity.Atoms.TwoHeadPencil
import HeadComplexity.Atoms.RoPEStrictness
import HeadComplexity.Results.RoPEComparison

set_option linter.style.header false

/-!
# Two pure rotary heads require only two vanilla heads

Subtracting a suitable token value from a nondegenerate pure atom produces,
up to sign, a positive affine numerator with strictly uniform slopes. This
gives one admissible affine factor in the cleared two-head polynomial.
The two-product construction then removes the complement-invariance
assumption entirely. The rotary objects here are the existing scalar atoms.
-/

namespace HeadComplexity

open scoped BigOperators

namespace AffineFraction

variable {n : ℕ}

noncomputable def numForm (r : AffineFraction n) : CubeAffine n := ⟨r.b, r.A⟩
noncomputable def denForm (r : AffineFraction n) : CubeAffine n := ⟨r.d, r.C⟩

@[simp] theorem numForm_eval (r : AffineFraction n) (x : Fin n → Bool) :
    r.numForm.eval x = r.numerator x := rfl

@[simp] theorem denForm_eval (r : AffineFraction n) (x : Fin n → Bool) :
    r.denForm.eval x = r.denominator x := rfl

end AffineFraction

namespace PureRoPEAtom

variable {n : ℕ}

/-- Subtract the value of token zero from the head numerator. -/
noncomputable def zeroShift (p : PureRoPEAtom n) : CubeAffine n :=
  ⟨p.η - p.v₀ * p.γ, fun i ↦ (p.v₁ - p.v₀) * p.b i⟩

/-- Subtract the head numerator from token one's value times the denominator. -/
noncomputable def oneShift (p : PureRoPEAtom n) : CubeAffine n :=
  ⟨p.v₁ * p.γ - p.η + (p.v₁ - p.v₀) * ∑ i, p.a i,
    fun i ↦ -(p.v₁ - p.v₀) * p.a i⟩

theorem zeroShift_eval (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.zeroShift.eval x = p.η - p.v₀ * p.γ +
      (p.v₁ - p.v₀) * ∑ i, if x i then p.b i else 0 := by
  simp only [zeroShift, CubeAffine.eval, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

theorem oneShift_eval (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.oneShift.eval x = p.v₁ * p.γ - p.η +
      (p.v₁ - p.v₀) * ∑ i, if x i then 0 else p.a i := by
  simp only [oneShift, CubeAffine.eval, Finset.mul_sum, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]
  ring

theorem zeroShift_eq (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.zeroShift.eval x = p.toAffineFraction.numerator x -
      p.v₀ * p.toAffineFraction.denominator x := by
  simp only [zeroShift, CubeAffine.eval, toAffineFraction,
    AffineFraction.numerator, AffineFraction.denominator,
    mul_add, Finset.mul_sum]
  rw [add_sub_add_comm]
  congr 1
  · rw [show (∑ i, p.a i * p.v₀) = ∑ i, p.v₀ * p.a i from
      Finset.sum_congr rfl fun i _ ↦ mul_comm _ _]
    ring
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem oneShift_eq (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.oneShift.eval x = p.v₁ * p.toAffineFraction.denominator x -
      p.toAffineFraction.numerator x := by
  simp only [oneShift, CubeAffine.eval, toAffineFraction,
    AffineFraction.numerator, AffineFraction.denominator,
    mul_add, Finset.mul_sum]
  rw [add_sub_add_comm]
  congr 1
  · simp only [sub_mul, Finset.sum_sub_distrib, mul_comm]
    ring
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Some token endpoint leaves a positive affine numerator with strictly
uniform slopes. Both denominator orientations are allowed by vanilla. -/
theorem exists_uniform_endpoint (p : PureRoPEAtom n) (hp : p.v₁ ≠ p.v₀) :
    ∃ (F : CubeAffine n) (t σ : ℝ),
      (σ = 1 ∨ σ = -1) ∧ (∀ x, 0 < F.eval x) ∧
      ((∀ i, 0 < F.slope i) ∨ (∀ i, F.slope i < 0)) ∧
      ∀ x, p.toAffineFraction.numerator x =
        t * p.toAffineFraction.denominator x + σ * F.eval x := by
  have hmass₀ (x : Fin n → Bool) : 0 ≤ ∑ i, if x i then p.b i else 0 :=
    Finset.sum_nonneg fun i _ ↦ by split <;> first | exact (p.hb i).le | exact le_rfl
  have hmass₁ (x : Fin n → Bool) : 0 ≤ ∑ i, if x i then 0 else p.a i :=
    Finset.sum_nonneg fun i _ ↦ by split <;> first | exact (p.ha i).le | exact le_rfl
  rcases lt_or_gt_of_ne hp with hk | hk
  · by_cases hc : p.η - p.v₀ * p.γ < 0
    · let F := CubeAffine.combine (-1) p.zeroShift 0 p.zeroShift
      refine ⟨F, p.v₀, -1, Or.inr rfl, ?_, Or.inl ?_, ?_⟩
      · intro x
        simp only [F, CubeAffine.combine_eval, neg_one_mul, zero_mul, add_zero]
        rw [neg_pos, zeroShift_eval]
        have hterm := mul_nonpos_of_nonpos_of_nonneg (sub_neg.mpr hk).le (hmass₀ x)
        linarith
      · intro i
        dsimp [F, CubeAffine.combine, zeroShift]
        have := mul_neg_of_neg_of_pos (sub_neg.mpr hk) (p.hb i)
        linarith
      · intro x
        simp only [F, CubeAffine.combine_eval, neg_one_mul, zero_mul, add_zero,
          neg_neg]
        linarith [p.zeroShift_eq x]
    · let F := CubeAffine.combine (-1) p.oneShift 0 p.oneShift
      have hc' : p.v₁ * p.γ - p.η < 0 := by
        have := mul_lt_mul_of_pos_right hk p.hγ
        linarith
      refine ⟨F, p.v₁, 1, Or.inl rfl, ?_, Or.inr ?_, ?_⟩
      · intro x
        simp only [F, CubeAffine.combine_eval, neg_one_mul, zero_mul, add_zero]
        rw [neg_pos, oneShift_eval]
        have hterm := mul_nonpos_of_nonpos_of_nonneg (sub_neg.mpr hk).le (hmass₁ x)
        linarith
      · intro i
        dsimp [F, CubeAffine.combine, oneShift]
        have := mul_neg_of_neg_of_pos (sub_neg.mpr hk) (p.ha i)
        linarith
      · intro x
        simp only [F, CubeAffine.combine_eval, neg_one_mul, zero_mul, add_zero,
          one_mul]
        linarith [p.oneShift_eq x]
  · by_cases hc : 0 < p.η - p.v₀ * p.γ
    · refine ⟨p.zeroShift, p.v₀, 1, Or.inl rfl, ?_, Or.inl ?_, ?_⟩
      · intro x
        rw [zeroShift_eval]
        exact add_pos_of_pos_of_nonneg hc
          (mul_nonneg (sub_pos.mpr hk).le (hmass₀ x))
      · intro i
        exact mul_pos (sub_pos.mpr hk) (p.hb i)
      · intro x
        simp only [one_mul]
        linarith [p.zeroShift_eq x]
    · have hc' : 0 < p.v₁ * p.γ - p.η := by
        have := mul_lt_mul_of_pos_right hk p.hγ
        linarith
      refine ⟨p.oneShift, p.v₁, -1, Or.inr rfl, ?_, Or.inr ?_, ?_⟩
      · intro x
        rw [oneShift_eval]
        exact add_pos_of_pos_of_nonneg hc'
          (mul_nonneg (sub_pos.mpr hk).le (hmass₁ x))
      · intro i
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hk)) (p.ha i)
      · intro x
        simp only [neg_one_mul]
        linarith [p.oneShift_eq x]

end PureRoPEAtom

/-- Even an arbitrary positive affine fraction may accompany the first pure
head. The second head need not satisfy the pure token-value restriction. -/
theorem vanilla_two_of_nondegenerate_pure_add_positive_fraction {n : ℕ}
    (p : PureRoPEAtom n) (hp : p.v₁ ≠ p.v₀) (q : AffineFraction n)
    (hq : ∀ x, 0 < q.denominator x) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + p.eval x + q.eval x ↔ f x = true)) :
    computableWithSharedHeadsN n 2 f := by
  obtain ⟨F, t, σ, hσ, hF, hFs, hN⟩ := p.exists_uniform_endpoint hp
  let D := p.toAffineFraction.denForm
  let E := q.denForm
  let M := CubeAffine.combine 1 q.numForm (c + t) E
  let V := CubeAffine.combine σ E 0 E
  obtain ⟨r, hr, hsign⟩ := CubeAffine.two_products_uniform_factor D M F V hF hFs
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 2 f).mpr
  refine ⟨r, 0, hr, fun x ↦ ?_⟩
  rw [zero_add, hsign]
  have hD : 0 < D.eval x := p.denominator_pos x
  have hE : 0 < E.eval x := hq x
  have hpe : p.eval x = t + σ * F.eval x / D.eval x := by
    rw [p.eval_eq]
    change p.toAffineFraction.numerator x / D.eval x = _
    rw [hN x]
    change (t * D.eval x + σ * F.eval x) / D.eval x = _
    field_simp
  have hclear : D.eval x * M.eval x + F.eval x * V.eval x =
      D.eval x * E.eval x * (c + p.eval x + q.eval x) := by
    simp only [M, V, CubeAffine.combine_eval, one_mul, zero_mul, add_zero,
      AffineFraction.numForm_eval]
    rw [hpe]
    change D.eval x * (q.numerator x + (c + t) * E.eval x) +
      F.eval x * (σ * E.eval x) =
      D.eval x * E.eval x * (c + (t + σ * F.eval x / D.eval x) +
        q.numerator x / E.eval x)
    field_simp
    ring
  rw [hclear, mul_pos_iff_of_pos_left (mul_pos hD hE)]
  exact hf x

/-- The mixed two-head result also covers equal token values, by perturbing
the pure head while keeping the arbitrary second fraction fixed. -/
theorem vanilla_two_of_pure_add_positive_fraction {n : ℕ}
    (p : PureRoPEAtom n) (q : AffineFraction n)
    (hq : ∀ x, 0 < q.denominator x) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + p.eval x + q.eval x ↔ f x = true)) :
    computableWithSharedHeadsN n 2 f := by
  obtain ⟨p', c', hp', hs⟩ := p.exists_nondegenerate_addend q.eval c
  apply vanilla_two_of_nondegenerate_pure_add_positive_fraction p' hp' q hq c' f
  intro x
  exact (hs x).1.trans (hf x)

/-- Every two-head pure scalar classifier has a two-head realization in the
unchanged shared-embedding vanilla architecture. No complement symmetry is
assumed. The strict perturbation handles equal input-token values. -/
theorem vanilla_two_of_pureRoPEComputable {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n 2 f) :
    computableWithSharedHeadsN n 2 f := by
  obtain ⟨p, q, c, hp, hsign⟩ := pureRoPEComputable_two_nondegenerate hf
  apply vanilla_two_of_nondegenerate_pure_add_positive_fraction p hp q.toAffineFraction
    q.denominator_pos c f
  intro x
  simpa only [← q.eval_eq] using hsign x

theorem pureRoPEComputable_two_iff_vanilla {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n 2 f ↔ computableWithSharedHeadsN n 2 f :=
  ⟨vanilla_two_of_pureRoPEComputable, pureRoPEComputable_of_vanilla⟩

theorem vanilla_of_pureRoPEComputable_le_two {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hH : H ≤ 2) (hf : pureRoPEComputable n H f) :
    computableWithSharedHeadsN n H f := by
  interval_cases H
  · obtain ⟨p, c, hp⟩ := hf
    apply (computableWithSharedHeadsN_iff_affineFractionComputable 0 f).mpr
    exact ⟨Fin.elim0, c, fun h ↦ h.elim0, by simpa using hp⟩
  · exact computableWithSharedHeadsN_of_computableWithHeadsN
      (computable_one_of_isLTF f ((pureRoPEComputable_one_iff_isLTF f).mp hf))
  · exact vanilla_two_of_pureRoPEComputable hf

theorem pureRoPEComputable_iff_vanilla_of_le_two {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (hH : H ≤ 2) :
    pureRoPEComputable n H f ↔ computableWithSharedHeadsN n H f :=
  ⟨vanilla_of_pureRoPEComputable_le_two hH, pureRoPEComputable_of_vanilla⟩

/-- Any strict pure rotary improvement needs at least three pure heads. -/
theorem pureRoPEHStar_eq_vanilla_of_le_two {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : PureRoPEHStar n f ≤ 2) :
    PureRoPEHStar n f = HStar n f := by
  apply le_antisymm (pureRoPEHStar_le_vanilla f)
  have hc := computableWithHeadsN_of_computableWithSharedHeadsN
    (vanilla_of_pureRoPEComputable_le_two hf (pureRoPEHStar_computable f))
  classical
  unfold HStar
  rw [dif_pos (exists_computable f)]
  exact Nat.find_min' _ hc

end HeadComplexity
