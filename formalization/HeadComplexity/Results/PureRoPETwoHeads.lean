import HeadComplexity.Results.RoPEComparison

set_option linter.style.header false

/-!
# Two pure rotary heads never improve vanilla Boolean head count

A nondegenerate pure numerator-denominator pencil contains a positive affine
form with strictly uniform slopes. Two nearby denominators in this pencil
compile the cleared quadratic into two vanilla-admissible fractions. A finite
strictification and perturbation handles coincident token values.
-/

namespace HeadComplexity
namespace RoPETwoHead

open scoped BigOperators

variable {n : ℕ}

/-- An affine scalar form in Boolean coordinates. -/
@[ext] structure Form (n : ℕ) where
  c : ℝ
  v : Fin n → ℝ

noncomputable def Form.eval (a : Form n) (x : Fin n → Bool) : ℝ :=
  a.c + ∑ i, a.v i * boolToReal (x i)

noncomputable def Form.lin (a b : Form n) (r s : ℝ) : Form n :=
  ⟨r * a.c + s * b.c, fun i ↦ r * a.v i + s * b.v i⟩

theorem Form.lin_eval (a b : Form n) (r s : ℝ) (x : Fin n → Bool) :
    (a.lin b r s).eval x = r * a.eval x + s * b.eval x := by
  simp only [Form.eval, Form.lin, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  ring

noncomputable def numerator (r : AffineFraction n) : Form n := ⟨r.b, r.A⟩
noncomputable def denominator (r : AffineFraction n) : Form n := ⟨r.d, r.C⟩

noncomputable def fraction (a b : Form n) : AffineFraction n :=
  ⟨a.v, a.c, b.v, b.c⟩

@[simp] theorem fraction_eval (a b : Form n) (x : Fin n → Bool) :
    (fraction a b).eval x = a.eval x / b.eval x := rfl

/-- Strict slope orientation plus a positive denominator suffices, including
zero-dimensional input where the numerator condition is vacuous. -/
theorem fraction_admissible (a b : Form n) (hb : ∀ x, 0 < b.eval x)
    (hv : (∀ i, 0 < b.v i) ∨ (∀ i, b.v i < 0)) :
    (fraction a b).Admissible := by
  refine ⟨hb, ?_, ?_⟩
  · rcases hv with hp | hn
    · exact Or.inl hp
    · exact Or.inr (Or.inl hn)
  · intro hz
    left
    intro i
    rcases hv with hp | hn
    · exact False.elim ((hp i).ne' (hz i))
    · exact False.elim ((hn i).ne (hz i))

/-- A sufficiently large positive multiple preserves a strict slope
orientation even after adding an arbitrary affine denominator. -/
theorem exists_large_oriented (b d : Form n)
    (hb : (∀ i, 0 < b.v i) ∨ (∀ i, b.v i < 0)) :
    ∃ e : ℝ, 0 < e ∧
      ((∀ i, 0 < e * b.v i + d.v i) ∨ (∀ i, e * b.v i + d.v i < 0)) := by
  classical
  let e : ℝ := 1 + ∑ i, |d.v i / b.v i|
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hbound (i : Fin n) : |d.v i / b.v i| < e := by
    have := Finset.single_le_sum (fun j _ ↦ abs_nonneg (d.v j / b.v j))
      (Finset.mem_univ i)
    dsimp [e]
    linarith
  refine ⟨e, he, ?_⟩
  rcases hb with hp | hn
  · left
    intro i
    have h := (neg_le_abs (d.v i / b.v i)).trans_lt (hbound i)
    have hh : -d.v i < e * b.v i := by
      rw [← neg_div] at h
      exact (div_lt_iff₀ (hp i)).mp h
    linarith
  · right
    intro i
    have h := (neg_le_abs (d.v i / b.v i)).trans_lt (hbound i)
    have hh : e * b.v i < -d.v i := by
      rw [← neg_div] at h
      exact (div_lt_iff_of_neg (hn i)).mp h
    linarith

/-- A quadratic with one positive strictly oriented factor and another positive
factor is represented with two admissible fractions, with exactly the same sign.
This is an identity after multiplication by the new positive denominator. -/
theorem compile_products (a b c d : Form n)
    (hb : ∀ x, 0 < b.eval x) (hd : ∀ x, 0 < d.eval x)
    (hv : (∀ i, 0 < b.v i) ∨ (∀ i, b.v i < 0)) :
    ∃ r : Fin 2 → AffineFraction n, (∀ h, (r h).Admissible) ∧
      ∀ x, (0 < ∑ h, (r h).eval x ↔
        0 < a.eval x * b.eval x + c.eval x * d.eval x) := by
  obtain ⟨e, he, hev⟩ := exists_large_oriented b d hv
  let E := b.lin d e 1
  have hE (x) : 0 < E.eval x := by
    rw [Form.lin_eval]
    nlinarith [hb x, hd x]
  let r : Fin 2 → AffineFraction n := ![fraction c b, fraction (a.lin c 1 (-e)) E]
  refine ⟨r, ?_, ?_⟩
  · intro h
    fin_cases h
    · exact fraction_admissible c b hb hv
    · exact fraction_admissible _ E hE (by simpa [E, Form.lin] using hev)
  · intro x
    have hB0 := (hb x).ne'
    have hE0 := (hE x).ne'
    have hid : (∑ h, (r h).eval x) * (b.eval x * E.eval x) =
        a.eval x * b.eval x + c.eval x * d.eval x := by
      simp only [Fin.sum_univ_two, r, Matrix.cons_val_zero, Matrix.cons_val_one,
        fraction_eval, Form.lin_eval, one_mul]
      change (c.eval x / b.eval x + (a.eval x + -e * c.eval x) / E.eval x) *
        (b.eval x * E.eval x) = _
      field_simp
      rw [show E.eval x = e * b.eval x + d.eval x by simp [E, Form.lin_eval]]
      ring
    rw [← hid, mul_pos_iff_of_pos_right (mul_pos (hb x) (hE x))]


/-- A pure head with increasing token values has a strictly oriented positive
member of its numerator-denominator pencil. -/
theorem pure_oriented_pencil_increasing (p : PureRoPEAtom n) (hv : p.v₀ < p.v₁) :
    ∃ (b : Form n) (r s : ℝ), r * r = 1 ∧
      b = (numerator p.toAffineFraction).lin (denominator p.toAffineFraction) r s ∧
      (∀ x, 0 < b.eval x) ∧
      ((∀ i, 0 < b.v i) ∨ (∀ i, b.v i < 0)) := by
  let N := numerator p.toAffineFraction
  let D := denominator p.toAffineFraction
  have hsum : ∑ i, p.a i * p.v₀ = p.v₀ * ∑ i, p.a i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  by_cases hq : p.v₀ * p.γ < p.η
  · let b := N.lin D 1 (-p.v₀)
    have hbv (i) : b.v i = p.b i * (p.v₁ - p.v₀) := by
      dsimp [b, N, D, numerator, denominator, Form.lin, PureRoPEAtom.toAffineFraction]
      ring
    have hbc : b.c = p.η - p.v₀ * p.γ := by
      dsimp [b, N, D, numerator, denominator, Form.lin, PureRoPEAtom.toAffineFraction]
      rw [hsum]
      ring
    refine ⟨b, 1, -p.v₀, by norm_num, rfl, ?_, Or.inl ?_⟩
    · intro x
      rw [Form.eval, hbc]
      apply add_pos_of_pos_of_nonneg (sub_pos.mpr hq)
      apply Finset.sum_nonneg
      intro i _
      rw [hbv]
      cases x i
      · simp [boolToReal]
      · change 0 ≤ p.b i * (p.v₁ - p.v₀) * 1
        simpa only [mul_one] using mul_nonneg (p.hb i).le (sub_pos.mpr hv).le
    · intro i
      rw [hbv]
      exact mul_pos (p.hb i) (sub_pos.mpr hv)
  · let b := N.lin D (-1) p.v₁
    have hbv (i) : b.v i = -p.a i * (p.v₁ - p.v₀) := by
      dsimp [b, N, D, numerator, denominator, Form.lin, PureRoPEAtom.toAffineFraction]
      ring
    have hbc : b.c = p.v₁ * p.γ - p.η + ∑ i, p.a i * (p.v₁ - p.v₀) := by
      dsimp [b, N, D, numerator, denominator, Form.lin, PureRoPEAtom.toAffineFraction]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    have hq' : 0 < p.v₁ * p.γ - p.η := by
      have hh := mul_lt_mul_of_pos_right hv p.hγ
      linarith
    refine ⟨b, -1, p.v₁, by norm_num, rfl, ?_, Or.inr ?_⟩
    · intro x
      rw [Form.eval, hbc, add_assoc, ← Finset.sum_add_distrib]
      apply add_pos_of_pos_of_nonneg hq'
      apply Finset.sum_nonneg
      intro i _
      rw [hbv]
      cases x i
      · change 0 ≤ p.a i * (p.v₁ - p.v₀) + -p.a i * (p.v₁ - p.v₀) * 0
        simpa only [mul_zero, add_zero] using
          mul_nonneg (p.ha i).le (sub_pos.mpr hv).le
      · change 0 ≤ p.a i * (p.v₁ - p.v₀) + -p.a i * (p.v₁ - p.v₀) * 1
        nlinarith
    · intro i
      rw [hbv]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (p.ha i)) (sub_pos.mpr hv)

noncomputable def negValues (p : PureRoPEAtom n) : PureRoPEAtom n :=
  { p with η := -p.η, v₀ := -p.v₀, v₁ := -p.v₁ }

/-- Distinct token values suffice in either order. -/
theorem pure_oriented_pencil (p : PureRoPEAtom n) (hv : p.v₀ ≠ p.v₁) :
    ∃ (b : Form n) (r s : ℝ), r * r = 1 ∧
      b = (numerator p.toAffineFraction).lin (denominator p.toAffineFraction) r s ∧
      (∀ x, 0 < b.eval x) ∧
      ((∀ i, 0 < b.v i) ∨ (∀ i, b.v i < 0)) := by
  rcases lt_or_gt_of_ne hv with h | h
  · exact pure_oriented_pencil_increasing p h
  · obtain ⟨b, r, s, hr, hb, hpos, hor⟩ :=
      pure_oriented_pencil_increasing (negValues p) (by simpa [negValues] using h)
    refine ⟨b, -r, s, by nlinarith [hr], ?_, hpos, hor⟩
    rw [hb]
    ext i
    · simp only [Form.lin, numerator, denominator, PureRoPEAtom.toAffineFraction,
        negValues, mul_neg, Finset.sum_neg_distrib]
      ring
    · simp only [Form.lin, numerator, denominator, PureRoPEAtom.toAffineFraction,
        negValues]
      ring

/-- Nondegenerate pure two-head scores compile without an approximation. -/
theorem compile_pure_two (p q : PureRoPEAtom n) (t : ℝ) (hv : p.v₀ ≠ p.v₁) :
    ∃ r : Fin 2 → AffineFraction n, (∀ h, (r h).Admissible) ∧
      ∀ x, (0 < ∑ h, (r h).eval x ↔ 0 < t + p.eval x + q.eval x) := by
  obtain ⟨b, r, s, hr, hb, hbp, hbv⟩ := pure_oriented_pencil p hv
  let D := denominator p.toAffineFraction
  let N := numerator p.toAffineFraction
  let E := denominator q.toAffineFraction
  let M := numerator q.toAffineFraction
  let A := E.lin E r 0
  let C := M.lin E 1 (t - r * s)
  have hD (x) : 0 < D.eval x := p.denominator_pos x
  have hE (x) : 0 < E.eval x := q.denominator_pos x
  obtain ⟨R, hR, hsign⟩ := compile_products A b C D hbp hD hbv
  refine ⟨R, hR, fun x ↦ (hsign x).trans ?_⟩
  have hB : b.eval x = r * N.eval x + s * D.eval x := by
    rw [hb, Form.lin_eval]
  have hid : A.eval x * b.eval x + C.eval x * D.eval x =
      (t + p.eval x + q.eval x) * (D.eval x * E.eval x) := by
    rw [p.eval_eq, q.eval_eq]
    change _ = (t + N.eval x / D.eval x + M.eval x / E.eval x) * _
    rw [show A.eval x = r * E.eval x by simp [A, Form.lin_eval]]
    rw [show C.eval x = M.eval x + (t - r * s) * E.eval x by simp [C, Form.lin_eval]]
    rw [hB]
    field_simp [(hD x).ne', (hE x).ne']
    linear_combination N.eval x * E.eval x * hr
  rw [hid, mul_pos_iff_of_pos_right (mul_pos (hD x) (hE x))]


/-- A uniform positive downward shift fits below all positive scores on the
finite input cube. No positive scores is included. -/
theorem exists_positive_shift (S : (Fin n → Bool) → ℝ)
    (f : (Fin n → Bool) → Bool) (hS : ∀ x, 0 < S x ↔ f x = true) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, f x = true → ε < S x := by
  classical
  let T := Finset.univ.filter fun x ↦ f x = true
  by_cases hT : T.Nonempty
  · refine ⟨T.inf' hT S / 2, ?_, ?_⟩
    · apply half_pos
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact (hS x).mpr (Finset.mem_filter.mp hx).2
    · intro x hx
      have hmem : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
      have hle := Finset.inf'_le S hmem
      have hp : 0 < T.inf' hT S := by
        rw [Finset.lt_inf'_iff]
        intro y hy
        exact (hS y).mpr (Finset.mem_filter.mp hy).2
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    exact False.elim (hT ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩)

noncomputable def raiseOneValue (p : PureRoPEAtom n) (δ : ℝ) : PureRoPEAtom n :=
  { p with v₁ := p.v₁ + δ }

/-- Raising one token value by a nonnegative amount changes every pure score by
an amount between zero and that increment, since its attention mass is in [0,1]. -/
theorem raiseOneValue_bounds (p : PureRoPEAtom n) (δ : ℝ) (hδ : 0 ≤ δ)
    (x : Fin n → Bool) :
    p.eval x ≤ (raiseOneValue p δ).eval x ∧
      (raiseOneValue p δ).eval x ≤ p.eval x + δ := by
  let B : ℝ := ∑ i, if x i then p.b i else 0
  let D : ℝ := p.γ + ∑ i, if x i then p.b i else p.a i
  have hD : 0 < D := by
    simpa [D, PureRoPEAtom.denominator_eq] using p.denominator_pos x
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro i _
    split
    · exact (p.hb i).le
    · exact le_refl 0
  have hBD : B ≤ D := by
    have hsum : B ≤ ∑ i, if x i then p.b i else p.a i := by
      apply Finset.sum_le_sum
      intro i _
      split
      · exact le_refl _
      · exact (p.ha i).le
    dsimp [D]
    linarith [p.hγ]
  have hnum :
      (p.η + ∑ i, if x i then p.b i * (p.v₁ + δ) else p.a i * p.v₀) =
        (p.η + ∑ i, if x i then p.b i * p.v₁ else p.a i * p.v₀) + δ * B := by
    dsimp [B]
    rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split <;> ring
  have heval : (raiseOneValue p δ).eval x = p.eval x + δ * B / D := by
    dsimp [raiseOneValue, PureRoPEAtom.eval]
    rw [hnum, add_div]
  rw [heval]
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ hB) hD.le)
  · have hh : δ * B / D ≤ δ := (div_le_iff₀ hD).mpr
      (mul_le_mul_of_nonneg_left hBD hδ)
    linarith

/-- Every pure two-head Boolean classifier has a representation whose first
head has distinct token values, without changing any Boolean label. -/
theorem nondegenerate_pure_two {f : (Fin n → Bool) → Bool}
    (hf : pureRoPEComputable n 2 f) :
    ∃ (p q : PureRoPEAtom n) (t : ℝ), p.v₀ ≠ p.v₁ ∧
      ∀ x, (0 < t + p.eval x + q.eval x ↔ f x = true) := by
  obtain ⟨p, c, hp⟩ := hf
  have hS : ∀ x, 0 < c + (p 0).eval x + (p 1).eval x ↔ f x = true := by
    intro x
    simpa [Fin.sum_univ_two, add_assoc] using hp x
  by_cases hv : (p 0).v₀ ≠ (p 0).v₁
  · exact ⟨p 0, p 1, c, hv, hS⟩
  · have hv' : (p 0).v₀ = (p 0).v₁ := not_ne_iff.mp hv
    obtain ⟨ε, hε, hεS⟩ := exists_positive_shift
      (fun x ↦ c + (p 0).eval x + (p 1).eval x) f hS
    refine ⟨raiseOneValue (p 0) (ε / 2), p 1, c - ε, ?_, ?_⟩
    · dsimp [raiseOneValue]
      rw [hv']
      linarith
    · intro x
      have hb := raiseOneValue_bounds (p 0) (ε / 2) (by positivity) x
      constructor
      · intro hnew
        apply (hS x).mp
        linarith
      · intro htrue
        have := hεS x htrue
        linarith

end RoPETwoHead

/-- Pure rotary attention cannot improve the Boolean head count from two to
three, without any complement-invariance hypothesis. -/
theorem vanillaComputable_two_of_pureRoPE {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : pureRoPEComputable n 2 f) : computableWithSharedHeadsN n 2 f := by
  obtain ⟨p, q, t, hv, hsign⟩ := RoPETwoHead.nondegenerate_pure_two hf
  obtain ⟨r, hr, hR⟩ := RoPETwoHead.compile_pure_two p q t hv
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 2 f).mpr
  exact ⟨r, 0, hr, fun x ↦ by simpa only [zero_add] using (hR x).trans (hsign x)⟩

/-- At a budget of two heads the unchanged vanilla architecture and the pure
rotary scalar model compute exactly the same Boolean functions. -/
theorem pureRoPEComputable_two_iff_vanilla {n : ℕ} (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n 2 f ↔ computableWithSharedHeadsN n 2 f :=
  ⟨vanillaComputable_two_of_pureRoPE, pureRoPEComputable_of_vanilla⟩


/-- The equality also includes the zero- and one-head budgets. -/
theorem vanillaComputable_of_pureRoPE_le_two {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hH : H ≤ 2)
    (hf : pureRoPEComputable n H f) : computableWithSharedHeadsN n H f := by
  interval_cases H
  · obtain ⟨p, c, hp⟩ := hf
    apply (computableWithSharedHeadsN_iff_affineFractionComputable 0 f).mpr
    refine ⟨Fin.elim0, c, (fun h ↦ Fin.elim0 h), ?_⟩
    simpa using hp
  · apply (computableWithHeadsN_iff_computableWithSharedHeadsN n 1 f).mp
    exact computable_one_of_isLTF f ((pureRoPEComputable_one_iff_isLTF f).mp hf)
  · exact vanillaComputable_two_of_pureRoPE hf

/-- The minimum pure head count equals vanilla whenever it is at most two. -/
theorem pureRoPEHStar_eq_vanilla_of_le_two {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : PureRoPEHStar n f ≤ 2) : PureRoPEHStar n f = HStar n f := by
  classical
  apply le_antisymm (pureRoPEHStar_le_vanilla f)
  have hc := vanillaComputable_of_pureRoPE_le_two hf (pureRoPEHStar_computable f)
  have hc' := (computableWithHeadsN_iff_computableWithSharedHeadsN n _ f).mpr hc
  have hex := exists_computable f
  unfold HStar
  rw [dif_pos hex]
  exact Nat.find_min' hex hc'

/-- Any strict pure rotary Boolean separation needs at least three pure heads. -/
theorem pureRoPE_separation_requires_three_heads {n : ℕ}
    (f : (Fin n → Bool) → Bool) (h : PureRoPEHStar n f < HStar n f) :
    3 ≤ PureRoPEHStar n f := by
  by_contra hn
  have he := pureRoPEHStar_eq_vanilla_of_le_two f (by omega)
  omega

end HeadComplexity
