import HeadComplexity.Results.AffineFractionNormalForm

set_option linter.style.header false

/-!
# Scalar atoms for rotary attention

These are scalar normal forms, not a formalization of rotation matrices.
The fixed-frequency interpolation argument connecting them to literal RoPE
is proved in the accompanying Markdown writeup.
-/

namespace HeadComplexity

open scoped BigOperators

/-- A head without additive positional embeddings, after its position-dependent
logits have been interpolated. Values depend only on the token. -/
structure PureRoPEAtom (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  γ : ℝ
  η : ℝ
  v₀ : ℝ
  v₁ : ℝ
  ha : ∀ i, 0 < a i
  hb : ∀ i, 0 < b i
  hγ : 0 < γ

namespace PureRoPEAtom

variable {n : ℕ}

noncomputable def eval (p : PureRoPEAtom n) (x : Fin n → Bool) : ℝ :=
  (p.η + ∑ i, if x i then p.b i * p.v₁ else p.a i * p.v₀) /
    (p.γ + ∑ i, if x i then p.b i else p.a i)

noncomputable def toAffineFraction (p : PureRoPEAtom n) : AffineFraction n where
  A i := p.b i * p.v₁ - p.a i * p.v₀
  b := p.η + ∑ i, p.a i * p.v₀
  C i := p.b i - p.a i
  d := p.γ + ∑ i, p.a i

theorem denominator_eq (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.toAffineFraction.denominator x =
      p.γ + ∑ i, if x i then p.b i else p.a i := by
  unfold AffineFraction.denominator toAffineFraction
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

theorem denominator_pos (p : PureRoPEAtom n) (x : Fin n → Bool) :
    0 < p.toAffineFraction.denominator x := by
  rw [denominator_eq]
  apply add_pos_of_pos_of_nonneg p.hγ
  apply Finset.sum_nonneg
  intro i _
  split <;> exact le_of_lt (by first | exact p.hb i | exact p.ha i)

theorem eval_eq (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.eval x = p.toAffineFraction.eval x := by
  have hnum : p.toAffineFraction.numerator x =
      p.η + ∑ i, if x i then p.b i * p.v₁ else p.a i * p.v₀ := by
    unfold AffineFraction.numerator toAffineFraction
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [boolToReal]
  simp only [eval, AffineFraction.eval, denominator_eq, hnum]

noncomputable def flip (p : PureRoPEAtom n) : PureRoPEAtom n where
  a := p.b
  b := p.a
  γ := p.γ
  η := p.η
  v₀ := p.v₁
  v₁ := p.v₀
  ha := p.hb
  hb := p.ha
  hγ := p.hγ

theorem flip_eval (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.flip.eval x = p.eval (fun i ↦ !(x i)) := by
  have h (a b : Fin n → ℝ) :
      (∑ i, if x i then a i else b i) =
        ∑ i, if !(x i) then b i else a i := by
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  exact congrArg₂ (· / ·) (congrArg (p.η + ·) (h _ _))
    (congrArg (p.γ + ·) (h _ _))

end PureRoPEAtom

namespace AffineFraction

variable {n : ℕ}

/-- Complement every input, retaining the actual affine coefficients. -/
noncomputable def flip (r : AffineFraction n) : AffineFraction n where
  A i := -r.A i
  b := r.b + ∑ i, r.A i
  C i := -r.C i
  d := r.d + ∑ i, r.C i

theorem flip_eval (r : AffineFraction n) (x : Fin n → Bool) :
    r.flip.eval x = r.eval (fun i ↦ !(x i)) := by
  have h (v : Fin n → ℝ) (c : ℝ) :
      c + ∑ i, v i + ∑ i, -v i * boolToReal (x i) =
        c + ∑ i, v i * boolToReal (!(x i)) := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [boolToReal]
  exact congrArg₂ (· / ·) (h r.A r.b) (h r.C r.d)

/-- The constants can be chosen after the positive weights and value slopes. -/
private theorem realize_pure (r : AffineFraction n) (a b : Fin n → ℝ) (v₀ v₁ : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hs : ∑ i, a i < r.d)
    (hA : ∀ i, b i * v₁ - a i * v₀ = r.A i)
    (hC : ∀ i, b i - a i = r.C i) :
    ∃ p : PureRoPEAtom n, p.toAffineFraction = r := by
  refine ⟨{
    a := a, b := b, γ := r.d - ∑ i, a i,
    η := r.b - ∑ i, a i * v₀, v₀ := v₀, v₁ := v₁,
    ha := ha, hb := hb, hγ := sub_pos.mpr hs }, ?_⟩
  ext i <;> simp [PureRoPEAtom.toAffineFraction, hA, hC]

private theorem scale_weights (w : Fin n → ℝ) (d : ℝ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) :
    ∃ q : ℝ, 0 < q ∧ (∑ i, w i / q) < d := by
  let S := ∑ i, w i
  let q := 1 + S / d
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ (hw i).le
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q, hq, ?_⟩
  rw [← Finset.sum_div]
  apply (div_lt_iff₀ hq).mpr
  have hprod : d * q = d + S := by dsimp [q]; field_simp
  change S < d * q
  rw [hprod]
  linarith

/-- Positive denominator slopes allow arbitrary numerator slopes, even with
token-only values. This preserves the entire score, not only its signs. -/
theorem exists_pure_positive (r : AffineFraction n)
    (hd : 0 < r.d) (hC : ∀ i, 0 < r.C i) :
    ∃ p : PureRoPEAtom n, p.toAffineFraction = r := by
  classical
  let t := 1 + ∑ i, |r.A i / r.C i|
  have hw (i) : 0 < r.A i + t * r.C i := by
    have hle : |r.A i / r.C i| ≤ ∑ j, |r.A j / r.C j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (r.A j / r.C j)) (Finset.mem_univ i)
    have hlt : -r.A i / r.C i < t := by
      have := neg_le_abs (r.A i / r.C i)
      rw [neg_div]
      dsimp [t]
      linarith
    have := (div_lt_iff₀ (hC i)).mp hlt
    linarith
  obtain ⟨q, hq, hs⟩ := scale_weights (fun i ↦ r.A i + t * r.C i) r.d hw hd
  apply realize_pure r (fun i ↦ (r.A i + t * r.C i) / q)
    (fun i ↦ (r.A i + t * r.C i) / q + r.C i) (-(t + q)) (-t)
    (fun i ↦ div_pos (hw i) hq)
    (fun i ↦ add_pos (div_pos (hw i) hq) (hC i)) hs
  · intro i
    field_simp
    ring
  · intro i
    ring

private theorem exists_pure_constant (r : AffineFraction n) (hd : 0 < r.d)
    (hC : ∀ i, r.C i = 0) (hA : UniformSign r.A) :
    ∃ p : PureRoPEAtom n, p.toAffineFraction = r := by
  rcases hA with hpos | hneg | hzero
  · obtain ⟨q, hq, hs⟩ := scale_weights r.A r.d hpos hd
    exact realize_pure r (fun i ↦ r.A i / q) (fun i ↦ r.A i / q) 0 q
      (fun i ↦ div_pos (hpos i) hq) (fun i ↦ div_pos (hpos i) hq) hs
      (fun i ↦ by simp [hq.ne']) (fun i ↦ by simp [hC])
  · obtain ⟨q, hq, hs⟩ := scale_weights (fun i ↦ -r.A i) r.d
      (fun i ↦ neg_pos.mpr (hneg i)) hd
    apply realize_pure r (fun i ↦ -r.A i / q) (fun i ↦ -r.A i / q) 0 (-q)
      (fun i ↦ div_pos (neg_pos.mpr (hneg i)) hq)
      (fun i ↦ div_pos (neg_pos.mpr (hneg i)) hq) hs
    · intro i
      field_simp
      ring
    · intro i
      simp [hC]
  · obtain ⟨q, hq, hs⟩ := scale_weights (fun _ : Fin n ↦ (1 : ℝ)) r.d
      (fun _ ↦ by norm_num) hd
    exact realize_pure r (fun _ ↦ 1 / q) (fun _ ↦ 1 / q) 0 0
      (fun _ ↦ one_div_pos.mpr hq) (fun _ ↦ one_div_pos.mpr hq) hs
      (fun i ↦ by simp [hzero]) (fun i ↦ by simp [hC])

/-- Every admissible vanilla ratio has an exactly equal pure rotary scalar atom. -/
theorem exists_pure (r : AffineFraction n) (hr : r.Admissible) :
    ∃ p : PureRoPEAtom n, ∀ x, p.eval x = r.eval x := by
  have hd : 0 < r.d := by
    simpa [denominator, boolToReal] using hr.1 (fun _ ↦ false)
  rcases hr.2.1 with hpos | hneg | hzero
  · obtain ⟨p, hp⟩ := r.exists_pure_positive hd hpos
    exact ⟨p, fun x ↦ by rw [p.eval_eq, hp]⟩
  · have hd' : 0 < r.flip.d := by
      simpa [flip, denominator, boolToReal] using hr.1 (fun _ ↦ true)
    obtain ⟨p, hp⟩ := r.flip.exists_pure_positive hd' (fun i ↦ neg_pos.mpr (hneg i))
    refine ⟨p.flip, fun x ↦ ?_⟩
    rw [PureRoPEAtom.flip_eval, p.eval_eq, hp, flip_eval]
    simp only [Bool.not_not]
  · obtain ⟨p, hp⟩ := exists_pure_constant r hd hzero (hr.2.2 hzero)
    exact ⟨p, fun x ↦ by rw [p.eval_eq, hp]⟩

end AffineFraction

/-- Computation in the scalar normal form for pure rotary attention. -/
def pureRoPEComputable (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (p : Fin H → PureRoPEAtom n) (c : ℝ),
    ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)

theorem pureRoPEComputable_of_vanilla {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithSharedHeadsN n H f) : pureRoPEComputable n H f := by
  obtain ⟨r, c, hr, hf⟩ :=
    (computableWithSharedHeadsN_iff_affineFractionComputable H f).mp hf
  choose p hp using fun h ↦ (r h).exists_pure (hr h)
  exact ⟨p, c, fun x ↦ by simpa only [hp] using hf x⟩

/-- A scalar rotary head with additive positional embeddings retained. -/
structure RetainedRoPEAtom (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  γ : ℝ
  η : ℝ
  m : Fin n → ℝ
  δ : ℝ
  ha : ∀ i, 0 < a i
  hb : ∀ i, 0 < b i
  hγ : 0 < γ

namespace RetainedRoPEAtom

variable {n : ℕ}

noncomputable def toAffineFraction (p : RetainedRoPEAtom n) : AffineFraction n where
  A i := p.b i * (p.m i + p.δ) - p.a i * p.m i
  b := p.η + ∑ i, p.a i * p.m i
  C i := p.b i - p.a i
  d := p.γ + ∑ i, p.a i

noncomputable def eval (p : RetainedRoPEAtom n) (x : Fin n → Bool) : ℝ :=
  p.toAffineFraction.eval x

theorem denominator_pos (p : RetainedRoPEAtom n) (x : Fin n → Bool) :
    0 < p.toAffineFraction.denominator x := by
  let q : PureRoPEAtom n := ⟨p.a, p.b, p.γ, 0, 0, 0, p.ha, p.hb, p.hγ⟩
  exact q.denominator_pos x

theorem eval_eq_weighted (p : RetainedRoPEAtom n) (x : Fin n → Bool) :
    p.eval x =
      (p.η + ∑ i, if x i then p.b i * (p.m i + p.δ) else p.a i * p.m i) /
      (p.γ + ∑ i, if x i then p.b i else p.a i) := by
  have hn : p.toAffineFraction.numerator x =
      p.η + ∑ i, if x i then p.b i * (p.m i + p.δ) else p.a i * p.m i := by
    unfold AffineFraction.numerator toAffineFraction
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp [boolToReal]
  let q : PureRoPEAtom n := ⟨p.a, p.b, p.γ, 0, 0, 0, p.ha, p.hb, p.hγ⟩
  exact congrArg₂ (· / ·) hn (q.denominator_eq x)

end RetainedRoPEAtom

noncomputable def PureRoPEAtom.toRetained {n : ℕ} (p : PureRoPEAtom n) :
    RetainedRoPEAtom n where
  a := p.a
  b := p.b
  γ := p.γ
  η := p.η
  m _ := p.v₀
  δ := p.v₁ - p.v₀
  ha := p.ha
  hb := p.hb
  hγ := p.hγ

theorem PureRoPEAtom.toRetained_eval {n : ℕ} (p : PureRoPEAtom n)
    (x : Fin n → Bool) : p.toRetained.eval x = p.eval x := by
  rw [p.eval_eq]
  have h : p.toRetained.toAffineFraction = p.toAffineFraction := by
    ext i <;> simp [toRetained, RetainedRoPEAtom.toAffineFraction, toAffineFraction]
  exact congrArg (fun r : AffineFraction n ↦ r.eval x) h

def retainedRoPEComputable (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (p : Fin H → RetainedRoPEAtom n) (c : ℝ),
    ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)

theorem retainedRoPEComputable_of_pure {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : pureRoPEComputable n H f) : retainedRoPEComputable n H f := by
  obtain ⟨p, c, hp⟩ := hf
  exact ⟨fun h ↦ (p h).toRetained, c,
    fun x ↦ by simpa only [PureRoPEAtom.toRetained_eval] using hp x⟩

end HeadComplexity
