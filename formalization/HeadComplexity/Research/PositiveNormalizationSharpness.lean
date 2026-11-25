import HeadComplexity.Research.SameWidthPositiveNormalization

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.PositiveNormalizationSharpness
open Finset RelativeMarginQuantifiers
open scoped BigOperators

variable {n H : ℕ}

/-- For a nonconstant target, nonnegative heads with bias minus one can never
have relative margin above one third, at any width or amplitude. -/
theorem relativeMargin_le_third
    {f : (Fin n → Bool) → Bool} {φ : Fin H → FracAtom n}
    (hs : StrictlyRepresents f φ (-1))
    (hn : ∀ h x, 0 ≤ (φ h).eval x)
    (hfalse : ∃ x, f x = false) (htrue : ∃ x, f x = true) :
    relativeMargin f φ (-1) ≤ 1/3 := by
  let γ := relativeMargin f φ (-1)
  let A := amplitude φ (-1)
  have hA : 0 < A := amplitude_pos_of_strict hs
  have hpoint := (le_relativeMargin_iff hs).mp (le_refl γ)
  obtain ⟨x,hx⟩ := hfalse
  obtain ⟨y,hy⟩ := htrue
  have hx' := hpoint x
  have hy' := hpoint y
  have hxn : 0 ≤ ∑ h, (φ h).eval x := sum_nonneg fun h _ => hn h x
  have hys : (∑ h, (φ h).eval y) ≤ ∑ h, atomSup (φ h) :=
    sum_le_sum fun h _ => (le_abs_self _).trans (abs_eval_le_atomSup (φ h) y)
  have hneg : γ*A ≤ 1 := by
    simp only [signedLabel,hx,Bool.false_eq_true,↓reduceIte,score] at hx'
    linarith
  have hpos : γ*A ≤ A-2 := by
    have he : A = 1+∑ h, atomSup (φ h) := by simp [A,amplitude]
    simp only [signedLabel,hy,↓reduceIte,one_mul,score] at hy'
    linarith
  by_contra hg
  have hg' : 1/3 < γ := lt_of_not_ge hg
  have hm := mul_pos hA (sub_pos.mpr hg')
  nlinarith

def literalHead : FracAtom 1 where
  η := -2
  δ := 4
  γ := 1
  α := 1
  ρ := fun _ => 1
  m := fun _ => 0
  hγ := by norm_num
  hα := by norm_num
  hρ := by intro i; norm_num

def literal : (Fin 1 → Bool) → Bool := fun x => x 0

@[simp] theorem literalHead_eval (x : Fin 1 → Bool) :
    literalHead.eval x = if x 0 then 1 else -1 := by
  simp [literalHead,FracAtom.eval,FracAtom.wt]
  split <;> norm_num

/-- A genuine width-one source has relative margin exactly one. -/
theorem literal_source_margin :
    StrictlyRepresents literal (fun _ : Fin 1 => literalHead) 0 ∧
    relativeMargin literal (fun _ : Fin 1 => literalHead) 0 = 1 := by
  have hv (x : Fin 1 → Bool) :
      signedLabel literal x * score (fun _ : Fin 1 => literalHead) 0 x = 1 := by
    cases hx : x 0 <;> simp [signedLabel,literal,score,hx]
  have ha : atomSup literalHead = 1 := by
    have hh (x : Fin 1 → Bool) : |literalHead.eval x| = 1 := by
      rw [literalHead_eval]; split <;> norm_num
    unfold atomSup
    simp_rw [hh]
    simp
  constructor
  · intro x; rw [hv]; norm_num
  · norm_num [relativeMargin,minimumSignedScore,hv,amplitude,ha]

/-- The normalized literal attains the universal upper bound, so the factor
three in same-width positive normalization cannot be improved uniformly. -/
theorem literal_normalized_margin :
    let φ : Fin 1 → FracAtom 1 := fun _ => literalHead.translate 1
    (∀ h x, 0 ≤ (φ h).eval x) ∧
    (∀ h, ∃ x, (φ h).eval x = 0) ∧
    amplitude φ (-1) = 3 ∧ StrictlyRepresents literal φ (-1) ∧
    relativeMargin literal φ (-1) = 1/3 := by
  dsimp only
  have he (x : Fin 1 → Bool) : (literalHead.translate 1).eval x = if x 0 then 2 else 0 := by
    simp only [FracAtom.translate_eval,literalHead_eval]
    split <;> norm_num
  have hv (x : Fin 1 → Bool) :
      signedLabel literal x * score (fun _ : Fin 1 => literalHead.translate 1) (-1) x = 1 := by
    cases hx : x 0 <;> norm_num [signedLabel,literal,score,he,hx]
  have ha : atomSup (literalHead.translate 1) = 2 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro x _
      rw [he]; split <;> norm_num
    · have hh := abs_eval_le_atomSup (literalHead.translate 1) (fun _ => true)
      simpa [he] using hh
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro h x
    rw [he]; split <;> norm_num
  · intro h
    exact ⟨(fun _ => false),by simp [he]⟩
  · norm_num [amplitude,ha]
  · intro x; rw [hv]; norm_num
  · norm_num [relativeMargin,minimumSignedScore,hv,amplitude,ha]


/-- The one-bit literal witnesses exact sharpness inside the canonical class. -/
theorem hasNormalizedMargin_literal_iff (γ : ℝ) :
    SameWidthPositiveNormalization.HasNormalizedMargin 1 1 literal γ ↔ γ ≤ 1/3 := by
  constructor
  · rintro ⟨φ,hn,hz,hD,hs,hγ⟩
    exact hγ.trans (relativeMargin_le_third hs hn
      ⟨(fun _ => false),rfl⟩ ⟨(fun _ => true),rfl⟩)
  · intro hγ
    obtain ⟨hn,hz,hD,hs,hm⟩ := literal_normalized_margin
    exact ⟨(fun _ => literalHead.translate 1),hn,hz,hD.le,hs,by simpa [hm] using hγ⟩

end HeadComplexity.PositiveNormalizationSharpness
