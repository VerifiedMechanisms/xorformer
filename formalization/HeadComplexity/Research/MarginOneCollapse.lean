import HeadComplexity.Research.RelativeMarginQuantifiers

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.MarginOneCollapse
open Finset RelativeMarginQuantifiers
open scoped BigOperators

variable {n H : ℕ}

/-- Equality in the whole-cube amplitude bound forces every summand to align
with every label. This includes the bias as a separate summand. -/
theorem alignment_of_margin_one
    {f : (Fin n → Bool) → Bool} {φ : Fin H → FracAtom n} {b : ℝ}
    (hs : StrictlyRepresents f φ b) (hm : 1 ≤ relativeMargin f φ b) :
    ∀ x, signedLabel f x * b = |b| ∧
      ∀ h, signedLabel f x * (φ h).eval x = atomSup (φ h) := by
  intro x
  have hlo := (le_relativeMargin_iff hs).mp hm x
  have hb : signedLabel f x * b ≤ |b| := by
    calc
      _ ≤ |signedLabel f x * b| := le_abs_self _
      _ = |b| := by rw [abs_mul,abs_signedLabel,one_mul]
  have hh (h : Fin H) : signedLabel f x * (φ h).eval x ≤ atomSup (φ h) := by
    calc
      _ ≤ |signedLabel f x * (φ h).eval x| := le_abs_self _
      _ = |(φ h).eval x| := by rw [abs_mul,abs_signedLabel,one_mul]
      _ ≤ _ := abs_eval_le_atomSup _ _
  have hnonneg : 0 ≤ ∑ h, (atomSup (φ h)-signedLabel f x*(φ h).eval x) :=
    sum_nonneg fun h _ => sub_nonneg.mpr (hh h)
  have htotal : (|b|-signedLabel f x*b)+
      ∑ h, (atomSup (φ h)-signedLabel f x*(φ h).eval x) ≤ 0 := by
    simp only [one_mul,amplitude,score,mul_add] at hlo
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    linarith
  have hsum : (∑ h, (atomSup (φ h)-signedLabel f x*(φ h).eval x)) = 0 := by
    linarith
  refine ⟨by linarith,?_⟩
  intro h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin H))) => sub_nonneg.mpr (hh i))).mp hsum
  have hi := hz h (Finset.mem_univ h)
  linarith

/-- A nonconstant margin-one certificate necessarily has zero bias. -/
theorem bias_eq_zero_of_margin_one
    {f : (Fin n → Bool) → Bool} {φ : Fin H → FracAtom n} {b : ℝ}
    (hs : StrictlyRepresents f φ b) (hm : 1 ≤ relativeMargin f φ b)
    (hfalse : ∃ x, f x = false) (htrue : ∃ x, f x = true) : b = 0 := by
  obtain ⟨x,hx⟩ := hfalse
  obtain ⟨y,hy⟩ := htrue
  have hx' := (alignment_of_margin_one hs hm x).1
  have hy' := (alignment_of_margin_one hs hm y).1
  simp only [signedLabel_of_false hx,neg_one_mul] at hx'
  simp only [signedLabel_of_true hy,one_mul] at hy'
  linarith

/-- Each nonzero head in a margin-one certificate is already a positive
multiple of the complete signed truth table. -/
theorem eval_eq_norm_mul_signedLabel
    {f : (Fin n → Bool) → Bool} {φ : Fin H → FracAtom n} {b : ℝ}
    (hs : StrictlyRepresents f φ b) (hm : 1 ≤ relativeMargin f φ b)
    (h : Fin H) (x : Fin n → Bool) :
    (φ h).eval x = atomSup (φ h)*signedLabel f x := by
  have hh := (alignment_of_margin_one hs hm x).2 h
  cases hx : f x <;> simp [signedLabel,hx] at hh ⊢ <;> linarith

/-- Arbitrary width cannot create a new nonconstant table attaining relative
margin one: one of its genuine heads already attains that margin by itself. -/
theorem hasRelativeMargin_one_head
    {f : (Fin n → Bool) → Bool}
    (hf : HasRelativeMargin n H f 1)
    (hfalse : ∃ x, f x = false) (htrue : ∃ x, f x = true) :
    HasRelativeMargin n 1 f 1 := by
  obtain ⟨φ,b,hs,hm⟩ := hf
  have hb := bias_eq_zero_of_margin_one hs hm hfalse htrue
  have hsum : 0 < ∑ h, atomSup (φ h) := by
    simpa [amplitude,hb] using amplitude_pos_of_strict hs
  have hex : ∃ h, 0 < atomSup (φ h) := by
    by_contra hn
    push Not at hn
    have hle := Finset.sum_nonpos (s := Finset.univ) (fun h _ => hn h)
    linarith
  obtain ⟨h,hh⟩ := hex
  let ψ : Fin 1 → FracAtom n := fun _ => φ h
  have he (x : Fin n → Bool) : signedLabel f x * score ψ 0 x = atomSup (φ h) := by
    simpa [ψ,score] using (alignment_of_margin_one hs hm x).2 h
  have hs' : StrictlyRepresents f ψ 0 := by
    intro x
    rw [he]
    exact hh
  refine ⟨ψ,0,hs',(le_relativeMargin_iff hs').mpr ?_⟩
  intro x
  rw [he]
  simp [ψ,amplitude]

end HeadComplexity.MarginOneCollapse
