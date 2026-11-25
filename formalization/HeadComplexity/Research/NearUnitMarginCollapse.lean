import HeadComplexity.Research.RelativeMarginQuantifiers

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.NearUnitMarginCollapse
open Finset RelativeMarginQuantifiers
open scoped BigOperators

theorem norm_le_total_deficit {X : Type*} [Fintype X]
    (a : X → ℝ) (M : ℝ) (hbound : ∀ x, a x ≤ M) (hbad : ∃ x, a x ≤ 0) :
    M ≤ ∑ x, (M - a x) := by
  classical
  obtain ⟨x,hx⟩ := hbad
  calc
    M ≤ M-a x := by linarith
    _ ≤ ∑ y, (M-a y) := single_le_sum (fun y _ => sub_nonneg.mpr (hbound y)) (mem_univ x)

/-- A quantitative near-equality statement for the requested whole-cube
amplitude: sufficiently near margin one, some existing head classifies every
input correctly by itself. It need not retain the source margin. -/
theorem exists_strict_head_of_near_unit_margin {n H : ℕ}
    {f : (Fin n → Bool) → Bool} {φ : Fin H → FracAtom n} {b γ : ℝ}
    (hs : StrictlyRepresents f φ b) (hm : γ ≤ relativeMargin f φ b)
    (hfalse : ∃ x, f x = false) (htrue : ∃ x, f x = true)
    (hnear : (2 : ℝ)^n * (1-γ) < 1) :
    ∃ h, ∀ x, 0 < signedLabel f x * (φ h).eval x := by
  classical
  by_contra hnone
  push_neg at hnone
  have hbound (h : Fin H) (x : Fin n → Bool) :
      signedLabel f x * (φ h).eval x ≤ atomSup (φ h) := by
    calc
      _ ≤ |signedLabel f x * (φ h).eval x| := le_abs_self _
      _ = |(φ h).eval x| := by rw [abs_mul, abs_signedLabel, one_mul]
      _ ≤ _ := abs_eval_le_atomSup _ _
  have hhead (h : Fin H) : atomSup (φ h) ≤
      ∑ x, (atomSup (φ h) - signedLabel f x * (φ h).eval x) :=
    norm_le_total_deficit _ _ (hbound h) (hnone h)
  have hbbound (x : Fin n → Bool) : signedLabel f x * b ≤ |b| := by
    calc
      _ ≤ |signedLabel f x * b| := le_abs_self _
      _ = |b| := by rw [abs_mul, abs_signedLabel, one_mul]
  have hbbad : ∃ x, signedLabel f x * b ≤ 0 := by
    by_cases hb : 0 ≤ b
    · obtain ⟨x,hx⟩ := hfalse
      refine ⟨x,?_⟩
      rw [signedLabel_of_false hx]
      linarith
    · obtain ⟨x,hx⟩ := htrue
      refine ⟨x,?_⟩
      rw [signedLabel_of_true hx]
      linarith
  have hbdef := norm_le_total_deficit _ _ hbbound hbbad
  have hrow (x : Fin n → Bool) :
      amplitude φ b - signedLabel f x * score φ b x =
        (|b|-signedLabel f x*b) +
        ∑ h, (atomSup (φ h)-signedLabel f x*(φ h).eval x) := by
    simp [amplitude, score, mul_add, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  have hlo : amplitude φ b ≤
      ∑ x, (amplitude φ b - signedLabel f x * score φ b x) := by
    simp_rw [hrow]
    rw [sum_add_distrib, sum_comm]
    exact add_le_add hbdef (sum_le_sum fun h _ => hhead h)
  have hpoint := (le_relativeMargin_iff hs).mp hm
  have hhi : (∑ x, (amplitude φ b - signedLabel f x * score φ b x)) ≤
      (2 : ℝ)^n * (1-γ) * amplitude φ b := by
    calc
      _ ≤ ∑ _x : Fin n → Bool, ((1-γ)*amplitude φ b) :=
        sum_le_sum fun x _ => by nlinarith [hpoint x]
      _ = _ := by simp [Fintype.card_fun, mul_assoc]
  have hstrict := mul_lt_mul_of_pos_right hnear (amplitude_pos_of_strict hs)
  linarith

/-- The near-unit statement concludes unrestricted original width one. -/
theorem computable_one_head_of_near_unit_margin {n H : ℕ}
    {f : (Fin n → Bool) → Bool} {γ : ℝ}
    (hf : HasRelativeMargin n H f γ)
    (hfalse : ∃ x, f x = false) (htrue : ∃ x, f x = true)
    (hnear : (2 : ℝ)^n * (1-γ) < 1) : computableWithHeadsN n 1 f := by
  obtain ⟨φ,b,hs,hm⟩ := hf
  obtain ⟨h,hh⟩ := exists_strict_head_of_near_unit_margin hs hm hfalse htrue hnear
  have hstrict : StrictlyRepresents f (fun _ : Fin 1 => φ h) 0 := by
    intro x
    simpa [score] using hh x
  exact computable_of_hasRelativeMargin
    ⟨(fun _ : Fin 1 => φ h),0,hstrict,(relativeMargin_pos hstrict).le⟩

end HeadComplexity.NearUnitMarginCollapse
