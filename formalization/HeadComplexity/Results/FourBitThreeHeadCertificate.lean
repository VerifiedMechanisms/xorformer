import HeadComplexity.Results.RoPESmallInputs
import Std.Tactic.BVDecide

set_option linter.style.header false

/-!
# Strict sign templates for finite-dimensional score spaces

An exact integer certificate consists of a base vector and one correction vector
per input. At unrestricted inputs the corrections form a positive diagonal
matrix. At the remaining inputs the base dominates the sum of correction
magnitudes. The resulting score realizes every compatible Boolean labeling.
-/

namespace HeadComplexity

open scoped BigOperators

namespace SignTemplate

variable {m d : ℕ}

/-- Integer evaluation in a finite feature space. -/
def eval (T : Fin m → Fin d → ℤ) (a : Fin d → ℤ) (v : Fin m) : ℤ :=
  ∑ k, T v k * a k

/-- A finite exact certificate for an open cylinder of sign assignments. -/
structure Certificate (m d : ℕ) where
  base : Fin d → ℤ
  adjust : Fin m → Fin d → ℤ
  scale : ℤ
  support : Fin m → Bool
  positive : Fin m → Bool

/-- Every certificate condition is integer arithmetic. -/
def Valid (T : Fin m → Fin d → ℤ) (c : Certificate m d) : Prop :=
  0 < c.scale ∧ ∀ v,
    if c.support v then
      if c.positive v then
        (∑ j, |eval T (c.adjust j) v|) < eval T c.base v
      else
        eval T c.base v < -(∑ j, |eval T (c.adjust j) v|)
    else
      eval T c.base v = 0 ∧
        ∀ j, eval T (c.adjust j) v = if j = v then c.scale else 0

instance (T : Fin m → Fin d → ℤ) (c : Certificate m d) :
    Decidable (Valid T c) := inferInstanceAs (Decidable (_ ∧ ∀ _, _))

/-- The sign convention used by a template is strict on both labels. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

/-- The open sign cylinder encoded by the fixed support. -/
def Matches (c : Certificate m d) (y : Fin m → Bool) : Prop :=
  ∀ v, c.support v = true → y v = c.positive v

/-- A valid template constructs an integer feature coefficient vector with the
required strict signs. No linear programming or approximation oracle is used. -/
theorem exists_strict_score (T : Fin m → Fin d → ℤ) (c : Certificate m d)
    (hc : Valid T c) (y : Fin m → Bool) (hy : Matches c y) :
    ∃ a : Fin d → ℤ, ∀ v, if y v then 0 < eval T a v else eval T a v < 0 := by
  let a : Fin d → ℤ := fun k => c.base k + ∑ j, sign (y j) * c.adjust j k
  have heval (v : Fin m) : eval T a v =
      eval T c.base v + ∑ j, sign (y j) * eval T (c.adjust j) v := by
    simp only [eval, a, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨a, fun v => ?_⟩
  rw [heval]
  have hbound : |∑ j, sign (y j) * eval T (c.adjust j) v| ≤
      ∑ j, |eval T (c.adjust j) v| := by
    calc
      _ ≤ ∑ j, |sign (y j) * eval T (c.adjust j) v| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_sign, one_mul]
  have hscale := hc.1
  have hv := hc.2 v
  cases hs : c.support v with
  | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at hv
      rw [hv.1]
      simp only [hv.2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_add]
      cases y v <;> simp only [sign, Bool.false_eq_true, ↓reduceIte,
        neg_one_mul, one_mul] <;> omega
  | true =>
      have hy' := hy v hs
      simp only [hs, ↓reduceIte] at hv
      rw [hy']
      cases hp : c.positive v <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hv ⊢
      · have := (abs_le.mp hbound).2
        omega
      · have := (abs_le.mp hbound).1
        omega

/-- A template may be used with either global orientation. -/
theorem exists_strict_score_or_neg (T : Fin m → Fin d → ℤ) (c : Certificate m d)
    (hc : Valid T c) (y : Fin m → Bool)
    (hy : Matches c y ∨ Matches c (fun v => !(y v))) :
    ∃ a : Fin d → ℤ, ∀ v, if y v then 0 < eval T a v else eval T a v < 0 := by
  rcases hy with hy | hy
  · exact exists_strict_score T c hc y hy
  · obtain ⟨a, ha⟩ := exists_strict_score T c hc (fun v => !(y v)) hy
    refine ⟨fun k => -a k, fun v => ?_⟩
    have he : eval T (fun k => -a k) v = -eval T a v := by
      simp only [eval, mul_neg, Finset.sum_neg_distrib]
    rw [he]
    have hv := ha v
    cases hyv : y v <;> simp [hyv] at hv ⊢ <;> omega

end SignTemplate
end HeadComplexity
