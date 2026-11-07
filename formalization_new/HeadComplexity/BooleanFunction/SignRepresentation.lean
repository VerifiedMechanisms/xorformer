module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Data.Fintype.EquivFin

/-!
# Sign representations of Boolean functions

A score represents a Boolean function when its strictly positive set is the true set.
On a finite domain, a constant shift gives a representation whose score is nowhere zero.
-/

@[expose] public section

namespace Function

variable {α R : Type*}

/-- The positive set of the score agrees with the true set of the Boolean function. -/
def SignRepresents [Zero R] [LT R] (s : α → R) (f : α → Bool) : Prop :=
  ∀ x, 0 < s x ↔ f x = true

namespace SignRepresents

variable {s : α → ℝ} {f : α → Bool}

/-- A score that represents a Boolean function is positive at precisely its true inputs. -/
theorem pos_iff (h : SignRepresents s f) (x : α) : 0 < s x ↔ f x = true :=
  h x

/-- A score that represents a Boolean function is nonpositive at precisely its false inputs. -/
theorem nonpos_iff (h : SignRepresents s f) (x : α) : s x ≤ 0 ↔ f x = false := by
  simpa using not_congr (h x)

/-- Multiplying a sign-representing score by a positive factor at each input preserves the
Boolean function it represents. -/
theorem mul_pos_right (h : SignRepresents s f) {t : α → ℝ} (ht : ∀ x, 0 < t x) :
    SignRepresents (fun x ↦ s x * t x) f :=
  fun x ↦ (mul_pos_iff_of_pos_right (ht x)).trans (h x)

/-- On a finite domain, a sufficiently small positive downward shift makes the score strictly
negative on false inputs and keeps it positive on true inputs. -/
theorem exists_pos_sub_strict [Finite α] (h : SignRepresents s f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, if f x then 0 < s x - ε else s x - ε < 0 := by
  obtain ⟨ε, hε, hlt⟩ := Pi.exists_forall_pos_add_lt
    (fun x : {x // f x = true} ↦ (h x).2 x.property)
  refine ⟨ε, hε, fun x ↦ ?_⟩
  cases hx : f x
  · simpa only [hx, Bool.false_eq_true, ↓reduceIte, sub_neg] using
      (h.nonpos_iff x).2 hx |>.trans_lt hε
  · simpa only [hx, ↓reduceIte, sub_pos, zero_add] using hlt ⟨x, hx⟩

/-- The sign of the mixed difference on a checkerboard square is determined by its label. -/
theorem checkerboard (s : Bool → Bool → ℝ) (b : Bool)
    (h : ∀ i j, 0 < s i j ↔ xor i j = b) :
    0 < (if b then -1 else 1) * (s false false + s true true - s false true - s true false) := by
  rw [← sub_add_eq_sub_sub]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, sub_pos]
    exact (add_nonpos (by simpa [xor] using not_congr (h false true))
      (by simpa [xor] using not_congr (h true false))).trans_lt
      (add_pos ((h false false).mpr rfl) ((h true true).mpr rfl))
  · simp only [↓reduceIte, neg_one_mul, neg_pos, sub_neg]
    exact (add_nonpos (by simpa [xor] using not_congr (h false false))
      (by simpa [xor] using not_congr (h true true))).trans_lt
      (add_pos ((h false true).mpr rfl) ((h true false).mpr rfl))

end SignRepresents
end Function
