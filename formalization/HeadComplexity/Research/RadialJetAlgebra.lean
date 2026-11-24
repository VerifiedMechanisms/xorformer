import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-!
Exact finite algebra for bounded moving-numerator radial paths.
These are auxiliary identities, not an unrestricted head-complexity theorem.
-/
namespace HeadComplexity.RadialJetAlgebra

variable {R : Type*} [CommRing R]

def numerator (a : ℕ → R) (t : R) (r : ℕ) : R :=
  ∑ j ∈ Finset.range (r + 1), a j * t^j

def moment (a : ℕ → R) (B C : R) (r : ℕ) : R :=
  ∑ j ∈ Finset.range (r + 1), a j * B^j * (-C)^(r-j)

/-- Horner form of the finite low-order part. -/
def lowPart (a : ℕ → R) (B C t : R) : ℕ → R
  | 0 => 0
  | r+1 => B * lowPart a B C t r + t^r * moment a B C r

theorem numerator_succ (a : ℕ → R) (t : R) (r : ℕ) :
    numerator a t (r+1) = numerator a t r + a (r+1)*t^(r+1) := by
  exact Finset.sum_range_succ _ (r+1)

theorem moment_zero (a : ℕ → R) (B C : R) : moment a B C 0 = a 0 := by
  simp [moment]

theorem moment_succ (a : ℕ → R) (B C : R) (r : ℕ) :
    moment a B C (r+1) = -C * moment a B C r + a (r+1)*B^(r+1) := by
  unfold moment
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [show r+1-j = (r-j)+1 by omega, pow_succ]
  ring

/-- The entire remainder is one fixed moment weight divided by the original
linear denominator. No convergence or bounded cancellation order is used. -/
theorem tail_identity (a : ℕ → R) (B C t : R) (r : ℕ) :
    B^r * numerator a t r =
      (B+t*C) * lowPart a B C t r + t^r * moment a B C r := by
  induction r with
  | zero => simp [numerator, lowPart, moment]
  | succ r ih =>
      rw [numerator_succ, moment_succ]
      simp only [lowPart, pow_succ]
      calc
        B^r * B * (numerator a t r + a (r+1)*(t^r*t)) =
          B * (B^r * numerator a t r) + B^r * B * a (r+1) * (t^r*t) := by ring
        _ = B * ((B+t*C)*lowPart a B C t r + t^r*moment a B C r) +
            B^r*B*a (r+1)*(t^r*t) := by rw [ih]
        _ = _ := by ring

/-- Once the numerator coefficients stop, every later moment comes from the
same fixed tail weight. This is the algebra behind exponential transfer. -/
theorem moment_tail (a : ℕ → R) (B C : R) (r ℓ : ℕ)
    (ha : ∀ j, r < j → a j = 0) :
    moment a B C (r+ℓ) = moment a B C r * (-C)^ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [Nat.add_succ, moment_succ, ih, ha (r+ℓ+1) (by omega)]
      simp only [zero_mul, add_zero, pow_succ]
      ring

#print axioms tail_identity
#print axioms moment_tail
end HeadComplexity.RadialJetAlgebra
