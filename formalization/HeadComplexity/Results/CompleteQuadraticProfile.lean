import HeadComplexity.Results.SymmetricComplexity
import Mathlib.Tactic

set_option linter.style.header false

/-! The symmetric complete-quadratic sign profile has exactly half as many
heads as input bits in even dimension. Its exponential Fourier threshold
density is a separate written Fourier argument. -/
namespace HeadComplexity.CompleteQuadraticProfile

def profile (t : ℕ) : Bool := decide (t % 4 < 2)

theorem profile_change (t : ℕ) : profile t ≠ profile (t + 1) ↔ t % 2 = 1 := by
  simp only [profile, ne_eq, decide_eq_decide]
  omega

theorem signChanges_eq (m : ℕ) : signChanges (2 * m) profile = m := by
  have hfilter (n : ℕ) : (Finset.range n).filter (fun t ↦ profile t ≠ profile (t + 1)) =
      (Finset.range n).filter (fun t ↦ t % 2 = 1) := by
    ext t
    simp [profile_change]
  simp only [signChanges, hfilter]
  induction m with
  | zero => simp
  | succ m ih =>
    have hindex : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hindex, Finset.range_add_one, Finset.filter_insert]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
      Nat.one_mod, zero_add, ite_true]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.range_add_one, Finset.filter_insert]
      simpa using congrArg Nat.succ ih
    · simp only [Finset.mem_filter, Finset.mem_range, not_and]
      omega

theorem HStar_eq (m : ℕ) : HStar (2 * m) (symmetricFn profile) = m := by
  rw [HStar_symmetricFn_eq_signChanges (symmetricFn_computable profile (2 * m)), signChanges_eq]

end HeadComplexity.CompleteQuadraticProfile
