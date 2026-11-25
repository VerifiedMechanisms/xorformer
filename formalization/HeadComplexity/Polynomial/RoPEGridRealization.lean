import HeadComplexity.Polynomial.RoPEGridLimit
import HeadComplexity.Polynomial.RoPEGroupSymmetrization

set_option linter.style.header false

/-!
# Every centered grid point is a vector of group means
-/

namespace HeadComplexity.RoPEGridLimit

/-- Realize each prescribed group Hamming weight independently. -/
theorem exists_mean_eq_of_inCenteredGrid {G : Type*} {m : ℕ}
    (hm : 0 < m) (q : G → ℝ) (hq : InCenteredGrid m q) :
    ∃ x : G × Fin m → Bool, RoPEGroupSymmetrization.mean x = q := by
  classical
  choose k hk he using hq
  choose x hx using fun g ↦ exists_hammingWeight_eq (hk g)
  refine ⟨fun p ↦ x p.1 p.2, ?_⟩
  funext g
  have hw := RoPEGroupSymmetrization.mean_to_weight hm (fun p ↦ x p.1 p.2) g
  change (m : ℝ) / 2 * (RoPEGroupSymmetrization.mean (fun p ↦ x p.1 p.2) g + 1) =
    (hammingWeight (x g) : ℝ) at hw
  rw [hx g] at hw
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hq' : (m : ℝ) / 2 * (q g + 1) = k g := by
    rw [he g]
    field_simp
    ring
  nlinarith

end HeadComplexity.RoPEGridLimit
