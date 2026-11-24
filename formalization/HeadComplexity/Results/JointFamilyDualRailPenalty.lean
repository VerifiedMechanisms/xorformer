import HeadComplexity.Results.DualRailLift

set_option linter.style.header false

/-!
# An affine penalty cannot select a complementary-rail cube

The exact dual-rail lifting theorem remains valid. The obstruction here
concerns the separate global gluing step: an everywhere-nonnegative affine
penalty vanishing on a complementary-rail cube vanishes on the entire cube.
No assertion is made about nonlinear selectors or rational cancellations.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

theorem jointFamily_affine_antipode_sum {n : ℕ} (c : ℝ) (b : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue c b x + affineValue c b (fun i ↦ !(x i)) =
      2 * c + ∑ i, b i := by
  have hbit (i : Fin n) : b i * boolToReal (x i) +
      b i * boolToReal (!(x i)) = b i := by
    cases x i <;> simp [boolToReal]
  unfold affineValue
  calc
    _ = 2 * c + ∑ i, (b i * boolToReal (x i) +
        b i * boolToReal (!(x i))) := by rw [Finset.sum_add_distrib]; ring
    _ = _ := by simp_rw [hbit]

/-- Two antipodal zeros force every nonnegative affine value to vanish. -/
theorem jointFamily_nonnegative_affine_antipodal_zeros {n : ℕ}
    (c : ℝ) (b : Fin n → ℝ) (x : Fin n → Bool)
    (hnonneg : ∀ y, 0 ≤ affineValue c b y)
    (hx : affineValue c b x = 0)
    (hxc : affineValue c b (fun i ↦ !(x i)) = 0) :
    ∀ y, affineValue c b y = 0 := by
  have hconstant : 2 * c + ∑ i, b i = 0 := by
    rw [← jointFamily_affine_antipode_sum c b x, hx, hxc, add_zero]
  intro y
  have hsum := jointFamily_affine_antipode_sum c b y
  rw [hconstant] at hsum
  have hy := hnonneg y
  have hyc := hnonneg (fun i ↦ !(y i))
  linarith

/-- The two-rail parallelogram obstruction, stated without coordinates. -/
theorem jointFamily_nonnegative_affine_pair_obstruction (c u v : ℝ)
    (h00 : 0 ≤ c) (h11 : 0 ≤ c + u + v)
    (h01 : c + v = 0) (h10 : c + u = 0) :
    c = 0 ∧ c + u + v = 0 := by constructor <;> linarith

/-- Vanishing on all complementary-rail inputs cannot define an affine
suppression penalty for their complement. -/
theorem jointFamily_dualRail_affine_penalty_zero {n : ℕ}
    (c : ℝ) (b : Fin (n + n) → ℝ)
    (hnonneg : ∀ y, 0 ≤ affineValue c b y)
    (hzero : ∀ x : Fin n → Bool, affineValue c b (dualRailBits x) = 0) :
    ∀ y, affineValue c b y = 0 := by
  let x : Fin n → Bool := fun _ ↦ false
  apply jointFamily_nonnegative_affine_antipodal_zeros c b (dualRailBits x) hnonneg
    (hzero x)
  have heq : (fun i ↦ !(dualRailBits x i)) = dualRailBits (fun i ↦ !(x i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [dualRailBits, Fin.addCases_left, Fin.addCases_right]
  rw [heq]
  exact hzero _

end HeadComplexity.AxisZeroGluing
