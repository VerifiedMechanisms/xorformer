import HeadComplexity.Polynomial.ThreeHeadTripartiteCross
import HeadComplexity.Results.PureRoPETwoHeads

set_option linter.style.header false

/-!
# Exact cubic coefficients under coordinate replication

Summing the three distinct-group cubic coefficient indices is exactly the
same as summing the numerator and denominator slope vectors inside each group.
There is no finite-population correction on three distinct groups. The
uniform-sign denominator property survives every nonempty group sum.
-/

namespace HeadComplexity.ThreeHeadReplication

noncomputable section

open Finset ThreeHeadTripartiteCross
open scoped BigOperators

private theorem coefficient_swap_XY (c : ℝ) (AX AY AZ BX BY BZ : Fin 3 → ℝ) :
    coefficient c AX AY AZ BX BY BZ = coefficient c AY AX AZ BY BX BZ := by
  simp [coefficient, pairFactor, middleFactor, other₀, other₁, Fin.sum_univ_succ]
  ring

private theorem coefficient_swap_XZ (c : ℝ) (AX AY AZ BX BY BZ : Fin 3 → ℝ) :
    coefficient c AX AY AZ BX BY BZ = coefficient c AZ AY AX BZ BY BX := by
  simp [coefficient, pairFactor, middleFactor, other₀, other₁, Fin.sum_univ_succ]
  ring

theorem coefficient_sum_Y {m : ℕ} (c : ℝ) (AY BY : Fin m → Fin 3 → ℝ)
    (AX AZ BX BZ : Fin 3 → ℝ) :
    coefficient c AX (fun h ↦ ∑ i, AY i h) AZ BX (fun h ↦ ∑ i, BY i h) BZ =
      ∑ i, coefficient c AX (AY i) AZ BX (BY i) BZ := by
  rw [coefficient_swap_XY, coefficient_sum_X]
  apply Finset.sum_congr rfl
  intro i _
  exact coefficient_swap_XY _ _ _ _ _ _ _

theorem coefficient_sum_Z {m : ℕ} (c : ℝ) (AZ BZ : Fin m → Fin 3 → ℝ)
    (AX AY BX BY : Fin 3 → ℝ) :
    coefficient c AX AY (fun h ↦ ∑ i, AZ i h) BX BY (fun h ↦ ∑ i, BZ i h) =
      ∑ i, coefficient c AX AY (AZ i) BX BY (BZ i) := by
  rw [coefficient_swap_XZ, coefficient_sum_X]
  apply Finset.sum_congr rfl
  intro i _
  exact coefficient_swap_XZ _ _ _ _ _ _ _

theorem coefficient_sum_three_groups {a b d : ℕ} (c : ℝ)
    (AX BX : Fin a → Fin 3 → ℝ) (AY BY : Fin b → Fin 3 → ℝ)
    (AZ BZ : Fin d → Fin 3 → ℝ) :
    coefficient c (fun h ↦ ∑ i, AX i h) (fun h ↦ ∑ j, AY j h)
      (fun h ↦ ∑ k, AZ k h) (fun h ↦ ∑ i, BX i h)
      (fun h ↦ ∑ j, BY j h) (fun h ↦ ∑ k, BZ k h) =
        ∑ i, ∑ j, ∑ k, coefficient c (AX i) (AY j) (AZ k) (BX i) (BY j) (BZ k) := by
  rw [coefficient_sum_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_sum_Y]
  apply Finset.sum_congr rfl
  intro j _
  exact coefficient_sum_Z _ _ _ _ _ _ _

theorem uniform_group_sum {n m : ℕ} [NeZero m] (B : Fin n × Fin m → ℝ)
    (hB : (∀ p, 0 < B p) ∨ (∀ p, B p < 0) ∨ (∀ p, B p = 0)) :
    AffineFraction.UniformSign (fun i ↦ ∑ r, B (i, r)) := by
  rcases hB with hp | hn | hz
  · exact Or.inl (fun i ↦ Finset.sum_pos (fun r _ ↦ hp (i, r)) Finset.univ_nonempty)
  · exact Or.inr (Or.inl (fun i ↦
      Finset.sum_neg (fun r _ ↦ hn (i, r)) Finset.univ_nonempty))
  · exact Or.inr (Or.inr (fun i ↦ by simp [hz]))

/-- Once a three-head pure construction has an all-vanilla four-head lower
bound, its minimum pure head count is exactly three. -/
theorem exact_three_of_upper_and_vanilla_lower {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hupper : pureRoPEComputable n 3 f) (hlower : 4 ≤ HStar n f) :
    PureRoPEHStar n f = 3 := by
  classical
  have hle : PureRoPEHStar n f ≤ 3 := by
    unfold PureRoPEHStar
    exact Nat.find_min' _ hupper
  have hge : 3 ≤ PureRoPEHStar n f := by
    by_contra h
    have he := pureRoPEHStar_eq_vanilla_of_le_two f (by omega)
    omega
  omega

end

end HeadComplexity.ThreeHeadReplication
