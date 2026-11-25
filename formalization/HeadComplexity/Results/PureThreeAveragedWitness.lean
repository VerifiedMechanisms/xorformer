import HeadComplexity.Results.PureThreeSeparationLimit
import HeadComplexity.Polynomial.VanillaThreeCentered
import HeadComplexity.Polynomial.RoPEAveragedTensor
import HeadComplexity.Polynomial.RoPEPhysicalTensor
import HeadComplexity.Polynomial.RoPEGridRealization

set_option linter.style.header false

/-!
# Every vanilla representation supplies an actual averaged witness

This module connects the unchanged vanilla architecture to the finite
polynomial, grid-sign, tensor-factor, and denominator-orientation data used
by the separation limit theorem.
-/

namespace HeadComplexity.PureThreeAveragedWitness

open scoped BigOperators
open MvPolynomial RoPECrossBlockCoefficients RoPEGroupSymmetrization
open RoPEMixedTensor RoPEThreeTensor RoPEAveragedTensor RoPEGridLimit
open VanillaThreeCentered PureThreeSeparationLimit

theorem mixedTensor_averaged_data {m : ℕ} (hm : 0 < m)
    (a : VanillaThreeCentered.Data (Fin 18 × Fin m)) :
    mixedTensor (averagedGroupPolynomial a.polynomial) =
      factorTensor
        (aggregateRows a.denominatorSlope 0) (aggregateRows a.numeratorSlope 0)
        (aggregateRows a.denominatorSlope 1) (aggregateRows a.numeratorSlope 1)
        (aggregateRows a.denominatorSlope 2) (aggregateRows a.numeratorSlope 2) := by
  rw [mixedTensor_averagedGroupPolynomial hm _ a.totalDegree_le]
  simp only [VanillaThreeCentered.Data.polynomial, map_add, map_mul, rename_group_affine]
  exact RoPEPhysicalTensor.mixedTensor_three_affine
    a.numeratorConstant a.denominatorConstant
    (fun h g ↦ ∑ r, a.numeratorSlope h (g, r))
    (fun h g ↦ ∑ r, a.denominatorSlope h (g, r))

theorem grid_abs_le_one {G : Type*} {m : ℕ} (hm : 0 < m) (q : G → ℝ)
    (hq : InCenteredGrid m q) : ∀ g, |q g| ≤ 1 := by
  intro g
  obtain ⟨k, hk, he⟩ := hq g
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
  have hdiv : (k : ℝ) / m ≤ 1 := (div_le_one hm').mpr hk'
  have hdiv0 : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hm'.le
  rw [he, mul_div_assoc, abs_le]
  constructor <;> linarith

theorem coordinate_reindex {m : ℕ} (x : Fin 18 × Fin m → Bool) :
    PureThreeReplicatedGrid.coordinate
      (fun i ↦ x ((finProdFinEquiv (m := 18) (n := m)).symm i)) = mean x := by
  funext g
  simp only [PureThreeReplicatedGrid.coordinate, mean, Equiv.symm_apply_apply]

/-- All components of the averaged witness come from the actual vanilla
architecture. There is no assumed tensor factorization or sign-transfer step. -/
theorem averagedWitness_of_vanilla (m : ℕ) (hm : 0 < m)
    (hf : computableWithSharedHeadsN (18 * m) 3 (PureThreeReplicatedGrid.classifier m)) :
    Nonempty (AveragedWitness RoPEPhysicalCoordinates.physical m) := by
  classical
  obtain ⟨a, horient, hclass⟩ := exists_data_of_vanilla
    (finProdFinEquiv (m := 18) (n := m)) (PureThreeReplicatedGrid.classifier m) hf
  let Q := averagedGroupPolynomial a.polynomial
  let F : (Fin 18 → ℝ) → Bool := fun q ↦ decide (0 < PureThreeReplicatedGrid.score q)
  have hclass' (x : Fin 18 × Fin m → Bool) :
      (0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ↔ F (mean x) = true) ∧
      eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ≠ 0 := by
    simpa only [PureThreeReplicatedGrid.classifier, coordinate_reindex] using hclass x
  have hstrict (x : Fin 18 × Fin m → Bool) :
      (F (mean x) = true → 0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial) ∧
      (F (mean x) = false → eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial < 0) := by
    refine ⟨(hclass' x).1.mpr, fun hx ↦ ?_⟩
    have hn : ¬ 0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial := by
      intro hp
      have := (hclass' x).1.mp hp
      simp only [hx, Bool.false_eq_true] at this
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
    · exact hlt
    · exact ((hclass' x).2 heq).elim
  have hQstrict (x : Fin 18 × Fin m → Bool) :=
    averagedGroupPolynomial_strict_sign hm a.polynomial F hstrict x
  have hQne : Q ≠ 0 := by
    intro hz
    have he := averagedGroupPolynomial_group_cube hm a.polynomial (fun _ ↦ false)
    change eval (fun g ↦ 2 * boolToReal false - 1) Q = _ at he
    rw [hz, map_zero, eval_rename] at he
    apply (hclass (fun _ ↦ false)).2
    exact he.symm
  refine ⟨{
    polynomial := Q
    degree_le := (averagedGroupPolynomial_degree a.polynomial).trans a.totalDegree_le
    nonzero := hQne
    grid_sign := ?_
    D₁ := aggregateRows a.denominatorSlope 0
    N₁ := aggregateRows a.numeratorSlope 0
    D₂ := aggregateRows a.denominatorSlope 1
    N₂ := aggregateRows a.numeratorSlope 1
    D₃ := aggregateRows a.denominatorSlope 2
    N₃ := aggregateRows a.numeratorSlope 2
    factorization := mixedTensor_averaged_data hm a
    oriented := ?_ }⟩
  · intro q hq
    obtain ⟨x, hx⟩ := exists_mean_eq_of_inCenteredGrid hm q hq
    have hs := hQstrict x
    rw [hx] at hs
    have he : (0 < eval q Q) ↔ 0 < PureThreeReplicatedGrid.score q := by
      constructor
      · intro hp
        cases hF : F q with
        | false => exact False.elim ((not_lt_of_gt (hs.2 hF)) hp)
        | true => exact of_decide_eq_true hF
      · intro hp
        exact hs.1 (by exact decide_eq_true hp)
    rw [he, RoPEPhysicalCoordinates.eval_physical]
    exact (PureThreeReplicatedGrid.clearedScore_pos_iff q (grid_abs_le_one hm q hq)).symm
  · intro hT
    rw [mixedTensor_averaged_data hm a] at hT
    exact exists_oriented_aggregate_row hm a.denominatorSlope a.numeratorSlope horient hT

end HeadComplexity.PureThreeAveragedWitness
