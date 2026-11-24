import HeadComplexity.Polynomial.ThreeHeadMeanSign

set_option linter.style.header false

/-! # Arbitrary threshold polynomials induce mean-grid polynomials of the same degree -/

namespace HeadComplexity.ReplicatedThresholdMean

noncomputable section

open MvPolynomial PureRoPEReplication PureRoPEReplicationStrict
open PureCubicRawKernel MeanGridCubic MeanGridSymmetrization ThreeHeadMeanSign
open ReplicatedMeanGrid MeanGridSignProbe
open scoped BigOperators

theorem substitution_degree_le {α β : Type*}
    (v : α → MvPolynomial β ℝ) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (P : MvPolynomial α ℝ) : (aeval v P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  have hm : (aeval v (monomial d (P.coeff d))).totalDegree ≤ d.sum (fun _ e ↦ e) := by
    simp only [aeval_monomial, algebraMap_eq, Finsupp.prod]
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow _ _).trans
      (by simpa using Nat.mul_le_mul_left (d i) (hv i))
  exact hm.trans (le_totalDegree hd)

def spinPolynomial {n m : ℕ} (P : MvPolynomial (Fin (n * m)) ℝ) :
    MvPolynomial (Fin n × Fin m) ℝ :=
  aeval (fun i ↦ C (1 / 2 : ℝ) * (1 + X ((finProdFinEquiv (m := n) (n := m)).symm i))) P

theorem spinPolynomial_degree {n m : ℕ} (P : MvPolynomial (Fin (n * m)) ℝ) :
    (spinPolynomial P).totalDegree ≤ P.totalDegree := by
  apply substitution_degree_le
  intro i
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_add _ _).trans (by simp)

theorem spinPolynomial_eval {n m : ℕ} (P : MvPolynomial (Fin (n * m)) ℝ)
    (x : Fin (n * m) → Bool) :
    eval (fun p : Fin n × Fin m ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p)))
      (spinPolynomial P) = eval (fun i ↦ boolToReal (x i)) P := by
  change aeval _ (aeval _ P) = aeval (fun i ↦ boolToReal (x i)) P
  rw [comp_aeval_apply]
  congr 2
  funext i
  simp only [map_mul, aeval_C, map_add, map_one, aeval_X,
    Equiv.apply_symm_apply]
  cases hx : x i <;> norm_num [PureRoPECenteredConstruction.spin, boolToReal, hx]

def meanThreshold {n m : ℕ} (P : MvPolynomial (Fin (n * m)) ℝ) :
    MvPolynomial (Fin n) ℝ := meanPolynomial (spinPolynomial P)

theorem meanThreshold_degree {n m : ℕ} (P : MvPolynomial (Fin (n * m)) ℝ) :
    (meanThreshold P).totalDegree ≤ P.totalDegree :=
  (meanPolynomial_degree _).trans (spinPolynomial_degree P)

theorem meanThreshold_sign {m : ℕ} (hm : 2 < m)
    (P : MvPolynomial (Fin (14 * m)) ℝ) (hPdeg : P.totalDegree ≤ 3)
    (hP : SignRepresents P unshiftedFunction) (x : Fin (14 * m) → Bool) :
    0 < eval (means x) (meanThreshold P) ↔ unshiftedFunction x = true := by
  let z : Fin 14 × Fin m → ℝ :=
    fun p ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p))
  have hz (p) : z p ^ 2 = 1 := by
    dsimp [z, PureRoPECenteredConstruction.spin]
    split_ifs <;> norm_num
  have hmean : (fun i ↦ (∑ r, z (i, r)) / m) = means x := rfl
  rw [meanThreshold, ← hmean,
    ← average_polynomial_eq hm (spinPolynomial P) ((spinPolynomial_degree P).trans hPdeg) z hz]
  apply average_sign
  intro σ
  have he : (fun p : Fin 14 × Fin m ↦ z (p.1, σ p.1 p.2)) =
      fun p ↦ PureRoPECenteredConstruction.spin (permuteInput x σ (finProdFinEquiv p)) := by
    funext p
    simp [z, permuteInput]
  rw [he, spinPolynomial_eval]
  exact (hP (permuteInput x σ)).trans (by rw [unshifted_permuteInput])

/-- No symmetry of the original threshold polynomial is assumed. -/
theorem threshold_two_mean {m : ℕ} (hm : 2 < m)
    (h : ThresholdDegLE (unshiftedFunction (m := m)) 2) :
    ∃ Q : MvPolynomial (Fin 14) ℝ, Q.totalDegree ≤ 2 ∧ Q ≠ 0 ∧
      ∀ k : Fin 14 → Fin (m + 1),
        (0 < eval (fun i ↦ gridValue m (k i)) rawTarget ↔
          0 < eval (fun i ↦ gridValue m (k i)) Q) := by
  obtain ⟨P, hdeg, hP⟩ := h
  have hsign := meanThreshold_sign hm P (hdeg.trans (by decide)) hP
  refine ⟨meanThreshold P, (meanThreshold_degree P).trans hdeg, ?_,
    rawTarget_classifier_grid (by omega) (meanThreshold P) hsign⟩
  intro hz
  have hp := (hsign (fun _ ↦ true)).mpr (unshifted_all_true (by omega))
  rw [hz, map_zero] at hp
  exact (lt_irrefl 0) hp

end
end HeadComplexity.ReplicatedThresholdMean
