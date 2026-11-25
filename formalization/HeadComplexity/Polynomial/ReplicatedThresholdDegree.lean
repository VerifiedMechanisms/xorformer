import HeadComplexity.Polynomial.RoPEGridRealization
import HeadComplexity.Polynomial.BoundedCoefficientLimit
import HeadComplexity.Foundation.FiniteSignMargin

set_option linter.style.header false

/-!
# Threshold-degree obstructions on sufficiently fine replicated grids

The arbitrary-degree analytic part of the general-head separation: absence
of a nonzero weak polynomial sign representative on the continuous cube
forces sufficiently fine replicated Boolean classifiers to have larger
threshold degree. No tensor or architecture assumption enters this result.
-/

namespace HeadComplexity.ReplicatedThresholdDegree

open MvPolynomial RoPEGridLimit RoPEGroupSymmetrization
open scoped Topology
open Filter

def GridRepresentative {n : ℕ} (S : (Fin n → ℝ) → ℝ) (d m : ℕ) : Prop :=
  ∃ Q : MvPolynomial (Fin n) ℝ, Q ≠ 0 ∧ Q.totalDegree ≤ d ∧
    ∀ q, InCenteredGrid m q → (0 < eval q Q ↔ 0 < S q)

/-- Compact coefficients turn fine-grid representatives into weak cube signs. -/
theorem weak_representative_of_grid_sequence {n d : ℕ}
    (S : (Fin n → ℝ) → ℝ) (hS : Continuous S)
    (m : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hm : Tendsto m atTop atTop)
    (hw : ∀ k, GridRepresentative S d (m k)) :
    ∃ Q : MvPolynomial (Fin n) ℝ, Q ≠ 0 ∧ Q.totalDegree ≤ d ∧
      ∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
        (0 < S q → 0 ≤ eval q Q) ∧ (S q < 0 → eval q Q ≤ 0) := by
  classical
  choose P hPne hPdeg hPsign using hw
  obtain ⟨t, Q, φ, ht, hQne, hQdeg, hφ, hcoeff⟩ :=
    BoundedCoefficientLimit.normalized_polynomial_subsequence P hPdeg hPne
  let R : ℕ → MvPolynomial (Fin n) ℝ := fun k ↦ C (t (φ k)) * P (φ k)
  have hRdeg (k : ℕ) : (R k).totalDegree ≤ d := by
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using hPdeg (φ k))
  refine ⟨Q, hQne, hQdeg, fun q hq ↦ ?_⟩
  apply weak_sign_of_grid_limit S (fun q ↦ eval q Q)
    (fun k q ↦ eval q (R k)) (m ∘ φ) (fun k ↦ hmpos (φ k))
    (hm.comp hφ.tendsto_atTop) hS ?_ ?_ q hq
  · intro k z hz
    change 0 < eval z (C (t (φ k)) * P (φ k)) ↔ 0 < S z
    rw [map_mul, eval_C, mul_pos_iff_of_pos_left (ht (φ k))]
    exact hPsign (φ k) z hz
  · intro y z hz
    exact BoundedCoefficientLimit.tendsto_eval_of_bounded_coefficients
      R Q hRdeg hQdeg hcoeff z y hz

/-- A weak cube-sign obstruction eventually excludes exact grid signs. -/
theorem eventually_no_grid_representative {n d : ℕ}
    (S : (Fin n → ℝ) → ℝ) (hS : Continuous S)
    (hno : ∀ Q : MvPolynomial (Fin n) ℝ, Q ≠ 0 → Q.totalDegree ≤ d →
      ¬ (∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
        (0 < S q → 0 ≤ eval q Q) ∧ (S q < 0 → eval q Q ≤ 0))) :
    ∀ᶠ m in atTop, ¬ GridRepresentative S d m := by
  classical
  by_contra hn
  have hf : ∃ᶠ m in atTop, GridRepresentative S d m := hn
  have hex : ∀ k : ℕ, ∃ m, k + 1 ≤ m ∧ GridRepresentative S d m :=
    fun k ↦ frequently_atTop.mp hf (k + 1)
  choose m hlarge hw using hex
  have hmpos (k : ℕ) : 0 < m k := by have := hlarge k; omega
  have hm : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun k hk ↦ by have := hlarge k; omega⟩
  obtain ⟨Q, hQne, hQdeg, hweak⟩ := weak_representative_of_grid_sequence S hS m hmpos hm hw
  exact hno Q hQne hQdeg hweak

/-- Centering and strictification preserve a Boolean polynomial degree bound. -/
theorem strict_centered_polynomial {σ : Type*} {n d : ℕ}
    (e : σ ≃ Fin n) (f : (Fin n → Bool) → Bool) (hf : ThresholdDegLE f d) :
    ∃ P : MvPolynomial σ ℝ, P.totalDegree ≤ d ∧
      ∀ x : σ → Bool,
        (0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) P ↔ f (x ∘ e.symm) = true) ∧
        eval (fun i ↦ 2 * boolToReal (x i) - 1) P ≠ 0 := by
  classical
  letI := Fintype.ofEquiv (Fin n) e.symm
  obtain ⟨P, hPdeg, hPsign⟩ := hf
  obtain ⟨δ, hδ, hshift⟩ := exists_strict_shift
    (fun x : σ → Bool ↦ eval (cubePoint (x ∘ e.symm)) P)
  let V : σ → MvPolynomial σ ℝ := fun i ↦ C (1 / 2 : ℝ) * (X i + 1)
  let Q := aeval V (rename e.symm P) - C δ
  have hV (i : σ) : (V i).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using
        (totalDegree_add (X i : MvPolynomial σ ℝ) 1).trans (by simp))
  have hQdeg : Q.totalDegree ≤ d := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (affine_substitution_degree _ _ hV).trans ((totalDegree_rename_le _ _).trans hPdeg)
    · simpa only [totalDegree_C] using Nat.zero_le d
  have heval (x : σ → Bool) :
      eval (fun i ↦ 2 * boolToReal (x i) - 1) Q =
        eval (cubePoint (x ∘ e.symm)) P - δ := by
    simp only [Q, map_sub, eval_C, eval_affine_substitution, eval_rename]
    congr 1
    apply congrArg (fun z : Fin n → ℝ ↦ eval z P)
    funext i
    simp only [V, map_mul, map_add, eval_C, eval_X, map_one, cubePoint,
      Function.comp_apply]
    ring
  refine ⟨Q, hQdeg, fun x ↦ ?_⟩
  rw [heval]
  exact ⟨(hshift x).1.trans (hPsign (x ∘ e.symm)), (hshift x).2⟩

noncomputable def classifier {n : ℕ} (S : (Fin n → ℝ) → ℝ) (m : ℕ)
    (x : Fin (n * m) → Bool) : Bool :=
  decide (0 < S (mean (fun p : Fin n × Fin m ↦ x (finProdFinEquiv p))))

/-- A Boolean threshold polynomial supplies a nonzero group-grid polynomial. -/
theorem grid_representative_of_threshold {n d m : ℕ} (hm : 0 < m)
    (S : (Fin n → ℝ) → ℝ) (hf : ThresholdDegLE (classifier S m) d) :
    GridRepresentative S d m := by
  classical
  obtain ⟨P, hPdeg, hPclass⟩ := strict_centered_polynomial
    (finProdFinEquiv (m := n) (n := m)) (classifier S m) hf
  let F : (Fin n → ℝ) → Bool := fun q ↦ decide (0 < S q)
  have hclass (x : Fin n × Fin m → Bool) :
      (0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) P ↔ F (mean x) = true) ∧
        eval (fun i ↦ 2 * boolToReal (x i) - 1) P ≠ 0 := by
    simpa only [classifier, Function.comp_apply, Equiv.symm_apply_apply] using hPclass x
  have hstrict (x : Fin n × Fin m → Bool) :
      (F (mean x) = true → 0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) P) ∧
      (F (mean x) = false → eval (fun i ↦ 2 * boolToReal (x i) - 1) P < 0) := by
    refine ⟨(hclass x).1.mpr, fun hx ↦ ?_⟩
    have hn : ¬ 0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) P := by
      intro hp
      have := (hclass x).1.mp hp
      simp only [hx, Bool.false_eq_true] at this
    exact lt_of_le_of_ne (le_of_not_gt hn) (hclass x).2
  let Q := averagedGroupPolynomial P
  have hQstrict (x : Fin n × Fin m → Bool) :=
    averagedGroupPolynomial_strict_sign hm P F hstrict x
  have hQne : Q ≠ 0 := by
    intro hz
    have he := averagedGroupPolynomial_group_cube hm P (fun _ ↦ false)
    change eval (fun g ↦ 2 * boolToReal false - 1) Q = _ at he
    rw [hz, map_zero, eval_rename] at he
    exact (hclass (fun _ ↦ false)).2 he.symm
  refine ⟨Q, hQne, (averagedGroupPolynomial_degree P).trans hPdeg, ?_⟩
  intro q hq
  obtain ⟨x, hx⟩ := exists_mean_eq_of_inCenteredGrid hm q hq
  have hs := hQstrict x
  rw [hx] at hs
  constructor
  · intro hp
    cases hF : F q with
    | false => exact False.elim ((not_lt_of_gt (hs.2 hF)) hp)
    | true => exact of_decide_eq_true hF
  · intro hp
    exact hs.1 (by exact decide_eq_true hp)

/-- A continuous weak-sign obstruction eventually forces larger Boolean
threshold degree at every sufficiently fine replication count. -/
theorem eventually_not_thresholdDegLE {n d : ℕ}
    (S : (Fin n → ℝ) → ℝ) (hS : Continuous S)
    (hno : ∀ Q : MvPolynomial (Fin n) ℝ, Q ≠ 0 → Q.totalDegree ≤ d →
      ¬ (∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
        (0 < S q → 0 ≤ eval q Q) ∧ (S q < 0 → eval q Q ≤ 0))) :
    ∀ᶠ m in atTop, ¬ ThresholdDegLE (classifier S m) d := by
  filter_upwards [eventually_no_grid_representative S hS hno,
    eventually_gt_atTop (0 : ℕ)] with m hno hm
  exact fun hf ↦ hno (grid_representative_of_threshold hm S hf)

end HeadComplexity.ReplicatedThresholdDegree
