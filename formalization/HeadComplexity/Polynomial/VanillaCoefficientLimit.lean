import HeadComplexity.Polynomial.VanillaGeneralCentered
import HeadComplexity.Polynomial.ReplicatedThresholdDegree

set_option linter.style.header false

/-!
# Actual vanilla classifiers converge to oriented factor coefficients

The only algebraic premise of the final exclusion theorem is an explicit
obstruction to limits of oriented affine-factor coefficients. All Boolean
strictification, averaging, normalization, dense-grid signs, and subsequence
steps are proved here from actual vanilla computability.
-/

namespace HeadComplexity.VanillaCoefficientLimit

open MvPolynomial VanillaGeneralCentered RoPEGroupSymmetrization RoPEGridLimit
open scoped BigOperators Topology
open Filter

noncomputable def scaleNumerators {H : ℕ} {σ : Type*} (t : ℝ) (a : Data H σ) : Data H σ where
  denominatorConstant := a.denominatorConstant
  denominatorSlope := a.denominatorSlope
  numeratorConstant := fun h ↦ t * a.numeratorConstant h
  numeratorSlope := fun h i ↦ t * a.numeratorSlope h i

theorem affine_scale {σ : Type*} [Fintype σ] (t c : ℝ) (v : σ → ℝ) :
    RoPECrossBlockCoefficients.affine (t * c) (fun i ↦ t * v i) =
      C t * RoPECrossBlockCoefficients.affine c v := by
  classical
  simp only [RoPECrossBlockCoefficients.affine, map_mul, mul_add, Finset.mul_sum, mul_assoc]

theorem scaleNumerators_polynomial {H : ℕ} {σ : Type*} [Fintype σ]
    (t : ℝ) (a : Data H σ) : (scaleNumerators t a).polynomial = C t * a.polynomial := by
  classical
  simp only [Data.polynomial, scaleNumerators, affine_scale, Finset.mul_sum, mul_assoc]

/-- Top squarefree coefficients are precisely the data surviving centered
Boolean averaging at the head-count degree. -/
def TopCoefficientLimit {H n : ℕ} (a : ℕ → Data H (Fin n))
    (Q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ e : Fin n →₀ ℕ, (∀ i, e i ≤ 1) → e.sum (fun _ k ↦ k) = H →
    Tendsto (fun k ↦ (a k).polynomial.coeff e) atTop (𝓝 (Q.coeff e))

/-- Any unbounded sequence of actual vanilla classifiers for a rigid source
produces an oriented-factor coefficient sequence converging to a nonzero
scalar multiple of that source. -/
theorem factor_limit_of_vanilla_sequence {n H : ℕ} (hH : 0 < H)
    (P : MvPolynomial (Fin n) ℝ)
    (hrigid : ∀ Q : MvPolynomial (Fin n) ℝ, Q ≠ 0 → Q.totalDegree ≤ H →
      (∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
        (0 < eval q P → 0 ≤ eval q Q) ∧ (eval q P < 0 → eval q Q ≤ 0)) →
      ∃ t : ℝ, t ≠ 0 ∧ Q = C t * P)
    (m : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hm : Tendsto m atTop atTop)
    (hf : ∀ k, computableWithSharedHeadsN (n * m k) H
      (ReplicatedThresholdDegree.classifier (fun q ↦ eval q P) (m k))) :
    ∃ (a : ℕ → Data H (Fin n)) (t : ℝ), t ≠ 0 ∧
      (∀ k h, VanillaThreeCentered.Oriented ((a k).denominatorSlope h)) ∧
      TopCoefficientLimit a (C t * P) := by
  classical
  let F : (Fin n → ℝ) → Bool := fun q ↦ decide (0 < eval q P)
  have hex (k : ℕ) := exists_averaged_data_of_vanilla hH (hmpos k) F (hf k)
  choose a horient hne hdeg hstrict htop using hex
  let A : ℕ → MvPolynomial (Fin n) ℝ := fun k ↦ averagedGroupPolynomial (a k).polynomial
  obtain ⟨t, Q, φ, ht, hQne, hQdeg, hφ, hcoeff⟩ :=
    BoundedCoefficientLimit.normalized_polynomial_subsequence A hdeg hne
  let R : ℕ → MvPolynomial (Fin n) ℝ := fun k ↦ C (t (φ k)) * A (φ k)
  have hRdeg (k : ℕ) : (R k).totalDegree ≤ H := by
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using hdeg (φ k))
  have hsign (k : ℕ) (q : Fin n → ℝ) (hq : InCenteredGrid (m (φ k)) q) :
      0 < eval q (R k) ↔ 0 < eval q P := by
    rw [show R k = C (t (φ k)) * A (φ k) from rfl, map_mul, eval_C,
      mul_pos_iff_of_pos_left (ht (φ k))]
    obtain ⟨x, hx⟩ := exists_mean_eq_of_inCenteredGrid (hmpos (φ k)) q hq
    have hs := hstrict (φ k) x
    rw [hx] at hs
    constructor
    · intro hp
      cases hF : F q with
      | false => exact False.elim ((not_lt_of_gt (hs.2 hF)) hp)
      | true => exact of_decide_eq_true hF
    · intro hp
      exact hs.1 (by exact decide_eq_true hp)
  have hweak (q : Fin n → ℝ) (hq : ∀ i, -1 ≤ q i ∧ q i ≤ 1) :
      (0 < eval q P → 0 ≤ eval q Q) ∧ (eval q P < 0 → eval q Q ≤ 0) := by
    apply weak_sign_of_grid_limit (fun q ↦ eval q P) (fun q ↦ eval q Q)
      (fun k q ↦ eval q (R k)) (m ∘ φ) (fun k ↦ hmpos (φ k))
      (hm.comp hφ.tendsto_atTop) P.continuous_eval hsign ?_ q hq
    intro y z hz
    exact BoundedCoefficientLimit.tendsto_eval_of_bounded_coefficients
      R Q hRdeg hQdeg hcoeff z y hz
  obtain ⟨s, hs, hQ⟩ := hrigid Q hQne hQdeg hweak
  let b : ℕ → Data H (Fin n) := fun k ↦ scaleNumerators (t (φ k)) (a (φ k)).aggregate
  refine ⟨b, s, hs, fun k h ↦ horient (φ k) h, ?_⟩
  intro e he hcard
  have hbe (k : ℕ) : (b k).polynomial.coeff e = (R k).coeff e := by
    dsimp [b, R, A]
    rw [scaleNumerators_polynomial, coeff_C_mul, coeff_C_mul,
      htop (φ k) e he hcard]
  simpa only [hbe, hQ] using hcoeff e

/-- An explicit algebraic coefficient-limit obstruction excludes actual
vanilla classifiers at every sufficiently large replication count. -/
theorem eventually_not_vanilla_of_factor_limit_obstruction {n H : ℕ} (hH : 0 < H)
    (P : MvPolynomial (Fin n) ℝ)
    (hrigid : ∀ Q : MvPolynomial (Fin n) ℝ, Q ≠ 0 → Q.totalDegree ≤ H →
      (∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
        (0 < eval q P → 0 ≤ eval q Q) ∧ (eval q P < 0 → eval q Q ≤ 0)) →
      ∃ t : ℝ, t ≠ 0 ∧ Q = C t * P)
    (hno : ∀ (a : ℕ → Data H (Fin n)) (t : ℝ), t ≠ 0 →
      (∀ k h, VanillaThreeCentered.Oriented ((a k).denominatorSlope h)) →
      ¬ TopCoefficientLimit a (C t * P)) :
    ∀ᶠ m in atTop, ¬ computableWithSharedHeadsN (n * m) H
      (ReplicatedThresholdDegree.classifier (fun q ↦ eval q P) m) := by
  classical
  by_contra hn
  have hf : ∃ᶠ m in atTop, computableWithSharedHeadsN (n * m) H
      (ReplicatedThresholdDegree.classifier (fun q ↦ eval q P) m) := hn
  have hex : ∀ k : ℕ, ∃ m, k + 1 ≤ m ∧ computableWithSharedHeadsN (n * m) H
      (ReplicatedThresholdDegree.classifier (fun q ↦ eval q P) m) :=
    fun k ↦ frequently_atTop.mp hf (k + 1)
  choose m hlarge hw using hex
  have hmpos (k : ℕ) : 0 < m k := by have := hlarge k; omega
  have hm : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun k hk ↦ by have := hlarge k; omega⟩
  obtain ⟨a, t, ht, horient, hlim⟩ := factor_limit_of_vanilla_sequence hH P hrigid m hmpos hm hw
  exact hno a t ht horient hlim

end HeadComplexity.VanillaCoefficientLimit
