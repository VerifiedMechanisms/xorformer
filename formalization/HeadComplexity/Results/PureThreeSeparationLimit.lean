import HeadComplexity.Polynomial.RoPEGridLimit
import HeadComplexity.Polynomial.RoPEMixedTensor
import HeadComplexity.Atoms.RoPETensorFactors

set_option linter.style.header false

/-!
# Assembling the averaged-polynomial separation argument

The witness structure records exactly the remaining bridge from a finite
vanilla representation. The theorem below proves that such witnesses cannot
exist on an unbounded sequence of centered grids when the source has the
proved sign rigidity and tensor obstruction.
-/

namespace HeadComplexity.PureThreeSeparationLimit

open MvPolynomial RoPEGridLimit RoPEMixedTensor RoPEThreeTensor
open scoped Topology
open Filter

abbrev Poly := MvPolynomial (Fin 18) ℝ
abbrev Rows := Matrix (Fin 3) (Fin 6) ℝ

structure AveragedWitness (P : Poly) (m : ℕ) where
  polynomial : Poly
  degree_le : polynomial.totalDegree ≤ 3
  nonzero : polynomial ≠ 0
  grid_sign : ∀ q, InCenteredGrid m q → (0 < eval q polynomial ↔ 0 < eval q P)
  D₁ : Rows
  N₁ : Rows
  D₂ : Rows
  N₂ : Rows
  D₃ : Rows
  N₃ : Rows
  factorization : mixedTensor polynomial = factorTensor D₁ N₁ D₂ N₂ D₃ N₃
  oriented : mixedTensor polynomial ≠ 0 →
    ∃ h σ, (∀ j, 0 ≤ σ * D₁ h j) ∧ 0 < ∑ j, σ * D₁ h j

/-- Source sign rigidity and the tensor obstruction rule out averaged
three-head witnesses along every unbounded sequence of replication counts. -/
theorem no_averaged_witness_sequence (P : Poly)
    (hrigid : ∀ Q : Poly, Q ≠ 0 → Q.totalDegree ≤ 3 →
      (∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
        (0 < eval q P → 0 ≤ eval q Q) ∧ (eval q P < 0 → eval q Q ≤ 0)) →
      ∃ a : ℝ, a ≠ 0 ∧ Q = C a * P)
    (hsource : mixedTensor P = factorTensor (denominatorRows 1) (numeratorRows 2)
      (denominatorRows 1) (numeratorRows 2) (denominatorRows 1) (numeratorRows 2))
    (hsource_ne : mixedTensor P ≠ 0)
    (m : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hm : Tendsto m atTop atTop)
    (w : ∀ k, AveragedWitness P (m k)) : False := by
  obtain ⟨t, Q, φ, ht, hQne, hQdeg, hφ, hcoeff⟩ :=
    BoundedCoefficientLimit.normalized_polynomial_subsequence
      (fun k ↦ (w k).polynomial) (fun k ↦ (w k).degree_le) (fun k ↦ (w k).nonzero)
  let R : ℕ → Poly := fun k ↦ C (t (φ k)) * (w (φ k)).polynomial
  have hRdeg (k : ℕ) : (R k).totalDegree ≤ 3 := by
    have h := totalDegree_mul (C (t (φ k))) (w (φ k)).polynomial
    simpa only [totalDegree_C, zero_add] using h.trans (by
      simpa only [totalDegree_C, zero_add] using (w (φ k)).degree_le)
  have hweak (q : Fin 18 → ℝ) (hq : ∀ i, -1 ≤ q i ∧ q i ≤ 1) :
      (0 < eval q P → 0 ≤ eval q Q) ∧ (eval q P < 0 → eval q Q ≤ 0) := by
    apply weak_sign_of_grid_limit (fun q ↦ eval q P) (fun q ↦ eval q Q)
      (fun k q ↦ eval q (R k)) (m ∘ φ) (fun k ↦ hmpos (φ k))
      (hm.comp hφ.tendsto_atTop) P.continuous_eval ?_ ?_ q hq
    · intro k z hz
      change 0 < eval z (C (t (φ k)) * (w (φ k)).polynomial) ↔ 0 < eval z P
      rw [map_mul, eval_C, mul_pos_iff_of_pos_left (ht (φ k))]
      exact (w (φ k)).grid_sign z hz
    · intro y z hz
      exact BoundedCoefficientLimit.tendsto_eval_of_bounded_coefficients
        R Q hRdeg hQdeg hcoeff z y hz
  obtain ⟨a, ha, hQ⟩ := hrigid Q hQne hQdeg hweak
  have hTlim := tendsto_mixedTensor_of_coefficients R Q hcoeff
  rw [hQ, mixedTensor_C_mul] at hTlim
  have haT : a • mixedTensor P ≠ 0 := smul_ne_zero ha hsource_ne
  have hTne : ∀ᶠ k in atTop, mixedTensor (R k) ≠ 0 := hTlim.eventually_ne haT
  let D₁ : ℕ → Rows := fun k ↦ (w (φ k)).D₁
  let D₂ : ℕ → Rows := fun k ↦ (w (φ k)).D₂
  let D₃ : ℕ → Rows := fun k ↦ (w (φ k)).D₃
  let N₁ : ℕ → Rows := fun k ↦ t (φ k) • (w (φ k)).N₁
  let N₂ : ℕ → Rows := fun k ↦ t (φ k) • (w (φ k)).N₂
  let N₃ : ℕ → Rows := fun k ↦ t (φ k) • (w (φ k)).N₃
  have hfactor (k : ℕ) : mixedTensor (R k) =
      factorTensor (D₁ k) (N₁ k) (D₂ k) (N₂ k) (D₃ k) (N₃ k) := by
    dsimp [R, D₁, D₂, D₃, N₁, N₂, N₃]
    rw [mixedTensor_C_mul, (w (φ k)).factorization, factorTensor_smul_numerators]
  have horient : ∀ᶠ k in atTop, ∃ h σ, (∀ j, 0 ≤ σ * D₁ k h j) ∧
      0 < ∑ j, σ * D₁ k h j := hTne.mono fun k hk ↦ (w (φ k)).oriented (by
        intro hz
        apply hk
        simp only [R, mixedTensor_C_mul, hz, smul_zero])
  obtain ⟨K, hK⟩ := eventually_atTop.mp horient
  have hlim : Tendsto
      (fun k ↦ factorTensor (D₁ (k + K)) (N₁ (k + K)) (D₂ (k + K)) (N₂ (k + K))
        (D₃ (k + K)) (N₃ (k + K))) atTop
      (𝓝 (a • factorTensor (denominatorRows 1) (numeratorRows 2)
        (denominatorRows 1) (numeratorRows 2) (denominatorRows 1) (numeratorRows 2))) := by
    have hh := hTlim.comp (tendsto_add_atTop_nat K)
    simpa only [Function.comp_def, hfactor, hsource] using hh
  exact no_tendsto_scaled_physical_source_factorTensor 1 2 a (by norm_num) (by norm_num) ha
    (fun k ↦ D₁ (k + K)) (fun k ↦ N₁ (k + K))
    (fun k ↦ D₂ (k + K)) (fun k ↦ N₂ (k + K))
    (fun k ↦ D₃ (k + K)) (fun k ↦ N₃ (k + K))
    (fun k ↦ hK (k + K) (by omega)) hlim

/-- Excluding witnesses on every unbounded positive sequence implies their
eventual absence. This also handles arbitrarily sparse sets of replication
counts. -/
theorem eventually_no_witness_of_no_sequence (W : ℕ → Type*)
    (h : ∀ (m : ℕ → ℕ), (∀ k, 0 < m k) → Tendsto m atTop atTop →
      (∀ k, W (m k)) → False) : ∀ᶠ m in atTop, ¬Nonempty (W m) := by
  classical
  by_contra hnot
  have hf : ∃ᶠ m in atTop, Nonempty (W m) := hnot
  have hex : ∀ k : ℕ, ∃ m, k + 1 ≤ m ∧ Nonempty (W m) :=
    fun k ↦ frequently_atTop.mp hf (k + 1)
  choose m hm hw using hex
  have hmpos (k : ℕ) : 0 < m k := by have := hm k; omega
  have hmt : Tendsto m atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun k hk ↦ by have := hm k; omega⟩
  exact h m hmpos hmt (fun k ↦ Classical.choice (hw k))

end HeadComplexity.PureThreeSeparationLimit
