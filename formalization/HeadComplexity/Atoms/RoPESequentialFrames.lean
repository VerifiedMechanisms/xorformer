import HeadComplexity.Atoms.RoPEGeneralKernelFrames
import HeadComplexity.Polynomial.RoPEPolynomialRankLimit

/-!
# Sequential kernel-frame obstruction for polynomial contraction limits

This version only assumes convergence of coefficients along moving vectors.
It avoids imposing a topology on the polynomial ring or any boundedness on
candidate denominator matrices.
-/

noncomputable section

namespace HeadComplexity.RoPEGeneralFrames

open RoPEGeneralCoordinates
open scoped BigOperators Topology

theorem no_frames_of_sequential_paired_limit {H : ℕ}
    (low : ℕ → Space H → Prop)
    (hsequential : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (w : ℕ → Space H) (v : Space H),
      Filter.Tendsto w Filter.atTop (nhds v) →
      (∀ k, low (φ k) (w k)) → v.1 = v.2)
    (hframes : ∀ k, ∃ (w : Fin H → Space H) (v : Space H),
      (∀ a b, dot (w a) (w b) = if a = b then 1 else 0) ∧
      ((∀ i, 0 ≤ v.1 i) ∧ (∀ i, 0 ≤ v.2 i)) ∧ total v = 1 ∧
      (∀ a, dot (w a) v = 0) ∧ (∀ a, low k (w a))) : False := by
  choose w v hgram hvpos hvsum horth hlow using hframes
  let X := (Fin H → Space H) × Space H
  let lo : X := (fun _ ↦ (fun _ ↦ -1, fun _ ↦ -1), (fun _ ↦ 0, fun _ ↦ 0))
  let hi : X := (fun _ ↦ (fun _ ↦ 1, fun _ ↦ 1), (fun _ ↦ 1, fun _ ↦ 1))
  have hbound (k : ℕ) : (w k, v k) ∈ Set.Icc lo hi := by
    have hwbound (a : Fin H) := coordinate_bounds_of_unit_dot (w k a)
      (by simpa using hgram k a a)
    have hvbound := coordinate_bounds_of_simplex (v k) (hvpos k) (hvsum k)
    constructor
    · constructor
      · intro a
        constructor
        · intro i; exact ((hwbound a).1 i).1
        · intro i; exact ((hwbound a).2 i).1
      · exact hvpos k
    · constructor
      · intro a
        constructor
        · intro i; exact ((hwbound a).1 i).2
        · intro i; exact ((hwbound a).2 i).2
      · exact hvbound
  obtain ⟨Z, _, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc lo hi)).tendsto_subseq hbound
  have hw : Filter.Tendsto (fun k ↦ w (φ k)) Filter.atTop (nhds Z.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hv : Filter.Tendsto (fun k ↦ v (φ k)) Filter.atTop (nhds Z.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  have hp (a : Fin H) : (Z.1 a).1 = (Z.1 a).2 := by
    have hwa : Filter.Tendsto (fun k ↦ w (φ k) a) Filter.atTop (nhds (Z.1 a)) :=
      (continuous_apply a).continuousAt.tendsto.comp hw
    exact hsequential φ hφ (fun k ↦ w (φ k) a) (Z.1 a) hwa
      (fun k ↦ hlow (φ k) a)
  have hg (a b : Fin H) : dot (Z.1 a) (Z.1 b) = if a = b then 1 else 0 := by
    have hc : Continuous (fun W : Fin H → Space H ↦ dot (W a) (W b)) := by
      unfold dot
      fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hw)
    simpa only [Function.comp_def, hgram] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ (if a = b then 1 else 0 : ℝ)) Filter.atTop (nhds _))
  have ho (a : Fin H) : dot (Z.1 a) Z.2 = 0 := by
    have hc : Continuous (fun Y : X ↦ dot (Y.1 a) Y.2) := by
      change Continuous (fun Y : (Fin H → Space H) × Space H ↦ dot (Y.1 a) Y.2)
      unfold dot
      fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hlim)
    simpa only [Function.comp_def, horth] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds _))
  have hn : total Z.2 = 1 := by
    have hc : Continuous (fun V : Space H ↦ total V) := by
      unfold total
      fun_prop
    apply tendsto_nhds_unique (hc.continuousAt.tendsto.comp hv)
    simpa only [Function.comp_def, hvsum] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds _))
  exact no_unit_sum_orthogonal_paired_frame Z.1 Z.2 hp hg ho hn

/-- A matrix sequence needs only a single nonzero oriented row at each index. -/
theorem no_oriented_kernels_of_sequential_paired_limit {H : ℕ}
    (D : ℕ → Matrix (Fin H) (Fin H ⊕ Fin H) ℝ)
    (hsequential : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (w : ℕ → Space H) (v : Space H),
      Filter.Tendsto w Filter.atTop (nhds v) →
      (∀ k, (D (φ k)).mulVec (flatten (w k)) = 0) → v.1 = v.2)
    (horient : ∀ k, ∃ h σ, (∀ i, 0 ≤ σ * D k h i) ∧ 0 < ∑ i, σ * D k h i) :
    False := by
  apply no_frames_of_sequential_paired_limit
    (fun k v ↦ (D k).mulVec (flatten v) = 0) hsequential
  intro k
  obtain ⟨h, σ, hp, hs⟩ := horient k
  exact exists_oriented_kernel_frame (D k) h σ hp hs

/-- Coefficient limits of polynomial-valued contractions suffice to exclude
oriented denominator kernels when the limiting low-rank locus is paired. -/
theorem no_oriented_polynomial_rank_limit {H : ℕ} {σ ι : Type*}
    [Finite σ] [Finite ι] [DecidableEq ι] (d : ℕ)
    (L : ℕ → Space H → (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (M : Space H → (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (D : ℕ → Matrix (Fin H) (Fin H ⊕ Fin H) ℝ)
    (hdegree : ∀ v w, (M v w).totalDegree ≤ d)
    (hlimit : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (w : ℕ → Space H) (v : Space H),
      Filter.Tendsto w Filter.atTop (nhds v) →
      ∀ i e, Filter.Tendsto
        (fun k ↦ (L (φ k) (w k) (Pi.single i 1)).coeff e)
        Filter.atTop (nhds ((M v (Pi.single i 1)).coeff e)))
    (hsource : ∀ v, Module.finrank ℝ (M v).range ≤ H → v.1 = v.2)
    (hkernel : ∀ k v, (D k).mulVec (flatten v) = 0 →
      Module.finrank ℝ (L k v).range ≤ H)
    (horient : ∀ k, ∃ h s, (∀ i, 0 ≤ s * D k h i) ∧ 0 < ∑ i, s * D k h i) :
    False := by
  apply no_oriented_kernels_of_sequential_paired_limit D ?_ horient
  intro φ hφ w v hw hker
  apply hsource v
  apply RoPEPolynomialRankLimit.rank_le_of_coefficient_tendsto d H
    (fun k ↦ L (φ k) (w k)) (M v) (hdegree v)
  · exact hlimit φ hφ w v hw
  · intro k
    exact hkernel (φ k) (w k) (hker k)

/-- A zero-matrix subsequence would force every constant vector into the paired
source kernel, which is impossible in a nonempty coordinate space. -/
theorem eventually_nonzero_of_sequential_kernel_limit {H : ℕ} (hH : 0 < H)
    (D : ℕ → Matrix (Fin H) (Fin H ⊕ Fin H) ℝ)
    (hsequential : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (w : ℕ → Space H) (v : Space H),
      Filter.Tendsto w Filter.atTop (nhds v) →
      (∀ k, (D (φ k)).mulVec (flatten (w k)) = 0) → v.1 = v.2) :
    ∀ᶠ k in Filter.atTop, D k ≠ 0 := by
  by_contra h
  have hf : ∃ᶠ k in Filter.atTop, D k = 0 := by
    simpa only [not_not] using Filter.not_eventually.mp h
  obtain ⟨φ, hφ, hz⟩ := Filter.extraction_of_frequently_atTop hf
  let v : Space H := (fun _ ↦ 1, fun _ ↦ 0)
  have hp := hsequential φ hφ (fun _ ↦ v) v tendsto_const_nhds
    (fun k ↦ by rw [hz k]; simp)
  have hh := congrFun hp ⟨0, hH⟩
  norm_num [v] at hh

/-- Conditional row orientation suffices: zero matrices are ruled out by the
source rank locus itself before the compact frame argument is used. -/
theorem no_conditionally_oriented_kernels_of_sequential_paired_limit {H : ℕ}
    (hH : 0 < H) (D : ℕ → Matrix (Fin H) (Fin H ⊕ Fin H) ℝ)
    (hsequential : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (w : ℕ → Space H) (v : Space H),
      Filter.Tendsto w Filter.atTop (nhds v) →
      (∀ k, (D (φ k)).mulVec (flatten (w k)) = 0) → v.1 = v.2)
    (horient : ∀ k, D k ≠ 0 →
      ∃ h σ, (∀ i, 0 ≤ σ * D k h i) ∧ 0 < ∑ i, σ * D k h i) : False := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_nonzero_of_sequential_kernel_limit hH D hsequential)
  apply no_oriented_kernels_of_sequential_paired_limit (fun k ↦ D (k + N)) ?_ ?_
  · intro φ hφ w v hw hk
    exact hsequential (fun k ↦ φ k + N)
      (fun i j hij ↦ Nat.add_lt_add_right (hφ hij) N) w v hw hk
  · intro k
    exact horient (k + N) (hN (k + N) (Nat.le_add_left N k))

theorem no_conditionally_oriented_polynomial_rank_limit {H : ℕ} {σ ι : Type*}
    [Finite σ] [Finite ι] [DecidableEq ι] (hH : 0 < H) (d : ℕ)
    (L : ℕ → Space H → (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (M : Space H → (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (D : ℕ → Matrix (Fin H) (Fin H ⊕ Fin H) ℝ)
    (hdegree : ∀ v w, (M v w).totalDegree ≤ d)
    (hlimit : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (w : ℕ → Space H) (v : Space H),
      Filter.Tendsto w Filter.atTop (nhds v) →
      ∀ i e, Filter.Tendsto
        (fun k ↦ (L (φ k) (w k) (Pi.single i 1)).coeff e)
        Filter.atTop (nhds ((M v (Pi.single i 1)).coeff e)))
    (hsource : ∀ v, Module.finrank ℝ (M v).range ≤ H → v.1 = v.2)
    (hkernel : ∀ k v, (D k).mulVec (flatten v) = 0 →
      Module.finrank ℝ (L k v).range ≤ H)
    (horient : ∀ k, D k ≠ 0 →
      ∃ h s, (∀ i, 0 ≤ s * D k h i) ∧ 0 < ∑ i, s * D k h i) : False := by
  apply no_conditionally_oriented_kernels_of_sequential_paired_limit hH D ?_ horient
  intro φ hφ w v hw hker
  apply hsource v
  apply RoPEPolynomialRankLimit.rank_le_of_coefficient_tendsto d H
    (fun k ↦ L (φ k) (w k)) (M v) (hdegree v)
  · exact hlimit φ hφ w v hw
  · intro k
    exact hkernel (φ k) (w k) (hker k)

end HeadComplexity.RoPEGeneralFrames
