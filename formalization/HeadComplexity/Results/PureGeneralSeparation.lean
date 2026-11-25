import HeadComplexity.Results.PureGeneralSeparationReduction
import HeadComplexity.Polynomial.VanillaFactorReindex
import HeadComplexity.Polynomial.RoPEGeneralPhysicalRank
import HeadComplexity.Polynomial.BlockCoefficientLimit
import HeadComplexity.Polynomial.RoPEVanillaContractionRank
import HeadComplexity.Atoms.RoPESequentialFrames

set_option linter.style.header false

/-!
# Pure rotary attention separates from vanilla attention at every budget above two

This module discharges the oriented factor-limit obstruction from actual
vanilla classifiers. All averaging, polynomial limit, source rigidity, physical
coordinate, contraction rank, and compact frame steps are connected here.
-/

noncomputable section

namespace HeadComplexity.PureGeneralReplicatedGrid

open MvPolynomial Filter VanillaGeneralCentered VanillaCoefficientLimit
open RoPEGeneralPhysicalCoordinates RoPEGeneralPhysicalBlocks
open RoPEGeneralPolarization RoPEGeneralPhysicalRank VanillaFactorReindex
open RoPEGeneralCoordinates RoPEGeneralFrames
open scoped BigOperators Topology

theorem oriented_factor_limit_excluded_succ (m : ℕ) (hm : 1 ≤ m) :
    OrientedFactorLimitExcluded (m + 1) := by
  classical
  intro a t ht ha hlim
  let b : ℕ → Data (m + 2) (Block m × Local m) :=
    fun k ↦ reindex (physicalEquiv m) (a k)
  let Q : BlockPoly m (Local m) := C t * blockLift m (localSource m 0)
  let L := fun k (v : Space (m + 2)) ↦ contractMap m (b k).polynomial (flatten v)
  let M := fun (v : Space (m + 2)) ↦ contractMap m Q (flatten v)
  let D := fun k ↦ VanillaBlockDerivatives.denominatorRows (b k) (none : Block m)
  have hb (k : ℕ) : ∀ i, VanillaThreeCentered.Oriented ((b k).denominatorSlope i) :=
    reindex_oriented (physicalEquiv m) (a k) (ha k)
  have htop (e : Block m × Local m →₀ ℕ) (he : ∀ i, e i ≤ 1)
      (hdegree : e.sum (fun _ k ↦ k) = m + 2) :
      Tendsto (fun k ↦ (b k).polynomial.coeff e) atTop (𝓝 (Q.coeff e)) :=
    top_limit_physical_blocks m a t hlim e he hdegree
  apply no_conditionally_oriented_polynomial_rank_limit (by omega : 0 < m + 2)
    m L M D
  · intro v w
    exact contractDiagonal_totalDegree_le m Q (flatten v) w
  · intro φ hφ w v hw i e
    have hf : Continuous (flatten : Space (m + 2) → Local m → ℝ) := by
      apply continuous_pi
      intro j
      cases j <;> simp only [flatten, Sum.elim_inl, Sum.elim_inr] <;> fun_prop
    exact BlockCoefficientLimit.tendsto_contractDiagonal_coeff m
      (fun k ↦ (b (φ k)).polynomial) Q
      (fun d hd hc ↦ (htop d hd hc).comp hφ.tendsto_atTop)
      (fun k ↦ flatten (w k)) (fun _ ↦ Pi.single i 1)
      (flatten v) (Pi.single i 1) (hf.continuousAt.tendsto.comp hw)
      tendsto_const_nhds e
  · intro v hv
    simpa only [flatten, Sum.elim_inl, Sum.elim_inr] using
      (contractMap_scaled_localSource_rank_le_iff m hm t ht (flatten v)).mp hv
  · intro k v hv
    exact RoPEVanillaContractionRank.contractMap_rank_le (b k) (flatten v) hv
  · intro k hk
    exact RoPEVanillaContractionRank.data_oriented_row_of_ne_zero (b k) (hb k) hk

theorem oriented_factor_limit_excluded (h : ℕ) (hh : 2 ≤ h) :
    OrientedFactorLimitExcluded h := by
  have he : h - 1 + 1 = h := by omega
  rw [← he]
  exact oriented_factor_limit_excluded_succ (h - 1) (by omega)

/-- Every fixed head budget at least three has an eventual actual Boolean
separation, with exact pure minimum and an explicit finite vanilla upper bound. -/
theorem eventually_complexity_separation_general (H : ℕ) (hH : 3 ≤ H) :
    ∀ᶠ m in atTop,
      PureRoPEHStar (groupCount H * m) (classifier H m) = H ∧
      H + 1 ≤ SharedHStar (groupCount H * m) (classifier H m) ∧
      SharedHStar (groupCount H * m) (classifier H m) ≤ 2 ^ H - 2 ∧
      StandardPureRoPEHStar (groupCount H * m) (classifier H m) = H ∧
      FreePureRoPEHStar (groupCount H * m) (classifier H m) = H := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : H ≠ 0)
  exact eventually_separation_of_factor_obstruction h (by omega)
    (oriented_factor_limit_excluded h (by omega))

theorem eventually_not_vanilla_general (H : ℕ) (hH : 3 ≤ H) :
    ∀ᶠ m in atTop, ¬ computableWithSharedHeadsN (groupCount H * m) H
      (classifier H m) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : H ≠ 0)
  exact eventually_not_vanilla_of_factor_obstruction h
    (oriented_factor_limit_excluded h (by omega))

end HeadComplexity.PureGeneralReplicatedGrid
