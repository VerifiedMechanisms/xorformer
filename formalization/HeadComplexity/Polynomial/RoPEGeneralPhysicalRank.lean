import HeadComplexity.Polynomial.RoPEGeneralPhysicalBlocks
import HeadComplexity.Polynomial.BlockCoefficientDerivatives

/-! The source contraction rank is invariant under the actual block coordinates. -/

noncomputable section

namespace HeadComplexity.RoPEGeneralPhysicalRank

open MvPolynomial RoPEGeneralDerivative RoPEGeneralPolarization
open RoPEGeneralPhysicalBlocks AffineCoordinateEquivalence
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype τ] in
theorem directional_coordinatePolynomial (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ))
    (c : τ → ℝ) (v : σ → ℝ) (i : τ) :
    directional v (polynomial L c i) = C (L v i) := by
  classical
  unfold polynomial
  simp only [map_add, directional_C, zero_add, map_sum, Derivation.leibniz,
    directional_X, smul_eq_mul, mul_zero, add_zero]
  simp only [← map_mul, ← map_sum]
  congr 1
  rw [LinearMap.pi_apply_eq_sum_univ L v]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

theorem directional_substitutionEquiv
    (E : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ)
    (v : σ → ℝ) (P : MvPolynomial τ ℝ) :
    directional v (substitutionEquiv E c P) =
      substitutionEquiv E c (directional (E v) P) := by
  exact directional_eval₂ (E v) v (polynomial E.toLinearMap c)
    (directional_coordinatePolynomial E.toLinearMap c v) P

omit [Fintype τ] in
theorem coordinatePolynomial_homogeneous
    (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (i : τ) :
    (polynomial L 0 i).IsHomogeneous 1 := by
  classical
  simp only [polynomial, Pi.zero_apply, map_zero, zero_add]
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X ℝ j).C_mul _

theorem substitutionEquiv_homogeneous
    (E : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ))
    {P : MvPolynomial τ ℝ} {d : ℕ} (hP : P.IsHomogeneous d) :
    (substitutionEquiv E 0 P).IsHomogeneous d := by
  change (eval₂ C (polynomial E.toLinearMap 0) P).IsHomogeneous d
  simpa using hP.eval₂ C (polynomial E.toLinearMap 0)
    (fun c => isHomogeneous_C (σ := σ) c) (coordinatePolynomial_homogeneous E.toLinearMap)

def secondLinear (P : MvPolynomial σ ℝ) (v : σ → ℝ) :
    (σ → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun w := directional w (directional v P)
  map_add' := by intro w z; rw [directional_add]; rfl
  map_smul' := by intro c w; rw [directional_smul]; rfl

theorem secondLinear_substitutionEquiv
    (E : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ)
    (v : σ → ℝ) (P : MvPolynomial τ ℝ) :
    secondLinear (substitutionEquiv E c P) v =
      (substitutionEquiv E c).toLinearMap.comp
        ((secondLinear P (E v)).comp E.toLinearMap) := by
  apply LinearMap.ext
  intro w
  change directional w (directional v (substitutionEquiv E c P)) = _
  rw [directional_substitutionEquiv, directional_substitutionEquiv]
  rfl

theorem secondLinear_substitution_rank
    (E : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ)
    (v : σ → ℝ) (P : MvPolynomial τ ℝ) :
    Module.finrank ℝ (secondLinear (substitutionEquiv E c P) v).range =
      Module.finrank ℝ (secondLinear P (E v)).range := by
  rw [secondLinear_substitutionEquiv, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]
  exact (substitutionEquiv E c).toLinearEquiv.finrank_map_eq _

theorem secondLinear_source_eq {H : ℕ} (v : Var H → ℝ) :
    secondLinear (source H) v =
      (secondMap (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))).comp
        (LinearEquiv.sumArrowLequivProdArrow (Fin H) (Fin H) ℝ ℝ).toLinearMap := by
  apply LinearMap.ext
  intro w
  have hv : direction (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i; cases i <;> rfl
  have hw : direction (fun i => w (Sum.inl i)) (fun i => w (Sum.inr i)) = w := by
    funext i; cases i <;> rfl
  change directional w (directional v (source H)) =
    directional (direction (fun i => w (Sum.inl i)) (fun i => w (Sum.inr i)))
      (directional (direction (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))) (source H))
  rw [hv, hw]

theorem secondLinear_source_rank_le_iff {H : ℕ} (hH : 3 ≤ H) (v : Var H → ℝ) :
    Module.finrank ℝ (secondLinear (source H) v).range ≤ H ↔
      (fun i => v (Sum.inl i)) = 0 := by
  rw [secondLinear_source_eq, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, secondMap_rank_le_iff hH]

theorem localSource_zero_homogeneous (m : ℕ) :
    (localSource m 0).IsHomogeneous (m + 2) := by
  rw [localSource_zero_eq_substitution]
  exact substitutionEquiv_homogeneous _ (source_isHomogeneous _)

theorem contractMap_blockLift_localSource (m : ℕ) (v : Local m → ℝ) :
    contractMap m (blockLift m (localSource m 0)) v =
      (m.factorial : ℝ) • secondLinear (localSource m 0) v := by
  apply LinearMap.ext
  intro w
  apply contractDiagonal_blockLift
  simpa using directional_isHomogeneous w
    (directional_isHomogeneous v (localSource_zero_homogeneous m))

theorem contractMap_localSource_rank (m : ℕ) (v : Local m → ℝ) :
    Module.finrank ℝ (contractMap m (blockLift m (localSource m 0)) v).range =
      Module.finrank ℝ (secondLinear (source (m + 2)) (localCoordinateEquiv m v)).range := by
  rw [contractMap_blockLift_localSource, LinearMap.range_smul _ _
    (by exact_mod_cast Nat.factorial_ne_zero m), localSource_zero_eq_substitution]
  exact secondLinear_substitution_rank _ _ _ _

theorem contractMap_localSource_rank_le_iff (m : ℕ) (hm : 1 ≤ m)
    (v : Local m → ℝ) :
    Module.finrank ℝ (contractMap m (blockLift m (localSource m 0)) v).range ≤ m + 2 ↔
      (fun i => v (Sum.inl i)) = (fun i => v (Sum.inr i)) := by
  rw [contractMap_localSource_rank, secondLinear_source_rank_le_iff (by omega)]
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simpa only [localCoordinateEquiv_left, Pi.zero_apply, sub_eq_zero] using hi
  · intro h
    funext i
    simp only [localCoordinateEquiv_left, congrFun h i, sub_self, Pi.zero_apply]

omit [Fintype σ] in
theorem contractMap_C_mul (m : ℕ) (t : ℝ) (P : BlockPoly m σ) (v : σ → ℝ) :
    contractMap m (C t * P) v = t • contractMap m P v := by
  apply LinearMap.ext
  intro w
  change projection m (directional _ (directional _ (C t * P))) = _
  simp only [← smul_eq_C_mul, Derivation.map_smul, map_smul]
  rfl

theorem contractMap_scaled_localSource_rank_le_iff (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (ht : t ≠ 0) (v : Local m → ℝ) :
    Module.finrank ℝ (contractMap m (C t * blockLift m (localSource m 0)) v).range ≤ m + 2 ↔
      (fun i => v (Sum.inl i)) = (fun i => v (Sum.inr i)) := by
  rw [contractMap_C_mul, LinearMap.range_smul _ _ ht,
    contractMap_localSource_rank_le_iff m hm]

theorem contractMap_reindexedPhysical (m : ℕ) (v : Local m → ℝ) :
    contractMap m (reindexedPhysical m) v =
      contractMap m (blockLift m (localSource m 0)) v := by
  apply LinearMap.ext
  intro w
  apply BlockCoefficientDerivatives.contractDiagonal_eq_of_top_coeff_eq
  intro e he hdeg
  exact reindexedPhysical_top_coeff m e hdeg

theorem contractMap_scaled_reindexedPhysical_rank_le_iff (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (ht : t ≠ 0) (v : Local m → ℝ) :
    Module.finrank ℝ (contractMap m (C t * reindexedPhysical m) v).range ≤ m + 2 ↔
      (fun i => v (Sum.inl i)) = (fun i => v (Sum.inr i)) := by
  rw [contractMap_C_mul, LinearMap.range_smul _ _ ht,
    contractMap_reindexedPhysical, contractMap_localSource_rank_le_iff m hm]

end HeadComplexity.RoPEGeneralPhysicalRank
