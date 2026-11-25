import HeadComplexity.Polynomial.RoPEGeneralPhysicalCoordinates
import HeadComplexity.Polynomial.RoPEGeneralPolarization
import HeadComplexity.Polynomial.AffineProductTopDegree

set_option linter.style.header false

/-! # Reindexing the actual source into the blocks used by polarization -/

namespace HeadComplexity.RoPEGeneralPhysicalBlocks

open MvPolynomial RoPEGeneralPolarization PureGeneralReplicatedGrid
open scoped BigOperators

abbrev Local (m : ℕ) := Fin (m + 2) ⊕ Fin (m + 2)

def blockEquiv (m : ℕ) : Block m ≃ Fin (m + 2) :=
  (Equiv.optionCongr (_root_.finSuccEquiv m).symm).trans (_root_.finSuccEquiv (m + 1)).symm

def localEquiv (H : ℕ) : (Fin H ⊕ Fin H) ≃ Fin (2 * H) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] theorem localEquiv_left (H : ℕ) (i : Fin H) :
    localEquiv H (Sum.inl i) = leftIndex i := by apply Fin.ext; rfl

@[simp] theorem localEquiv_right (H : ℕ) (i : Fin H) :
    localEquiv H (Sum.inr i) = rightIndex i := by
  apply Fin.ext
  simp [localEquiv, rightIndex, Nat.add_comm]

def physicalEquiv (m : ℕ) : Block m × Local m ≃
    Fin (groupCount (m + 2)) :=
  (Equiv.prodCongr (blockEquiv m) (localEquiv (m + 2))).trans finProdFinEquiv

theorem physicalEquiv_apply (m : ℕ) (b : Block m) (j : Local m) :
    physicalEquiv m (b, j) = finProdFinEquiv (blockEquiv m b, localEquiv (m + 2) j) := rfl

noncomputable def localD (m : ℕ) (i : Fin (m + 2)) : MvPolynomial (Local m) ℝ :=
  X (Sum.inl i) - X (Sum.inr i)

noncomputable def localN (m : ℕ) (i : Fin (m + 2)) : MvPolynomial (Local m) ℝ :=
  C 2 * ((∑ j : Local m, X j) + X (Sum.inl i))

noncomputable def localSource (m : ℕ) (c : ℝ) : MvPolynomial (Local m) ℝ :=
  ∑ i : Fin (m + 2), localN m i *
    ∏ j ∈ Finset.univ.erase i, (C c + localD m j)

noncomputable def reindexedPhysical (m : ℕ) : BlockPoly m (Local m) :=
  rename (physicalEquiv m).symm (RoPEGeneralPhysicalCoordinates.physical (m + 1))

theorem denominator_reindexed (m : ℕ) (q : Block m × Local m → ℝ) (i : Fin (m + 2)) :
    denominator i (q ∘ (physicalEquiv m).symm) = base (m + 2) +
      ∑ b : Block m, (q (b, Sum.inl i) - q (b, Sum.inr i)) := by
  change base (m + 2) + RoPEGeneralPhysicalCoordinates.denominatorDirection _ i = _
  rw [RoPEGeneralPhysicalCoordinates.denominatorDirection_blocks,
    ← (blockEquiv m).sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  have hl := (physicalEquiv m).symm_apply_apply (b, Sum.inl i)
  have hr := (physicalEquiv m).symm_apply_apply (b, Sum.inr i)
  simp only [physicalEquiv_apply, localEquiv_left, localEquiv_right] at hl hr
  simp only [Function.comp_apply, hl, hr]

theorem numerator_reindexed (m : ℕ) (q : Block m × Local m → ℝ) (i : Fin (m + 2)) :
    numerator i (q ∘ (physicalEquiv m).symm) =
      2 * ((∑ b : Block m, ∑ j : Local m, q (b, j)) + ∑ b : Block m, q (b, Sum.inl i)) := by
  rw [RoPEGeneralPhysicalCoordinates.numerator_blocks,
    ← (blockEquiv m).sum_comp, ← (blockEquiv m).sum_comp]
  congr 2
  · apply Finset.sum_congr rfl
    intro b _
    rw [← (localEquiv (m + 2)).sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    change q ((physicalEquiv m).symm (physicalEquiv m (b, j))) = q (b, j)
    rw [Equiv.symm_apply_apply]
  · apply Finset.sum_congr rfl
    intro b _
    have hl := (physicalEquiv m).symm_apply_apply (b, Sum.inl i)
    simp only [physicalEquiv_apply, localEquiv_left] at hl
    simp only [Function.comp_apply, hl]

theorem reindexedPhysical_eq_blockLift (m : ℕ) :
    reindexedPhysical m = blockLift m (localSource m (base (m + 2))) := by
  apply MvPolynomial.funext
  intro q
  rw [reindexedPhysical, eval_rename, RoPEGeneralPhysicalCoordinates.eval_physical]
  simp only [blockLift, RoPEGroupSymmetrization.eval_affine_substitution,
    blockSum, map_sum, eval_X, localSource, map_mul, map_prod, map_add, eval_C,
    localD, map_sub, localN]
  simp_rw [denominator_reindexed, numerator_reindexed]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · rw [Finset.sum_comm]
  · apply Finset.prod_congr rfl
    intro j _
    rw [Finset.sum_sub_distrib]

theorem localD_totalDegree (m : ℕ) (i : Fin (m + 2)) : (localD m i).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans (by simp)

theorem localN_totalDegree (m : ℕ) (i : Fin (m + 2)) : (localN m i).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro j _
    simp
  · simp

/-- The source's constant denominator offsets affect only degrees below H. -/
theorem localSource_sub_zero_degree (m : ℕ) (c : ℝ) :
    (localSource m c - localSource m 0).totalDegree ≤ m + 1 := by
  have hb := AffineProductTopDegree.numerator_products_shift_sub_degree
    (H := m + 2) (by omega) (fun _ ↦ c) (localN m) (localD m)
    (localN_totalDegree m) (localD_totalDegree m)
  simpa only [localSource, map_zero, zero_add, show m + 2 - 1 = m + 1 by omega] using hb


theorem blockLift_totalDegree_le (m : ℕ) (P : MvPolynomial (Local m) ℝ) :
    (blockLift m P).totalDegree ≤ P.totalDegree := by
  apply RoPEGroupSymmetrization.affine_substitution_degree
  intro i
  apply totalDegree_finsetSum_le
  intro b _
  simp

theorem reindexedPhysical_sub_homogeneous_degree (m : ℕ) :
    (reindexedPhysical m - blockLift m (localSource m 0)).totalDegree ≤ m + 1 := by
  rw [reindexedPhysical_eq_blockLift, ← map_sub]
  exact (blockLift_totalDegree_le m _).trans (localSource_sub_zero_degree m _)

/-- Every top coefficient of the actual source is given by its homogeneous
block lift; the constant denominator offsets have disappeared exactly. -/
theorem reindexedPhysical_top_coeff (m : ℕ) (e : (Block m × Local m) →₀ ℕ)
    (he : e.sum (fun _ k ↦ k) = m + 2) :
    (reindexedPhysical m).coeff e = (blockLift m (localSource m 0)).coeff e := by
  have hz : (reindexedPhysical m - blockLift m (localSource m 0)).coeff e = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    have hd := reindexedPhysical_sub_homogeneous_degree m
    change (reindexedPhysical m - blockLift m (localSource m 0)).totalDegree <
      e.sum (fun _ k ↦ k)
    rw [he]
    omega
  simpa only [coeff_sub, sub_eq_zero] using hz

noncomputable def localCoordinateEquiv (m : ℕ) : (Local m → ℝ) ≃ₗ[ℝ] (Local m → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin (m + 2)) (Fin (m + 2)) ℝ ℝ).trans
    ((RoPEGeneralCoordinates.coordinateEquiv (m + 2)).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin (m + 2)) (Fin (m + 2)) ℝ ℝ).symm)

noncomputable def localSubstitution (m : ℕ) :=
  AffineCoordinateEquivalence.substitutionEquiv (localCoordinateEquiv m) 0

theorem localCoordinateEquiv_left (m : ℕ) (x : Local m → ℝ) (i : Fin (m + 2)) :
    localCoordinateEquiv m x (Sum.inl i) = x (Sum.inl i) - x (Sum.inr i) := rfl

theorem localCoordinateEquiv_right (m : ℕ) (x : Local m → ℝ) (i : Fin (m + 2)) :
    localCoordinateEquiv m x (Sum.inr i) = 2 * ((∑ j, x j) + x (Sum.inl i)) := by
  change 2 * ((∑ j, x (Sum.inl j)) + (∑ j, x (Sum.inr j)) + x (Sum.inl i)) = _
  rw [Fintype.sum_sum_type]

theorem localSource_zero_eq_substitution (m : ℕ) :
    localSource m 0 = localSubstitution m (RoPEGeneralDerivative.source (m + 2)) := by
  apply MvPolynomial.funext
  intro x
  rw [localSubstitution, AffineCoordinateEquivalence.eval_substitutionEquiv, add_zero]
  simp only [localSource, map_sum, map_mul, map_prod, map_add, eval_C, map_zero, zero_add,
    localN, localD, map_sub, eval_X, RoPEGeneralDerivative.source,
    RoPEGeneralDerivative.denomProduct, RoPEGeneralDerivative.N, RoPEGeneralDerivative.D,
    localCoordinateEquiv_left, localCoordinateEquiv_right]

end HeadComplexity.RoPEGeneralPhysicalBlocks
