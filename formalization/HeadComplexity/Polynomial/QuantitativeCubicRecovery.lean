import HeadComplexity.Polynomial.SymmetricCubicRecovery
import HeadComplexity.Polynomial.QuantitativeCrossRecovery

set_option linter.style.header false

/-!
# Quantitative recovery of symmetric cubic tensors from squarefree entries

The tensor convention is the third derivative. Hence distinct entries equal
ordinary squarefree coefficients, while repeated entries include multiplicities.
-/

namespace HeadComplexity.QuantitativeCubicRecovery
noncomputable section
open scoped BigOperators Matrix
open SymmetricCubicRecovery QuantitativeCrossRecovery

variable {ι : Type*} [Fintype ι]

def CrossLower (T : ι → ι → ι → ℝ) (d : ℝ) : Prop :=
  ∀ i k, i ≠ k → ∃ a b : Fin 6 → ι,
    (∀ p, a p ≠ i ∧ a p ≠ k ∧ b p ≠ i ∧ b p ≠ k) ∧
    (∀ p q, a p ≠ b q) ∧ d ≤ |((slice T k).submatrix a b).det|

def secondErrorFactor (K : ℝ) : ℝ := 6000 * firstErrorFactor K * K + 2000000 * K ^ 2

theorem firstErrorFactor_nonneg (K : ℝ) (hK : 0 ≤ K) : 0 ≤ firstErrorFactor K := by
  unfold firstErrorFactor
  positivity

theorem secondErrorFactor_nonneg (K : ℝ) (hK : 0 ≤ K) : 0 ≤ secondErrorFactor K := by
  have hL := firstErrorFactor_nonneg K hK
  unfold secondErrorFactor
  positivity

theorem error_of_repeated_pair (T U : ι → ι → ι → ℝ) (d e : ℝ)
    (hd : 0 < d) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsmall : 4320 * (19 : ℝ) ^ 5 * e < d / 2)
    (hrT : ∀ k, (slice T k).rank ≤ 6) (hrU : ∀ k, (slice U k).rank ≤ 6)
    (hc : CrossLower T d)
    (hT : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → |T i j k| ≤ 18)
    (hsq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → |T i j k - U i j k| ≤ e)
    (i k : ι) (hik : i ≠ k) :
    |T i i k - U i i k| ≤ firstErrorFactor (inverseBound d) * e := by
  let K := inverseBound d
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseBound_ge_one d hd)
  obtain ⟨a, b, hav, hab, hdet⟩ := hc i k hik
  have hcross (p q) : |T (a p) (b q) k - U (a p) (b q) k| ≤ e :=
    hsq _ _ _ (hab p q) (hav p).2.1 (hav q).2.2.2
  have hcrossT (p q) : |T (a p) (b q) k| ≤ 18 :=
    hT _ _ _ (hab p q) (hav p).2.1 (hav q).2.2.2
  obtain ⟨hdetT, hdetU, hTI, hUI⟩ := cross_block_stability
    ((slice T k).submatrix a b) ((slice U k).submatrix a b) d e
    hd he he1 hcrossT hcross hdet hsmall
  have hrow (p) : |T i (b p) k - U i (b p) k| ≤ e :=
    hsq _ _ _ (hav p).2.2.1.symm hik (hav p).2.2.2
  have hcol (p) : |T (a p) i k - U (a p) i k| ≤ e :=
    hsq _ _ _ (hav p).1 (hav p).2.1 hik
  have hrowT (p) : |T i (b p) k| ≤ 18 :=
    hT _ _ _ (hav p).2.2.1.symm hik (hav p).2.2.2
  have hcolT (p) : |T (a p) i k| ≤ 18 :=
    hT _ _ _ (hav p).1 (hav p).2.1 hik
  have hrowU (p) : |U i (b p) k| ≤ 19 := by
    have ht : |U i (b p) k| ≤ |T i (b p) k| + |T i (b p) k - U i (b p) k| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le (U i (b p) k) (T i (b p) k) 0
    linarith [hrowT p, hrow p]
  have hcolU (p) : |U (a p) i k| ≤ 19 := by
    have ht : |U (a p) i k| ≤ |T (a p) i k| + |T (a p) i k - U (a p) i k| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le (U (a p) i k) (T (a p) i k) 0
    linarith [hcolT p, hcol p]
  have hb := entry_error_bound (slice T k) (slice U k) a b (hrT k) (hrU k)
    hdetT hdetU i i 19 K e e (by norm_num) hK he he hTI hUI hcross
    (fun p ↦ (hrowT p).trans (by norm_num)) hrowU
    (fun p ↦ (hcolT p).trans (by norm_num)) hcolU hrow hcol
  exact hb.trans (first_stage_constant K e hK he)

theorem error_of_triple [Nontrivial ι] (T U : ι → ι → ι → ℝ) (d e : ℝ)
    (hd : 0 < d) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsmall : 4320 * (19 : ℝ) ^ 5 * e < d / 2)
    (hT : Symmetric T) (hU : Symmetric U)
    (hrT : ∀ k, (slice T k).rank ≤ 6) (hrU : ∀ k, (slice U k).rank ≤ 6)
    (hc : CrossLower T d)
    (hTsq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → |T i j k| ≤ 18)
    (hTrep : ∀ i k, i ≠ k → |T i i k| ≤ 36)
    (hsq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → |T i j k - U i j k| ≤ e)
    (hfirst : firstErrorFactor (inverseBound d) * e ≤ 1) (k : ι) :
    |T k k k - U k k k| ≤ secondErrorFactor (inverseBound d) * e := by
  let K := inverseBound d
  let L := firstErrorFactor K
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans (inverseBound_ge_one d hd)
  have hL : 0 ≤ L := firstErrorFactor_nonneg K hK
  have htwo := error_of_repeated_pair T U d e hd he he1 hsmall hrT hrU hc hTsq hsq
  obtain ⟨i, hik⟩ := exists_ne k
  obtain ⟨a, b, hav, hab, hdet⟩ := hc i k hik
  have hcross (p q) : |T (a p) (b q) k - U (a p) (b q) k| ≤ e :=
    hsq _ _ _ (hab p q) (hav p).2.1 (hav q).2.2.2
  have hcrossT (p q) : |T (a p) (b q) k| ≤ 18 :=
    hTsq _ _ _ (hab p q) (hav p).2.1 (hav q).2.2.2
  obtain ⟨hdetT, hdetU, hTI, hUI⟩ := cross_block_stability
    ((slice T k).submatrix a b) ((slice U k).submatrix a b) d e
    hd he he1 hcrossT hcross hdet hsmall
  have hrow (p) : |T k (b p) k - U k (b p) k| ≤ L * e := by
    rw [hT.2, hU.2]
    exact htwo k (b p) (hav p).2.2.2.symm
  have hcol (p) : |T (a p) k k - U (a p) k k| ≤ L * e := by
    rw [hT.1, hU.1, hT.2, hU.2]
    exact htwo k (a p) (hav p).2.1.symm
  have hrowT (p) : |T k (b p) k| ≤ 36 := by
    rw [hT.2]
    exact hTrep k (b p) (hav p).2.2.2.symm
  have hcolT (p) : |T (a p) k k| ≤ 36 := by
    rw [hT.1, hT.2]
    exact hTrep k (a p) (hav p).2.1.symm
  have hrowU (p) : |U k (b p) k| ≤ 38 := by
    have ht : |U k (b p) k| ≤ |T k (b p) k| + |T k (b p) k - U k (b p) k| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le (U k (b p) k) (T k (b p) k) 0
    linarith [hrowT p, hrow p]
  have hcolU (p) : |U (a p) k k| ≤ 38 := by
    have ht : |U (a p) k k| ≤ |T (a p) k k| + |T (a p) k k - U (a p) k k| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le (U (a p) k k) (T (a p) k k) 0
    linarith [hcolT p, hcol p]
  have hb := entry_error_bound (slice T k) (slice U k) a b (hrT k) (hrU k)
    hdetT hdetU k k 38 K (2 * L * e) e (by norm_num) hK (by positivity) he hTI hUI hcross
    (fun p ↦ (hrowT p).trans (by norm_num)) hrowU
    (fun p ↦ (hcolT p).trans (by norm_num)) hcolU
    (fun p ↦ (hrow p).trans (by nlinarith [mul_nonneg hL he]))
    (fun p ↦ (hcol p).trans (by nlinarith [mul_nonneg hL he]))
  exact hb.trans (second_stage_constant K L e hK hL he)

theorem factors_le_uniform (K : ℝ) (hK : 1 ≤ K) :
    1 ≤ 10 ^ 10 * K ^ 3 ∧ firstErrorFactor K ≤ 10 ^ 10 * K ^ 3 ∧
      secondErrorFactor K ≤ 10 ^ 10 * K ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hs : K ≤ K ^ 2 := by nlinarith
  have hc : K ^ 2 ≤ K ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
  unfold firstErrorFactor secondErrorFactor
  constructor
  · nlinarith
  constructor
  · nlinarith
  · unfold firstErrorFactor
    nlinarith

/-- The full quantitative squarefree-to-raw tensor recovery statement.
All competitor slices may use unrelated latent forms; only rank at most six
and the squarefree coefficient error are assumed. -/
theorem all_entries_error_bound [Nontrivial ι] (T U : ι → ι → ι → ℝ) (d e : ℝ)
    (hd : 0 < d) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsmall : 4320 * (19 : ℝ) ^ 5 * e < d / 2)
    (hT : Symmetric T) (hU : Symmetric U)
    (hrT : ∀ k, (slice T k).rank ≤ 6) (hrU : ∀ k, (slice U k).rank ≤ 6)
    (hc : CrossLower T d)
    (hTsq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → |T i j k| ≤ 18)
    (hTrep : ∀ i k, i ≠ k → |T i i k| ≤ 36)
    (hsq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → |T i j k - U i j k| ≤ e)
    (hfirst : firstErrorFactor (inverseBound d) * e ≤ 1) :
    ∀ i j k, |T i j k - U i j k| ≤ 10 ^ 10 * inverseBound d ^ 3 * e := by
  let K := inverseBound d
  obtain ⟨h1, hL, hC⟩ := factors_le_uniform K (inverseBound_ge_one d hd)
  have htwo (i k : ι) (hik : i ≠ k) :
      |T i i k - U i i k| ≤ 10 ^ 10 * K ^ 3 * e :=
    (error_of_repeated_pair T U d e hd he he1 hsmall hrT hrU hc hTsq hsq i k hik).trans
      (mul_le_mul_of_nonneg_right hL he)
  have hthree (k : ι) : |T k k k - U k k k| ≤ 10 ^ 10 * K ^ 3 * e :=
    (error_of_triple T U d e hd he he1 hsmall hT hU hrT hrU hc hTsq hTrep hsq hfirst k).trans
      (mul_le_mul_of_nonneg_right hC he)
  intro i j k
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      exact hthree i
    · exact htwo i k hik
  · by_cases hik : i = k
    · subst k
      rw [hT.2, hU.2]
      exact htwo i j hij
    · by_cases hjk : j = k
      · subst k
        rw [hT.1, hU.1, hT.2, hU.2]
        exact htwo j i (Ne.symm hij)
      · exact (hsq i j k hij hik hjk).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 he)

end
end HeadComplexity.QuantitativeCubicRecovery
