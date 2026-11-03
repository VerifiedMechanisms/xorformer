import HeadComplexity.Results.ThresholdDegreeSpan
import HeadComplexity.Results.UniversalNeighborhoodBound

set_option linter.style.header false

/-!
# Fixed-denominator universal interpolation width

The interpolation width bounds numeric interpolation of all cube functions,
which is stronger than separately computing all Boolean truth tables.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

theorem exists_clearedSpanCertificate (n : ℕ) : ∃ H, Nonempty (ClearedSpanCertificate n H) := by
  classical
  by_cases hn : 0 < n
  · let i : Fin n := ⟨0, hn⟩
    let cover : OpenNeighborhoodCover n (2 ^ n) := {
      center := cubeBits
      covers := fun x ↦ ⟨cubeIndex (cubeFlip x i), i, by simp⟩ }
    exact ⟨2 ^ n, ⟨cover.toClearedSpanCertificate⟩⟩
  · have hnzero : n = 0 := by omega
    subst n
    refine ⟨0, ⟨{
      denConst := Fin.elim0
      denCoeff := Fin.elim0
      denConst_pos := fun h ↦ Fin.elim0 h
      denCoeff_pos := fun h ↦ Fin.elim0 h
      spans := ?_ }⟩⟩
    intro target
    refine ⟨target (fun i ↦ Fin.elim0 i), Fin.elim0, Fin.elim0, fun bits ↦ ?_⟩
    change target bits = target (fun i ↦ Fin.elim0 i) * 1 + 0
    rw [mul_one, add_zero]
    congr
    funext i
    exact Fin.elim0 i

noncomputable def fixedDenominatorWidth (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_clearedSpanCertificate n)

theorem fixedDenominatorWidth_spec (n : ℕ) :
    Nonempty (ClearedSpanCertificate n (fixedDenominatorWidth n)) := by
  classical
  exact Nat.find_spec (exists_clearedSpanCertificate n)

theorem fixedDenominatorWidth_le {n H : ℕ} (C : ClearedSpanCertificate n H) :
    fixedDenominatorWidth n ≤ H := by
  classical
  exact Nat.find_min' (exists_clearedSpanCertificate n) ⟨C⟩

theorem HStar_le_fixedDenominatorWidth {n : ℕ} (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ fixedDenominatorWidth n :=
  (Classical.choice (fixedDenominatorWidth_spec n)).HStar_le f

/-- The shared constant leaves only `n` additional numerator coordinates per head. -/
theorem fixedDenominatorWidth_dimension (n : ℕ) :
    2 ^ n ≤ 1 + n * fixedDenominatorWidth n := by
  classical
  let C := Classical.choice (fixedDenominatorWidth_spec n)
  have hd :=
    (DegreeClearedSpanCertificate.ofClearedSpanCertificate (d := n) C).dimension_obstruction
  rw [← card_lowDegreeMonomialIndex] at hd
  have hc : Fintype.card (LowDegreeMonomialIndex n n) = 2 ^ n := by
    rw [Fintype.card_subtype]
    have hf : ((Finset.univ : Finset (Finset (Fin n))).filter fun S ↦ S.card ≤ n) =
        Finset.univ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      simpa using Finset.card_le_univ S
    rw [hf]
    simp
  rwa [hc] at hd

theorem SyndromeCover.width_mul_le {n : ℕ} {S : Type*} [AddCommGroup S]
    [Fintype S] (C : SyndromeCover n S) :
    fixedDenominatorWidth n * Fintype.card S ≤ C.targets.card * 2 ^ n := by
  classical
  rw [← C.centers_card_mul]
  exact Nat.mul_le_mul_right _
    (fixedDenominatorWidth_le C.toOpenNeighborhoodCover.toClearedSpanCertificate)

theorem fixedDenominatorWidth_mul_pow_le_singleKernel {n k : ℕ} (hn : 2 ^ k ≤ n) :
    fixedDenominatorWidth n * 2 ^ k ≤ 2 ^ n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ((singleKernelRecipe k).toSyndromeCover.extend extra).width_mul_le
  simpa [BinaryVector, ZMod.card, SyndromeCover.extend, SyndromeRecipe.toSyndromeCover,
    singleKernelRecipe] using h

theorem fixedDenominatorWidth_mul_pow_le_syndrome12 {n s : ℕ} (hn : 12 * 2 ^ s ≤ n) :
    fixedDenominatorWidth n * 2 ^ (6 + s) ≤ 7 * 2 ^ n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ((syndromeRecipe12.lift (by decide) s).extend extra).width_mul_le
  change fixedDenominatorWidth _ * Fintype.card (BinaryVector 6 × BinaryVector s) ≤
    (syndromeRecipe12.lift (by decide) s).targets.card * _ at h
  simpa [BinaryVector, ZMod.card, pow_add] using h

theorem fixedDenominatorWidth_mul_pow_le_syndrome13 {n s : ℕ} (hn : 13 * 2 ^ s ≤ n) :
    fixedDenominatorWidth n * 2 ^ (7 + s) ≤ 12 * 2 ^ n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ((syndromeRecipe13.lift (by decide) s).extend extra).width_mul_le
  change fixedDenominatorWidth _ * Fintype.card (BinaryVector 7 × BinaryVector s) ≤
    (syndromeRecipe13.lift (by decide) s).targets.card * _ at h
  simpa [BinaryVector, ZMod.card, pow_add] using h

theorem fixedDenominatorWidth_real_lt_three_halves {n : ℕ} (hn : 8 ≤ n) :
    (fixedDenominatorWidth n : ℝ) < 3 * (2 : ℝ) ^ n / (2 * n) := by
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  have h := two_mul_dimension_mul_cost_lt (heads := fixedDenominatorWidth n) hn
    (fun _ h ↦ fixedDenominatorWidth_mul_pow_le_singleKernel h)
    (fun _ h ↦ fixedDenominatorWidth_mul_pow_le_syndrome12 h)
    (fun _ h ↦ fixedDenominatorWidth_mul_pow_le_syndrome13 h)
  exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)

/-- At every power-of-two input dimension at least two, interpolation meets
the shared-constant dimension obstruction exactly. -/
theorem fixedDenominatorWidth_power_two (k : ℕ) (hk : 1 ≤ k) :
    fixedDenominatorWidth (2 ^ k) = 2 ^ (2 ^ k) / (2 ^ k) := by
  classical
  let C := (singleKernelRecipe k).toSyndromeCover
  let H := C.centers.card
  have hcard : H * 2 ^ k = 2 ^ (2 ^ k) := by
    simpa [H, C, SyndromeRecipe.toSyndromeCover, singleKernelRecipe, BinaryVector, ZMod.card]
      using C.centers_card_mul
  have hle : fixedDenominatorWidth (2 ^ k) ≤ H :=
    fixedDenominatorWidth_le C.toOpenNeighborhoodCover.toClearedSpanCertificate
  have hdim := fixedDenominatorWidth_dimension (2 ^ k)
  have hn : 2 ≤ 2 ^ k := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have heq : fixedDenominatorWidth (2 ^ k) = H := by
    apply Nat.le_antisymm hle
    by_contra! hlt
    have hm := Nat.mul_le_mul_left (2 ^ k) (show fixedDenominatorWidth (2 ^ k) + 1 ≤ H by omega)
    nlinarith
  rw [heq, ← hcard]
  exact (Nat.mul_div_cancel H (by positivity : 0 < 2 ^ k)).symm

end HeadComplexity
