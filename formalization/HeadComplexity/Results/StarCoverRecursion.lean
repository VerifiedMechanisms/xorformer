import HeadComplexity.Results.BernoulliStarCover
import HeadComplexity.Results.UniversalSublinearUpperBound
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# Partial star covers and block recursion

The semidirect construction uses every second-block monomial above a selected
first-block center, and a smaller second-block cover above each first-block
repair. This discounts repairs by the density of the smaller cover.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace StarCoverRecursion

/-- Generic coordinate-set version of the existing monomial-star relation. -/
def Star {α : Type*} [DecidableEq α] (S T : Finset α) : Prop :=
  S = T ∨ ∃ i, i ∉ S ∧ insert i S = T

def Covers {α : Type*} [DecidableEq α] (C : Finset (Finset α)) : Prop :=
  ∀ T, ∃ S ∈ C, Star S T

private theorem star_disjSum_left {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S T : Finset α} (h : Star S T) (U : Finset β) :
    Star (S.disjSum U) (T.disjSum U) := by
  rcases h with rfl | ⟨i, hi, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨Sum.inl i, by simpa using hi, ?_⟩
    ext x
    cases x <;> simp

private theorem star_disjSum_right {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) {T U : Finset β} (h : Star T U) :
    Star (S.disjSum T) (S.disjSum U) := by
  rcases h with rfl | ⟨i, hi, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨Sum.inr i, by simpa using hi, ?_⟩
    ext x
    cases x <;> simp

/-- Relabeling coordinates transports a star cover without increasing size. -/
theorem exists_cover_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : Finset (Finset α)) (hC : Covers C) :
    ∃ D : Finset (Finset β), Covers D ∧ D.card ≤ C.card := by
  classical
  refine ⟨C.image (fun S ↦ S.image e), ?_, Finset.card_image_le⟩
  intro T
  obtain ⟨S, hS, hstar⟩ := hC (T.image e.symm)
  refine ⟨S.image e, Finset.mem_image.mpr ⟨S, hS, rfl⟩, ?_⟩
  have hmap : Star (S.image e) ((T.image e.symm).image e) := by
    rcases hstar with h | ⟨i, hi, h⟩
    · exact Or.inl (congrArg (fun S ↦ S.image e) h)
    · refine Or.inr ⟨e i, ?_, ?_⟩
      · simpa [e.injective.eq_iff] using hi
      · rw [← Finset.image_insert, h]
  simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
    Finset.image_id'] using hmap

/-- Semidirect cover construction and its exact elementary size estimate. -/
theorem exists_semidirect {α β : Type*} [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S T : Finset (Finset α)) (C : Finset (Finset β))
    (hpartial : ∀ x, x ∉ T → ∃ s ∈ S, Star s x) (hC : Covers C) :
    ∃ D : Finset (Finset (α ⊕ β)), Covers D ∧
      D.card ≤ S.card * 2 ^ Fintype.card β + T.card * C.card := by
  classical
  let productCenters := fun (A : Finset (Finset α)) (B : Finset (Finset β)) ↦
    (A.product B).image (fun p ↦ p.1.disjSum p.2)
  let D := productCenters S Finset.univ ∪ productCenters T C
  refine ⟨D, ?_, ?_⟩
  · intro U
    by_cases hleft : U.toLeft ∈ T
    · obtain ⟨c, hc, hstar⟩ := hC U.toRight
      refine ⟨U.toLeft.disjSum c, Finset.mem_union_right _ ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(U.toLeft, c),
          Finset.mem_product.mpr ⟨hleft, hc⟩, rfl⟩
      · simpa only [Finset.toLeft_disjSum_toRight] using star_disjSum_right U.toLeft hstar
    · obtain ⟨s, hs, hstar⟩ := hpartial U.toLeft hleft
      refine ⟨s.disjSum U.toRight, Finset.mem_union_left _ ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(s, U.toRight),
          Finset.mem_product.mpr ⟨hs, Finset.mem_univ _⟩, rfl⟩
      · simpa only [Finset.toLeft_disjSum_toRight] using star_disjSum_left hstar U.toRight
  · have hproduct : ∀ A B, (productCenters A B).card ≤ A.card * B.card := by
      intro A B
      exact Finset.card_image_le.trans (by simp)
    calc
      D.card ≤ (productCenters S Finset.univ).card + (productCenters T C).card :=
        Finset.card_union_le _ _
      _ ≤ S.card * (Finset.univ : Finset (Finset β)).card + T.card * C.card :=
        Nat.add_le_add (hproduct _ _) (hproduct _ _)
      _ = S.card * 2 ^ Fintype.card β + T.card * C.card := by simp

end StarCoverRecursion

private theorem exists_universalCoverSize (n : ℕ) :
    ∃ H, ∃ C : Finset (Finset (Fin n)), C.card = H ∧ StarCoverRecursion.Covers C :=
  ⟨Finset.univ.card, Finset.univ, rfl,
    fun T ↦ ⟨T, Finset.mem_univ T, Or.inl rfl⟩⟩

/-- Minimum size of a full upward monomial star cover. Constants are included
in this combinatorial invariant, while the attention compiler keeps free bias. -/
noncomputable def monomialStarCoverNumber (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_universalCoverSize n)

theorem monomialStarCoverNumber_spec (n : ℕ) :
    ∃ C : Finset (Finset (Fin n)), C.card = monomialStarCoverNumber n ∧
      StarCoverRecursion.Covers C := by
  classical
  exact Nat.find_spec (exists_universalCoverSize n)

theorem monomialStarCoverNumber_le_card {n : ℕ}
    (C : Finset (Finset (Fin n))) (hC : StarCoverRecursion.Covers C) :
    monomialStarCoverNumber n ≤ C.card := by
  classical
  exact Nat.find_min' (exists_universalCoverSize n) ⟨C, rfl, hC⟩

/-- Every full monomial star cover compiles to the actual attention model. -/
theorem HStar_le_monomialStarCoverNumber {n : ℕ}
    (f : (Fin n → Bool) → Bool) : HStar n f ≤ monomialStarCoverNumber n := by
  obtain ⟨C, hcard, hC⟩ := monomialStarCoverNumber_spec n
  obtain ⟨P, _, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f)
  have h := P.HStar_le_of_starCover f hP C (fun T _ ↦ hC T)
  rwa [hcard] at h

/-- The logarithmic alteration argument bounds the cover invariant itself,
so it is available as an induction base for sharper block recursions. -/
theorem monomialStarCoverNumber_real_le_logarithmic {n : ℕ} (hn : 2 ≤ n) :
    (monomialStarCoverNumber n : ℝ) ≤ logarithmicStarBudget n := by
  have hp := logarithmicStarRate_mem_Icc hn
  obtain ⟨C, hC, hcard⟩ := exists_universal_starCover_bernoulli
    n (logarithmicStarRate n) hp.1 hp.2
  have hmin := monomialStarCoverNumber_le_card C hC
  exact (by exact_mod_cast hmin : (monomialStarCoverNumber n : ℝ) ≤ C.card).trans
    (hcard.trans (bernoulliStarBudget_logarithmic_le hn))

/-- Taking all centers that omit one fixed coordinate covers the entire cube. -/
theorem monomialStarCoverNumber_le_half {n : ℕ} (hn : 0 < n) :
    monomialStarCoverNumber n ≤ 2 ^ (n - 1) := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let C := (Finset.univ.erase i : Finset (Fin n)).powerset
  have hC : StarCoverRecursion.Covers C := by
    intro T
    by_cases hi : i ∈ T
    · refine ⟨T.erase i, ?_, Or.inr ⟨i, Finset.notMem_erase i T,
        Finset.insert_erase hi⟩⟩
      apply Finset.mem_powerset.mpr
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
      exact hj.1
    · refine ⟨T, ?_, Or.inl rfl⟩
      apply Finset.mem_powerset.mpr
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun h ↦ hi (h ▸ hj), Finset.mem_univ j⟩
  have h := monomialStarCoverNumber_le_card C hC
  simpa [C] using h

/-- A partial first-block cover with repairs discounted by the density of
an optimal second-block cover gives the exact real-valued block recurrence. -/
theorem monomialStarCoverNumber_block_recurrence (n m : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hpone : p ≤ 1) :
    (monomialStarCoverNumber (n + m) : ℝ) ≤
      (2 : ℝ) ^ (n + m) * p +
        monomialStarCoverNumber m * (1 - p) * (2 - p) ^ n := by
  classical
  obtain ⟨C, hCcard, hC⟩ := monomialStarCoverNumber_spec m
  let δ : ℝ := C.card / (2 : ℝ) ^ m
  obtain ⟨S, T, hpartial, hbudget⟩ := FiniteBernoulliCover.exists_patch_card_le
    (monomialPredecessors (n := n)) p δ hp hpone
  have hpartial' : ∀ x, x ∉ T → ∃ s ∈ S, StarCoverRecursion.Star s x := by
    intro x hx
    obtain ⟨s, hs, hstar⟩ := hpartial x hx
    exact ⟨s, hs, (mem_monomialPredecessors_iff s x).mp hstar⟩
  obtain ⟨D, hD, hDcard⟩ := StarCoverRecursion.exists_semidirect S T C hpartial' hC
  obtain ⟨E, hE, hEcard⟩ := StarCoverRecursion.exists_cover_equiv
    (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)) D hD
  have hcard := (monomialStarCoverNumber_le_card E hE).trans (hEcard.trans hDcard)
  simp only [Fintype.card_fin] at hcard
  have hcardReal : (monomialStarCoverNumber (n + m) : ℝ) ≤
      (S.card : ℝ) * (2 : ℝ) ^ m + (T.card : ℝ) * C.card := by
    exact_mod_cast hcard
  have hsum (q : ℝ) : (∑ U : Finset (Fin n), q ^ U.card) = (1 + q) ^ n := by
    have h := Fintype.prod_add (fun _ : Fin n ↦ q) (fun _ ↦ (1 : ℝ))
    simpa [add_comm] using h.symm
  simp only [card_monomialPredecessors, pow_succ, Fintype.card_finset,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hbudget
  rw [← Finset.sum_mul, hsum] at hbudget
  have hplus : (1 : ℝ) + (1 - p) = 2 - p := by ring
  rw [hplus] at hbudget
  have hδ : (2 : ℝ) ^ m * δ = C.card := by
    dsimp [δ]
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (by positivity : (0 : ℝ) ≤ 2 ^ m)
  calc
    (monomialStarCoverNumber (n + m) : ℝ) ≤
        (2 : ℝ) ^ m * ((S.card : ℝ) + δ * T.card) := by
      rw [mul_add, ← mul_assoc, hδ]
      nlinarith [hcardReal]
    _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ n * p + δ * ((2 - p) ^ n * (1 - p))) :=
      hscaled
    _ = (2 : ℝ) ^ (n + m) * p +
        monomialStarCoverNumber m * (1 - p) * (2 - p) ^ n := by
      rw [mul_add]
      simp_rw [← mul_assoc]
      rw [hδ, hCcard, pow_add]
      ring

end HeadComplexity
