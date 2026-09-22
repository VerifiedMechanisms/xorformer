import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Polynomial.OrderedSignChanges
import Mathlib.Data.Finset.Sort
import HeadComplexity.Results.DummyVariables
import HeadComplexity.Results.AffineSlab
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.StructuralInvariances

set_option linter.style.header false

/-!
# Sign changes along an arbitrary affine statistic

This module orders the finite image of an arbitrary affine statistic, builds
the corresponding univariate sign polynomial, and compiles it through the
affine-free support bound.  It also proves the exact zero-, one-, and
two-change regimes.  Mixed signs in the affine coefficients are allowed.
-/

namespace HeadComplexity

open Finset Polynomial MvPolynomial
open scoped BigOperators

variable {n K : ℕ}

private noncomputable def affinePoly (c : ℝ) (cs : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C c + ∑ i, MvPolynomial.C (cs i) * MvPolynomial.X i

private theorem affinePoly_totalDegree_le (c : ℝ) (cs : Fin n → ℝ) :
    (affinePoly c cs).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  rw [max_le_iff]
  constructor
  · simp
  · apply totalDegree_finsetSum_le
    intro i hi
    exact (totalDegree_mul _ _).trans (by simp)

private theorem affinePoly_eval (c : ℝ) (cs : Fin n → ℝ)
    (bits : Fin n → Bool) :
    eval (cubePoint bits) (affinePoly c cs) = affineValue c cs bits := by
  simp [affinePoly, affineValue, cubePoint]

private noncomputable def polynomialInAffine
    (P : ℝ[X]) (c : ℝ) (cs : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  P.eval₂ C (affinePoly c cs)

private theorem polynomialInAffine_totalDegree_le
    (P : ℝ[X]) (c : ℝ) (cs : Fin n → ℝ) :
    (polynomialInAffine P c cs).totalDegree ≤ P.natDegree := by
  rw [polynomialInAffine, Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro i hi
  rw [Finset.mem_range] at hi
  calc
    (MvPolynomial.C (P.coeff i) * affinePoly c cs ^ i).totalDegree ≤
        (MvPolynomial.C (P.coeff i)).totalDegree +
          (affinePoly c cs ^ i).totalDegree :=
      totalDegree_mul _ _
    _ ≤ 0 + i * (affinePoly c cs).totalDegree := by
      rw [totalDegree_C]
      exact Nat.add_le_add_left (totalDegree_pow (affinePoly c cs) i) 0
    _ ≤ P.natDegree := by
      have hL := affinePoly_totalDegree_le c cs
      simp only [zero_add]
      calc
        i * (affinePoly c cs).totalDegree ≤ i * 1 :=
          Nat.mul_le_mul_left i hL
        _ ≤ P.natDegree := by simpa using Nat.le_of_lt_succ hi

private theorem polynomialInAffine_eval
    (P : ℝ[X]) (c : ℝ) (cs : Fin n → ℝ) (bits : Fin n → Bool) :
    eval (cubePoint bits) (polynomialInAffine P c cs) =
      P.eval (affineValue c cs bits) := by
  rw [polynomialInAffine, Polynomial.hom_eval₂]
  rw [affinePoly_eval]
  have hcomp : (MvPolynomial.eval (cubePoint bits)).comp MvPolynomial.C =
      RingHom.id ℝ := by
    ext x
    simp
  rw [hcomp]
  exact Polynomial.eval₂_at_apply (RingHom.id ℝ) _

theorem thresholdDegLE_of_univariate_affine
    (c : ℝ) (cs : Fin n → ℝ) (f : (Fin n → Bool) → Bool)
    (h : UnivariateThresholdDegLE (affineValue c cs) f K) :
    ThresholdDegLE f K := by
  obtain ⟨P, hPdeg, hPsign⟩ := h
  refine ⟨polynomialInAffine P c cs,
    (polynomialInAffine_totalDegree_le P c cs).trans hPdeg, ?_⟩
  intro bits
  rw [polynomialInAffine_eval]
  exact hPsign bits

noncomputable def affineSupport (cs : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ cs i ≠ 0

noncomputable def affineSupportEmbedding (cs : Fin n → ℝ) :
    Fin (affineSupport cs).card ↪ Fin n where
  toFun j := ((affineSupport cs).equivFin.symm j).1
  inj' := by
    intro i j hij
    apply (affineSupport cs).equivFin.symm.injective
    apply Subtype.ext
    exact hij

theorem affineSupportEmbedding_mem (cs : Fin n → ℝ)
    (j : Fin (affineSupport cs).card) :
    affineSupportEmbedding cs j ∈ affineSupport cs :=
  ((affineSupport cs).equivFin.symm j).2

theorem exists_affineSupportEmbedding_eq (cs : Fin n → ℝ) {i : Fin n}
    (hi : i ∈ affineSupport cs) :
    ∃ j, affineSupportEmbedding cs j = i := by
  let si : {i // i ∈ affineSupport cs} := ⟨i, hi⟩
  refine ⟨(affineSupport cs).equivFin si, ?_⟩
  exact congrArg Subtype.val ((affineSupport cs).equivFin.symm_apply_apply si)

theorem affineValue_support_retraction (c : ℝ) (cs : Fin n → ℝ)
    (bits : Fin n → Bool) :
    affineValue c cs
        ((embeddingFace (affineSupportEmbedding cs)).apply
          (pullBitsAlong (affineSupportEmbedding cs) bits)) =
      affineValue c cs bits := by
  unfold affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hisupp : i ∈ affineSupport cs
  · obtain ⟨j, hj⟩ := exists_affineSupportEmbedding_eq cs hisupp
    subst i
    have hbit :
        (embeddingFace (affineSupportEmbedding cs)).apply
            (pullBitsAlong (affineSupportEmbedding cs) bits)
            (affineSupportEmbedding cs j) =
          bits (affineSupportEmbedding cs j) := by
      change (embeddingFace (affineSupportEmbedding cs)).apply
          (pullBitsAlong (affineSupportEmbedding cs) bits)
          ((embeddingFace (affineSupportEmbedding cs)).free j) = _
      rw [CoordFace.apply_free]
      rfl
    rw [hbit]
  · have hcs : cs i = 0 := by
      simpa [affineSupport] using hisupp
    simp [hcs]

theorem affineValue_embeddingFace_support (c : ℝ) (cs : Fin n → ℝ)
    (bits : Fin (affineSupport cs).card → Bool) :
    affineValue c cs
        ((embeddingFace (affineSupportEmbedding cs)).apply bits) =
      affineValue c (fun j ↦ cs (affineSupportEmbedding cs j)) bits := by
  unfold affineValue
  rw [(embeddingFace (affineSupportEmbedding cs)).sum_eq_free_add_fixed]
  have hfree :
      (∑ j, cs ((embeddingFace (affineSupportEmbedding cs)).free j) *
          boolToReal
            ((embeddingFace (affineSupportEmbedding cs)).apply bits
              ((embeddingFace (affineSupportEmbedding cs)).free j))) =
        ∑ j, cs (affineSupportEmbedding cs j) * boolToReal (bits j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [CoordFace.apply_free]
    rfl
  rw [hfree]
  have hfixed :
      (∑ j ∈ (embeddingFace (affineSupportEmbedding cs)).fixedSet,
          cs j * boolToReal
            ((embeddingFace (affineSupportEmbedding cs)).apply bits j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjnot : j ∉ affineSupport cs := by
      intro hjsupp
      obtain ⟨i, hi⟩ := exists_affineSupportEmbedding_eq cs hjsupp
      have hjfree : j ∈ (embeddingFace (affineSupportEmbedding cs)).freeSet := by
        rw [CoordFace.mem_freeSet]
        exact ⟨i, hi⟩
      exact (Finset.mem_sdiff.mp hj).2 hjfree
    have hcs : cs j = 0 := by
      simpa [affineSupport] using hjnot
    simp [hcs]
  rw [hfixed]
  ring

structure AffineStatisticProfile (c : ℝ) (cs : Fin n → ℝ)
    (f : (Fin n → Bool) → Bool) where
  steps : ℕ
  node : Fin (steps + 1) → ℝ
  node_strictMono : StrictMono node
  label : Fin (steps + 1) → Bool
  realized : ∀ i, ∃ bits, node i = affineValue c cs bits
  covers : ∀ bits, ∃ i, node i = affineValue c cs bits
  agrees : ∀ bits i, node i = affineValue c cs bits → f bits = label i

namespace AffineStatisticProfile

variable {c : ℝ} {cs : Fin n → ℝ} {f : (Fin n → Bool) → Bool}

def profile (C : AffineStatisticProfile c cs f) : ℕ → Bool := fun k ↦
  if hk : k ≤ C.steps then C.label (orderedNodeIndex C.steps k hk) else false

@[simp] theorem profile_at (C : AffineStatisticProfile c cs f)
    (i : Fin (C.steps + 1)) : C.profile i = C.label i := by
  rw [profile, dif_pos (Nat.lt_succ_iff.mp i.isLt)]
  congr

def alternations (C : AffineStatisticProfile c cs f) : ℕ :=
  signChanges C.steps C.profile

theorem univariateThresholdDegLE (C : AffineStatisticProfile c cs f) :
    UnivariateThresholdDegLE (affineValue c cs) f C.alternations := by
  obtain ⟨P, hPdeg, hPsign⟩ :=
    exists_ordered_sign_poly C.node C.node_strictMono C.profile
  refine ⟨P, hPdeg, ?_⟩
  intro bits
  obtain ⟨i, hi⟩ := C.covers bits
  have hik : (i : ℕ) ≤ C.steps := Nat.lt_succ_iff.mp i.isLt
  have hnode : C.node (orderedNodeIndex C.steps i hik) = C.node i := by
    congr
  have hagree := C.agrees bits i hi
  simpa [hnode, hi, C.profile_at i, hagree] using hPsign i hik

theorem alternations_le_of_univariateThresholdDegLE
    (C : AffineStatisticProfile c cs f)
    (h : UnivariateThresholdDegLE (affineValue c cs) f K) :
    C.alternations ≤ K := by
  obtain ⟨P, hPdeg, hPsign⟩ := h
  refine (ordered_signChanges_le_of_sign_iff P C.node C.node_strictMono C.profile ?_).trans hPdeg
  intro k hk
  let i : Fin (C.steps + 1) := orderedNodeIndex C.steps k hk
  obtain ⟨bits, hbits⟩ := C.realized i
  have hsign := hPsign bits
  rw [← hbits] at hsign
  have hagree := C.agrees bits i hbits
  rw [profile, dif_pos hk]
  simpa [i, hagree] using hsign

theorem eq_of_affineValue_eq (C : AffineStatisticProfile c cs f)
    {x y : Fin n → Bool}
    (hxy : affineValue c cs x = affineValue c cs y) : f x = f y := by
  obtain ⟨i, hi⟩ := C.covers x
  exact (C.agrees x i hi).trans
    (C.agrees y i (hi.trans hxy)).symm

noncomputable def activeCore (_C : AffineStatisticProfile c cs f) :
    (Fin (affineSupport cs).card → Bool) → Bool :=
  fun bits ↦ f ((embeddingFace (affineSupportEmbedding cs)).apply bits)

theorem factor_activeCore (C : AffineStatisticProfile c cs f) (bits : Fin n → Bool) :
    f bits = C.activeCore (pullBitsAlong (affineSupportEmbedding cs) bits) := by
  apply C.eq_of_affineValue_eq
  exact (affineValue_support_retraction c cs bits).symm

theorem activeCore_univariateThresholdDegLE
    (C : AffineStatisticProfile c cs f) :
    UnivariateThresholdDegLE
      (affineValue c (fun j ↦ cs (affineSupportEmbedding cs j)))
      C.activeCore C.alternations := by
  obtain ⟨P, hPdeg, hPsign⟩ := C.univariateThresholdDegLE
  refine ⟨P, hPdeg, ?_⟩
  intro bits
  have h := hPsign
    ((embeddingFace (affineSupportEmbedding cs)).apply bits)
  rw [affineValue_embeddingFace_support] at h
  exact h

theorem activeCore_thresholdDegLE (C : AffineStatisticProfile c cs f) :
    ThresholdDegLE C.activeCore C.alternations :=
  thresholdDegLE_of_univariate_affine c
    (fun j ↦ cs (affineSupportEmbedding cs j)) C.activeCore
    C.activeCore_univariateThresholdDegLE

theorem HStar_eq_activeCore (C : AffineStatisticProfile c cs f) :
    HStar n f = HStar (affineSupport cs).card C.activeCore := by
  apply HStar_juntaTransport (affineSupportEmbedding cs) C.activeCore f
  funext bits
  exact C.factor_activeCore bits

theorem HStar_le_support_sum (C : AffineStatisticProfile c cs f) :
    HStar n f ≤ 1 +
      ∑ r ∈ Finset.Icc 2 C.alternations,
        (affineSupport cs).card.choose r := by
  rw [C.HStar_eq_activeCore]
  exact HStar_le_one_add_sum_choose_of_ThresholdDegLE C.activeCore_thresholdDegLE

private theorem sum_choose_Icc_eq_min (k d : ℕ) :
    (∑ r ∈ Finset.Icc 2 d, k.choose r) =
      ∑ r ∈ Finset.Icc 2 (min d k), k.choose r := by
  by_cases hdk : d ≤ k
  · rw [min_eq_left hdk]
  · have hkd : k ≤ d := Nat.le_of_not_ge hdk
    rw [min_eq_right hkd]
    symm
    apply Finset.sum_subset
    · intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1, hr.2.trans hkd⟩
    · intro r hrd hrk
      simp only [Finset.mem_Icc, not_and] at hrd hrk
      apply Nat.choose_eq_zero_of_lt
      exact Nat.lt_of_not_ge (hrk hrd.1)

theorem HStar_le_support_sum_min (C : AffineStatisticProfile c cs f) :
    HStar n f ≤ 1 +
      ∑ r ∈ Finset.Icc 2 (min C.alternations (affineSupport cs).card),
        (affineSupport cs).card.choose r := by
  rw [← sum_choose_Icc_eq_min]
  exact C.HStar_le_support_sum

private theorem orderedNode_ne_cut
    (C : AffineStatisticProfile c cs f) (i : Fin (C.steps + 1))
    {t : ℕ} (ht : t < C.steps) : C.node i ≠ orderedCut C.node t := by
  have hi : (i : ℕ) ≤ C.steps := Nat.lt_succ_iff.mp i.isLt
  by_cases hit : (i : ℕ) ≤ t
  · have hmono : C.node i ≤ C.node (orderedNodeIndex C.steps t ht.le) := by
      apply C.node_strictMono.monotone
      change (i : ℕ) ≤ t
      exact hit
    exact ne_of_lt (hmono.trans_lt (orderedCut_between C.node C.node_strictMono ht).1)
  · have hti : t + 1 ≤ (i : ℕ) := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hit)
    have hmono : C.node (orderedNodeIndex C.steps (t + 1) ht) ≤ C.node i := by
      apply C.node_strictMono.monotone
      change t + 1 ≤ (i : ℕ)
      exact hti
    exact ne_of_gt ((orderedCut_between C.node C.node_strictMono ht).2.trans_le hmono)

/-- Exactly two changes along an affine statistic make either the true set or
the false set an affine slab. -/
theorem exists_affineSlab_or_complement_of_alternations_eq_two
    (C : AffineStatisticProfile c cs f) (hC : C.alternations = 2) :
    ∃ lo hi, lo ≤ hi ∧
      (f = affineSlab c cs lo hi ∨
        f = fun bits ↦ !(affineSlab c cs lo hi bits)) := by
  classical
  have hcard : (changeSet C.profile C.steps).card = 2 := by
    simpa [alternations, signChanges, changeSet] using hC
  obtain ⟨u, v, huv, huvset⟩ := Finset.card_eq_two.mp hcard
  have hordered : ∃ a b, a < b ∧ changeSet C.profile C.steps = {a, b} := by
    rcases lt_or_gt_of_ne huv with huvlt | hvult
    · exact ⟨u, v, huvlt, huvset⟩
    · exact ⟨v, u, hvult, huvset.trans (Finset.pair_comm u v)⟩
  obtain ⟨a, b, hablt, hset⟩ := hordered
  have hab : a ≠ b := ne_of_lt hablt
  have haS : a ∈ changeSet C.profile C.steps := by rw [hset]; simp
  have hbS : b ∈ changeSet C.profile C.steps := by rw [hset]; simp
  have ha : a < C.steps :=
    Finset.mem_range.mp (Finset.mem_filter.mp haS).1
  have hb : b < C.steps :=
    Finset.mem_range.mp (Finset.mem_filter.mp hbS).1
  change ∃ lo hi, lo ≤ hi ∧
    (f = affineSlab c cs lo hi ∨
      f = fun bits ↦ !(affineSlab c cs lo hi bits))
  · let lo := orderedCut C.node a
    let hi := orderedCut C.node b
    have hlohi : lo < hi := by
      have hmiddle :
          C.node (orderedNodeIndex C.steps (a + 1) ha) ≤
            C.node (orderedNodeIndex C.steps b hb.le) := by
        exact C.node_strictMono.monotone
          (by simpa [orderedNodeIndex] using hablt)
      exact ((orderedCut_between C.node C.node_strictMono ha).2.trans_le
        hmiddle).trans (orderedCut_between C.node C.node_strictMono hb).1
    refine ⟨lo, hi, hlohi.le, ?_⟩
    let last : Fin (C.steps + 1) := ⟨C.steps, Nat.lt_succ_self _⟩
    by_cases hlast : C.label last = false
    · left
      funext bits
      obtain ⟨i, hiBits⟩ := C.covers bits
      have hik : (i : ℕ) ≤ C.steps := Nat.lt_succ_iff.mp i.isLt
      let product : ℝ :=
        (C.node i - lo) * (C.node i - hi)
      have hprodform :
          (∏ t ∈ changeSet C.profile C.steps,
              (C.node i - orderedCut C.node t)) = product := by
        rw [hset]
        simp [product, lo, hi, hab]
      have hprodpos : 0 < product ↔ C.label i = C.label last := by
        have hs := ordered_prod_sign C.node C.node_strictMono C.profile i hik
        have heq := eq_Fn_iff_even_negCount C.profile C.steps hik
        rw [← heq] at hs
        have hidx : orderedNodeIndex C.steps (i : ℕ) hik = i := by
          apply Fin.ext
          rfl
        rw [hidx] at hs
        rw [hprodform] at hs
        have hlastprof : C.profile C.steps = C.label last := by
          unfold profile
          rw [dif_pos le_rfl]
          congr
        rw [hlastprof] at hs
        simpa [C.profile_at] using hs
      have hprodne : product ≠ 0 := by
        dsimp [product]
        exact mul_ne_zero
          (sub_ne_zero.mpr (C.orderedNode_ne_cut i ha))
          (sub_ne_zero.mpr (C.orderedNode_ne_cut i hb))
      have hslab : affineSlab c cs lo hi bits = true ↔ product < 0 := by
        rw [affineSlab, decide_eq_true_eq, ← hiBits]
        dsimp [product]
        constructor
        · rintro ⟨hlo, hhi⟩
          have hnel : C.node i ≠ lo := C.orderedNode_ne_cut i ha
          have hneh : C.node i ≠ hi := C.orderedNode_ne_cut i hb
          exact mul_neg_of_pos_of_neg
            (sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hnel)))
            (sub_neg.mpr (lt_of_le_of_ne hhi hneh))
        · intro hneg
          rcases mul_neg_iff.mp hneg with hgood | hbad
          · exact ⟨(sub_pos.mp hgood.1).le, (sub_neg.mp hgood.2).le⟩
          · exfalso
            have : hi < lo := (sub_pos.mp hbad.2).trans (sub_neg.mp hbad.1)
            exact (not_lt_of_ge hlohi.le) this
      apply Bool.eq_iff_iff.mpr
      rw [C.agrees bits i hiBits, hslab]
      have hneg : product < 0 ↔ ¬ 0 < product := by
        constructor
        · exact fun hp hn ↦ (not_lt_of_ge hp.le) hn
        · intro hn
          exact lt_of_le_of_ne (not_lt.mp hn) hprodne
      rw [hneg, hprodpos, hlast]
      simp
    · right
      have hlast' : C.label last = true := by
        cases h : C.label last <;> simp_all
      funext bits
      obtain ⟨i, hiBits⟩ := C.covers bits
      have hik : (i : ℕ) ≤ C.steps := Nat.lt_succ_iff.mp i.isLt
      let product : ℝ :=
        (C.node i - lo) * (C.node i - hi)
      have hprodform :
          (∏ t ∈ changeSet C.profile C.steps,
              (C.node i - orderedCut C.node t)) = product := by
        rw [hset]
        simp [product, lo, hi, hab]
      have hprodpos : 0 < product ↔ C.label i = C.label last := by
        have hs := ordered_prod_sign C.node C.node_strictMono C.profile i hik
        have heq := eq_Fn_iff_even_negCount C.profile C.steps hik
        rw [← heq] at hs
        have hidx : orderedNodeIndex C.steps (i : ℕ) hik = i := by
          apply Fin.ext
          rfl
        rw [hidx] at hs
        rw [hprodform] at hs
        have hlastprof : C.profile C.steps = C.label last := by
          unfold profile
          rw [dif_pos le_rfl]
          congr
        rw [hlastprof] at hs
        simpa [C.profile_at] using hs
      have hprodne : product ≠ 0 := by
        dsimp [product]
        exact mul_ne_zero
          (sub_ne_zero.mpr (C.orderedNode_ne_cut i ha))
          (sub_ne_zero.mpr (C.orderedNode_ne_cut i hb))
      have hslab : affineSlab c cs lo hi bits = true ↔ product < 0 := by
        rw [affineSlab, decide_eq_true_eq, ← hiBits]
        dsimp [product]
        constructor
        · rintro ⟨hlo, hhi⟩
          have hnel : C.node i ≠ lo := C.orderedNode_ne_cut i ha
          have hneh : C.node i ≠ hi := C.orderedNode_ne_cut i hb
          exact mul_neg_of_pos_of_neg
            (sub_pos.mpr (lt_of_le_of_ne hlo (Ne.symm hnel)))
            (sub_neg.mpr (lt_of_le_of_ne hhi hneh))
        · intro hneg
          rcases mul_neg_iff.mp hneg with hgood | hbad
          · exact ⟨(sub_pos.mp hgood.1).le, (sub_neg.mp hgood.2).le⟩
          · exfalso
            have : hi < lo := (sub_pos.mp hbad.2).trans (sub_neg.mp hbad.1)
            exact (not_lt_of_ge hlohi.le) this
      have hslabfalse : affineSlab c cs lo hi bits = false ↔ 0 < product := by
        rw [Bool.eq_false_iff]
        constructor
        · intro hn
          have hnneg : ¬ product < 0 := fun hneg ↦ hn (hslab.mpr hneg)
          exact lt_of_le_of_ne (not_lt.mp hnneg) (Ne.symm hprodne)
        · intro hp htrue
          exact (not_lt_of_ge hp.le) (hslab.mp htrue)
      apply Bool.eq_iff_iff.mpr
      rw [C.agrees bits i hiBits]
      have hright : C.label i = true ↔ affineSlab c cs lo hi bits = false := by
        rw [hslabfalse, hprodpos, hlast']
      simpa using hright

private theorem univariateThresholdDegLE_zero_of_constant
    (_C : AffineStatisticProfile c cs f) (hconst : ∀ x y, f x = f y) :
    UnivariateThresholdDegLE (affineValue c cs) f 0 := by
  refine ⟨Polynomial.C (if f default then (1 : ℝ) else -1), by simp, ?_⟩
  intro bits
  rw [hconst bits default]
  cases f default <;> norm_num

theorem nonconstant_of_alternations_ne_zero
    (C : AffineStatisticProfile c cs f) (hC : C.alternations ≠ 0) :
    ¬ (∀ x y, f x = f y) := by
  intro hconst
  have hle := C.alternations_le_of_univariateThresholdDegLE
    (C.univariateThresholdDegLE_zero_of_constant hconst)
  exact hC (Nat.eq_zero_of_le_zero hle)

/-- Zero affine-statistic sign changes give exact zero head complexity. -/
theorem HStar_eq_zero_of_affineStatistic_alternations_eq_zero
    (C : AffineStatisticProfile c cs f) (hC : C.alternations = 0) :
    HStar n f = 0 := by
  apply (HStar_eq_zero_iff f).2
  have htd : ThresholdDegLE f 0 := by
    simpa [hC] using
      (thresholdDegLE_of_univariate_affine c cs f C.univariateThresholdDegLE)
  exact constant_of_ThresholdDegLE_zero htd

/-- One affine-statistic sign change gives exact one-head complexity. -/
theorem HStar_eq_one_of_affineStatistic_alternations_eq_one
    (C : AffineStatisticProfile c cs f) (hC : C.alternations = 1) :
    HStar n f = 1 := by
  apply (HStar_eq_one_iff f).2
  have htd : ThresholdDegLE f 1 := by
    simpa [hC] using
      (thresholdDegLE_of_univariate_affine c cs f C.univariateThresholdDegLE)
  exact ⟨C.nonconstant_of_alternations_ne_zero (by omega),
    (ThresholdDegLE_one_iff_isLTF f).1 htd⟩

/-- Two affine-statistic sign changes require at most two heads, without a
sign restriction on the affine coefficients. -/
theorem HStar_le_two_of_affineStatistic_alternations_eq_two
    (C : AffineStatisticProfile c cs f) (hC : C.alternations = 2) :
    HStar n f ≤ 2 := by
  obtain ⟨lo, hi, hlohi, hslab | hcomplement⟩ :=
    C.exists_affineSlab_or_complement_of_alternations_eq_two hC
  · rw [hslab]
    exact HStar_affineSlab_le_two c cs lo hi hlohi
  · rw [hcomplement, HStar_complement]
    exact HStar_affineSlab_le_two c cs lo hi hlohi

/-- The two-change regime is exactly one head for an LTF and exactly two
heads otherwise. -/
theorem HStar_affineStatistic_alternations_eq_two_classification
    (C : AffineStatisticProfile c cs f) (hC : C.alternations = 2) :
    (isLTF f ∧ HStar n f = 1) ∨ (¬ isLTF f ∧ HStar n f = 2) := by
  have hnconst : ¬ (∀ x y, f x = f y) :=
    C.nonconstant_of_alternations_ne_zero (by omega)
  by_cases hltf : isLTF f
  · exact Or.inl ⟨hltf, (HStar_eq_one_iff f).2 ⟨hnconst, hltf⟩⟩
  · right
    refine ⟨hltf, ?_⟩
    have hle := C.HStar_le_two_of_affineStatistic_alternations_eq_two hC
    have hne0 : HStar n f ≠ 0 :=
      fun h0 ↦ hnconst ((HStar_eq_zero_iff f).1 h0)
    have hne1 : HStar n f ≠ 1 :=
      fun h1 ↦ hltf ((HStar_eq_one_iff f).1 h1).2
    omega

noncomputable def ofFunction (c : ℝ) (cs : Fin n → ℝ)
    (f : (Fin n → Bool) → Bool) (G : ℝ → Bool)
    (hf : ∀ bits, f bits = G (affineValue c cs bits)) :
    AffineStatisticProfile c cs f := by
  classical
  let S : Finset ℝ := Finset.univ.image (affineValue c cs)
  have hS : S.Nonempty :=
    ⟨affineValue c cs (fun _ ↦ false),
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hcard : S.card - 1 + 1 = S.card :=
    Nat.sub_add_cancel (Finset.card_pos.mpr hS)
  let e : Fin (S.card - 1 + 1) ≃o Fin S.card := Fin.castOrderIso hcard
  let nodes : Fin (S.card - 1 + 1) → ℝ :=
    fun i ↦ S.orderEmbOfFin rfl (e i)
  exact
    { steps := S.card - 1
      node := nodes
      node_strictMono := (S.orderEmbOfFin rfl).strictMono.comp e.strictMono
      label := fun i ↦ G (nodes i)
      realized := by
        intro i
        have hiS : nodes i ∈ S := S.orderEmbOfFin_mem rfl (e i)
        change nodes i ∈ Finset.univ.image (affineValue c cs) at hiS
        rw [Finset.mem_image] at hiS
        obtain ⟨bits, -, hbits⟩ := hiS
        exact ⟨bits, hbits.symm⟩
      covers := by
        intro bits
        have hmem : affineValue c cs bits ∈ S :=
          Finset.mem_image_of_mem _ (Finset.mem_univ bits)
        let j : Fin S.card :=
          (S.orderIsoOfFin rfl).symm ⟨affineValue c cs bits, hmem⟩
        refine ⟨e.symm j, ?_⟩
        change S.orderEmbOfFin rfl (e (e.symm j)) = affineValue c cs bits
        rw [e.apply_symm_apply]
        exact congrArg Subtype.val
          ((S.orderIsoOfFin rfl).apply_symm_apply
            ⟨affineValue c cs bits, hmem⟩)
      agrees := by
        intro bits i hi
        rw [hf bits, ← hi] }

/-- The ordered-image sign-change count for a displayed factorization through
an affine statistic. -/
noncomputable def signChangesOfFunction (c : ℝ) (cs : Fin n → ℝ)
    (f : (Fin n → Bool) → Bool) (G : ℝ → Bool)
    (hf : ∀ bits, f bits = G (affineValue c cs bits)) : ℕ :=
  (ofFunction c cs f G hf).alternations

/-- **Affine-statistic sign-change theorem.**  The first three regimes are
exact, up to the universal one-head LTF test in the two-change case.  For
three or more changes, the affine-free support compiler gives the stated
orientation-free bound in terms of the active-coordinate count. -/
theorem signChange_four_cases (C : AffineStatisticProfile c cs f) :
    (C.alternations = 0 → HStar n f = 0) ∧
      (C.alternations = 1 → HStar n f = 1) ∧
      (C.alternations = 2 →
        ((isLTF f ∧ HStar n f = 1) ∨
          (¬ isLTF f ∧ HStar n f = 2))) ∧
      (3 ≤ C.alternations →
        HStar n f ≤ 1 +
          ∑ r ∈ Finset.Icc 2
              (min C.alternations (affineSupport cs).card),
            (affineSupport cs).card.choose r) := by
  exact ⟨C.HStar_eq_zero_of_affineStatistic_alternations_eq_zero,
    C.HStar_eq_one_of_affineStatistic_alternations_eq_one,
    C.HStar_affineStatistic_alternations_eq_two_classification,
    fun _ ↦ C.HStar_le_support_sum_min⟩

end AffineStatisticProfile

end HeadComplexity
