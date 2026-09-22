import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.PositiveWeightedSignDegree
import HeadComplexity.Polynomial.FreshBit

set_option linter.style.header false

/-!
# Positive-statistic certificates with one raw bit

This module compiles a polynomial in one positive weighted statistic and one
fresh Boolean coordinate into positive-affine ratio atoms.  The tail slice has
degree at most `K`, while the difference between the two raw-bit slices has
degree strictly less than `K`.  These are exactly the reduced bidegree
conditions in theorem 138.
-/

namespace HeadComplexity

open Finset Polynomial
open scoped BigOperators

variable {m K : ℕ}

/-- A univariate polynomial is positive on true inputs and negative on false
inputs after evaluation through a statistic. -/
def StrictUnivariateSignRep {α : Type*} (P : ℝ[X])
    (t : α → ℝ) (f : α → Bool) : Prop :=
  ∀ x, (f x = true → 0 < P.eval (t x)) ∧
    (f x = false → P.eval (t x) < 0)

namespace StrictUnivariateSignRep

/-- Strict signs imply the classifier convention. -/
theorem signRepresents {α : Type*} {P : ℝ[X]} {t : α → ℝ} {f : α → Bool}
    (h : StrictUnivariateSignRep P t f) :
    ∀ x, (0 < P.eval (t x) ↔ f x = true) := by
  intro x
  cases hx : f x
  · simp only [Bool.false_eq_true, iff_false]
    exact not_lt_of_ge (le_of_lt ((h x).2 hx))
  · simp only [iff_true]
    exact (h x).1 hx

/-- Negating a strict sign polynomial represents the complemented labels. -/
theorem neg {α : Type*} {P : ℝ[X]} {t : α → ℝ} {f : α → Bool}
    (h : StrictUnivariateSignRep P t f) :
    StrictUnivariateSignRep (-P) t (fun x ↦ !(f x)) := by
  intro x
  constructor
  · intro hx
    cases hfx : f x
    · simpa using neg_pos.mpr ((h x).2 hfx)
    · simp [hfx] at hx
  · intro hx
    cases hfx : f x
    · simp [hfx] at hx
    · simpa using neg_neg_of_pos ((h x).1 hfx)

end StrictUnivariateSignRep

/-- A univariate sign certificate on a finite domain can be made strict on
both Boolean classes by a constant shift, without increasing degree. -/
theorem exists_strictUnivariateSignRep_of_UnivariateThresholdDegLE
    {α : Type*} [Finite α]
    {t : α → ℝ} {f : α → Bool} {K : ℕ}
    (h : UnivariateThresholdDegLE t f K) :
    ∃ P : ℝ[X], P.natDegree ≤ K ∧ StrictUnivariateSignRep P t f := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨P, hPdeg, hPsign⟩ := h
  let T : Finset α := Finset.univ.filter (fun x ↦ f x = true)
  obtain ⟨ε, hεpos, hεlt⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ∀ x, f x = true → ε < P.eval (t x) := by
    by_cases hTne : T.Nonempty
    · refine ⟨T.inf' hTne (fun x ↦ P.eval (t x)) / 2, ?_, ?_⟩
      · apply half_pos
        rw [Finset.lt_inf'_iff]
        intro x hx
        exact (hPsign x).mpr (Finset.mem_filter.mp hx).2
      · intro x hx
        have hxT : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
        have hle := Finset.inf'_le (fun x ↦ P.eval (t x)) hxT
        have hpos : 0 < P.eval (t x) := (hPsign x).mpr hx
        have hinfpos : 0 < T.inf' hTne (fun x ↦ P.eval (t x)) := by
          rw [Finset.lt_inf'_iff]
          intro y hy
          exact (hPsign y).mpr (Finset.mem_filter.mp hy).2
        linarith
    · refine ⟨1, one_pos, ?_⟩
      intro x hx
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
        (fun hxmem ↦ hTne ⟨x, hxmem⟩)
  refine ⟨P - C ε, ?_, ?_⟩
  · exact (natDegree_sub_le P (C ε)).trans
      (max_le hPdeg (by simp))
  · intro x
    have hev : (P - C ε).eval (t x) = P.eval (t x) - ε := by simp
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rw [hev]
      linarith [hεlt x hx]
    · have hnonpos : P.eval (t x) ≤ 0 := by
        by_contra hp
        push Not at hp
        have := (hPsign x).mp hp
        rw [hx] at this
        exact Bool.false_ne_true this
      rw [hev]
      linarith

/-- The partial-fraction identity with its polynomial part fixed to the top
coefficient. -/
theorem real_partial_fraction_coeff {K : ℕ} (P : ℝ[X]) (av : Fin K → ℝ)
    (hinj : Function.Injective av) (hdeg : P.natDegree ≤ K) :
    ∃ bv : Fin K → ℝ, ∀ k : ℝ,
      P.eval k = P.coeff K * (∏ h : Fin K, (k + av h)) +
        ∑ h : Fin K, bv h *
          (∏ j ∈ Finset.univ.erase h, (k + av j)) := by
  classical
  obtain ⟨A, bv, hpf⟩ := real_partial_fraction P av hinj hdeg
  let Q : ℝ[X] := ∏ h : Fin K, (X + C (av h))
  let L : Fin K → ℝ[X] := fun h ↦
    ∏ j ∈ Finset.univ.erase h, (X + C (av j))
  have hQmonic : Q.Monic :=
    monic_prod_of_monic _ _ (fun i _ ↦ monic_X_add_C _)
  have hQdeg : Q.natDegree = K := by
    dsimp [Q]
    rw [natDegree_prod _ _ (fun i _ ↦ (monic_X_add_C _).ne_zero)]
    simp
  have hLdeg : ∀ h, (L h).natDegree = K - 1 := by
    intro h
    dsimp [L]
    rw [natDegree_prod _ _ (fun i _ ↦ (monic_X_add_C _).ne_zero)]
    simp [Finset.card_erase_of_mem (Finset.mem_univ h)]
  have hpoly : P = C A * Q + ∑ h : Fin K, C (bv h) * L h := by
    apply Polynomial.funext
    intro k
    rw [eval_add, eval_mul, eval_C, eval_finsetSum]
    simp only [eval_mul, eval_C]
    have hQeval : Q.eval k = ∏ h : Fin K, (k + av h) := by
      dsimp [Q]
      rw [eval_prod]
      simp
    have hLeval : ∀ h, (L h).eval k =
        ∏ j ∈ Finset.univ.erase h, (k + av j) := by
      intro h
      dsimp [L]
      rw [eval_prod]
      simp
    rw [hQeval]
    simp_rw [hLeval]
    exact hpf k
  have hA : A = P.coeff K := by
    have hcoeff := congrArg (fun R : ℝ[X] ↦ R.coeff K) hpoly
    rw [coeff_add, coeff_C_mul] at hcoeff
    have hQc : Q.coeff K = 1 := by
      rw [← hQdeg]
      exact hQmonic.coeff_natDegree
    have hsumc : (∑ h : Fin K, C (bv h) * L h).coeff K = 0 := by
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro h _
      rw [coeff_C_mul]
      have hKpos : 0 < K := lt_of_le_of_lt (Nat.zero_le _) h.isLt
      have hdeglt : (L h).natDegree < K := by
        rw [hLdeg h]
        omega
      rw [coeff_eq_zero_of_natDegree_lt hdeglt, mul_zero]
    rw [hQc, mul_one, hsumc, add_zero] at hcoeff
    exact hcoeff.symm
  refine ⟨bv, fun k ↦ ?_⟩
  simpa [hA] using hpf k

/-- Put the full leading coefficient into one distinguished affine numerator.
The nonempty hypothesis is carried explicitly so this construction also has a
clean type at `K = 0`. -/
def leadingShare {K : ℕ} (hK : 0 < K) (A : ℝ) : Fin K → ℝ :=
  fun h ↦ if h = ⟨0, hK⟩ then A else 0

theorem sum_leadingShare {K : ℕ} (hK : 0 < K) (A : ℝ) :
    ∑ h : Fin K, leadingShare hK A h = A := by
  classical
  rw [Finset.sum_eq_single (⟨0, hK⟩ : Fin K)]
  · simp [leadingShare]
  · intro h _ hne
    simp [leadingShare, hne]
  · simp

/-- Degree-`K` univariate polynomials are spanned by affine numerators over
`K` distinct affine factors.  The coefficient of the variable is fixed by the
leading coefficient, which lets two slices share it. -/
theorem real_affineNumerator_span {K : ℕ} (hK : 0 < K)
    (P : ℝ[X]) (av : Fin K → ℝ) (hinj : Function.Injective av)
    (hdeg : P.natDegree ≤ K) :
    ∃ a : Fin K → ℝ, ∀ u : ℝ,
      P.eval u = ∑ h : Fin K,
        (a h + leadingShare hK (P.coeff K) h * u) *
          (∏ j ∈ Finset.univ.erase h, (u + av j)) := by
  classical
  obtain ⟨bv, hpf⟩ := real_partial_fraction_coeff P av hinj hdeg
  let μ : Fin K → ℝ := leadingShare hK (P.coeff K)
  let a : Fin K → ℝ := fun h ↦ bv h + μ h * av h
  refine ⟨a, fun u ↦ ?_⟩
  have hfactor : ∀ h : Fin K,
      (u + av h) * (∏ j ∈ Finset.univ.erase h, (u + av j)) =
        ∏ j : Fin K, (u + av j) := by
    intro h
    exact Finset.mul_prod_erase Finset.univ (fun j ↦ u + av j)
      (Finset.mem_univ h)
  calc
    P.eval u = P.coeff K * (∏ h : Fin K, (u + av h)) +
        ∑ h : Fin K, bv h *
          (∏ j ∈ Finset.univ.erase h, (u + av j)) := hpf u
    _ = (∑ h : Fin K, bv h *
          (∏ j ∈ Finset.univ.erase h, (u + av j))) +
        (∑ h : Fin K, μ h) * (∏ j : Fin K, (u + av j)) := by
          rw [show ∑ h : Fin K, μ h = P.coeff K by
            simpa [μ] using sum_leadingShare hK (P.coeff K)]
          ring
    _ = (∑ h : Fin K, bv h *
          (∏ j ∈ Finset.univ.erase h, (u + av j))) +
        ∑ h : Fin K, μ h * ((u + av h) *
          (∏ j ∈ Finset.univ.erase h, (u + av j))) := by
          rw [Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro h _
          rw [hfactor h]
    _ = ∑ h : Fin K,
          (bv h + μ h * (u + av h)) *
          (∏ j ∈ Finset.univ.erase h, (u + av j)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro h _
          ring
    _ = ∑ h : Fin K,
        (a h + leadingShare hK (P.coeff K) h * u) *
          (∏ j ∈ Finset.univ.erase h, (u + av j)) := by
          apply Finset.sum_congr rfl
          intro h _
          simp only [a, μ]
          ring

/-- Positive affine factors used by the raw-bit compiler. -/
noncomputable def rawBitShift (K : ℕ) (z : Bool) (h : Fin K) : ℝ :=
  1 + (h : ℕ) + 2 * (K : ℝ) * boolToReal z

theorem rawBitShift_injective (K : ℕ) (z : Bool) :
    Function.Injective (rawBitShift K z) := by
  intro h j heq
  simp only [rawBitShift] at heq
  have : (h : ℕ) = (j : ℕ) := by exact_mod_cast (by linarith : (h : ℝ) = (j : ℝ))
  exact Fin.ext this

/-- The two Boolean slices of a reduced raw-bit polynomial share one common
family of affine-over-affine numerators. -/
theorem exists_rawBit_affineNumerator_span {K : ℕ} (hK : 0 < K)
    (P0 R : ℝ[X]) (hP0 : P0.natDegree ≤ K) (hR : R.natDegree < K) :
    ∃ a μ c : Fin K → ℝ, ∀ z : Bool, ∀ u : ℝ,
      P0.eval u + boolToReal z * R.eval u =
        ∑ h : Fin K, (a h + μ h * u + c h * boolToReal z) *
          (∏ j ∈ Finset.univ.erase h, (u + rawBitShift K z j)) := by
  classical
  let P1 := P0 + R
  have hP1 : P1.natDegree ≤ K := by
    exact (natDegree_add_le P0 R).trans
      (max_le hP0 (Nat.le_of_lt hR))
  have hcoeff : P1.coeff K = P0.coeff K := by
    dsimp [P1]
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hR, add_zero]
  obtain ⟨a0, ha0⟩ := real_affineNumerator_span hK P0
    (rawBitShift K false) (rawBitShift_injective K false) hP0
  obtain ⟨a1, ha1⟩ := real_affineNumerator_span hK P1
    (rawBitShift K true) (rawBitShift_injective K true) hP1
  let μ : Fin K → ℝ := leadingShare hK (P0.coeff K)
  let c : Fin K → ℝ := fun h ↦ a1 h - a0 h
  refine ⟨a0, μ, c, ?_⟩
  intro z u
  cases z
  · simpa [μ, c, boolToReal] using ha0 u
  · have hslice : P0.eval u + R.eval u = P1.eval u := by
      simp [P1]
    rw [show boolToReal true = 1 by rfl]
    simp only [one_mul, mul_one]
    rw [hslice]
    calc
      P1.eval u = ∑ h : Fin K,
          (a1 h + μ h * u) *
            (∏ j ∈ Finset.univ.erase h, (u + rawBitShift K true j)) := by
              simpa [μ, hcoeff] using ha1 u
      _ = ∑ h : Fin K,
          (a0 h + μ h * u + c h) *
            (∏ j ∈ Finset.univ.erase h, (u + rawBitShift K true j)) := by
              apply Finset.sum_congr rfl
              intro h _
              simp only [c]
              congr 1
              ring

/-- A reduced polynomial certificate through a positive tail statistic and one
fresh raw bit. -/
def PositiveStatisticRawBitDegLE
    (f : (Fin (m + 1) → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ lam : Fin m → ℝ, (∀ i, 0 < lam i) ∧
    ∃ P0 R : ℝ[X], P0.natDegree ≤ K ∧ R.natDegree < K ∧
      ∀ z y, (0 < P0.eval (wT lam y) + boolToReal z * R.eval (wT lam y) ↔
        f (consBit z y) = true)

/-- Weighted-statistic evaluation in the affine-value convention. -/
theorem wT_eq_sum_mul_boolToReal (lam : Fin m → ℝ) (y : Fin m → Bool) :
    wT lam y = ∑ i, lam i * boolToReal (y i) := by
  unfold wT
  apply Finset.sum_congr rfl
  intro i _
  cases y i <;> simp [boolToReal]

/-- Coefficients of the affine numerator produced by the span theorem. -/
def rawBitNumeratorCoeffs (lam : Fin m → ℝ) (μ c : ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.cases c (fun i ↦ μ * lam i)

/-- Strictly positive coefficients of every denominator in the compiler. -/
noncomputable def rawBitDenominatorCoeffs (lam : Fin m → ℝ) (K : ℕ) :
    Fin (m + 1) → ℝ :=
  Fin.cases (2 * (K : ℝ)) lam

theorem affineValue_rawBitNumerator (a μ c : ℝ) (lam : Fin m → ℝ)
    (z : Bool) (y : Fin m → Bool) :
    affineValue a (rawBitNumeratorCoeffs lam μ c) (consBit z y) =
      a + μ * wT lam y + c * boolToReal z := by
  unfold affineValue rawBitNumeratorCoeffs
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, consBit_zero, Fin.cases_succ, consBit_succ]
  have hsum : (∑ x, μ * lam x * boolToReal (y x)) =
      μ * ∑ x, lam x * boolToReal (y x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, ← wT_eq_sum_mul_boolToReal]
  ring

theorem affineValue_rawBitDenominator (lam : Fin m → ℝ) (K : ℕ)
    (h : Fin K) (z : Bool) (y : Fin m → Bool) :
    affineValue (1 + (h : ℕ)) (rawBitDenominatorCoeffs lam K)
        (consBit z y) =
      wT lam y + rawBitShift K z h := by
  unfold affineValue rawBitDenominatorCoeffs rawBitShift
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, consBit_zero, Fin.cases_succ, consBit_succ]
  rw [← wT_eq_sum_mul_boolToReal]
  ring

theorem rawBitDenominatorCoeffs_pos (lam : Fin m → ℝ) (K : ℕ)
    (hK : 0 < K) (hlam : ∀ i, 0 < lam i) :
    ∀ i, 0 < rawBitDenominatorCoeffs lam K i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [rawBitDenominatorCoeffs, Fin.cases_zero]
    positivity
  · simp only [rawBitDenominatorCoeffs, Fin.cases_succ]
    exact hlam _

namespace PositiveStatisticRawBitDegLE

/-- Theorem 138 compiler.  A reduced degree-`K` certificate in one positive
statistic and one raw bit is realized by `K` positive-affine ratio atoms. -/
theorem computable {f : (Fin (m + 1) → Bool) → Bool}
    (h : PositiveStatisticRawBitDegLE f K) (hK : 0 < K) :
    computableWithHeadsN (m + 1) K f := by
  classical
  obtain ⟨lam, hlam, P0, R, hP0, hR, hsign⟩ := h
  obtain ⟨a, μ, c, hspan⟩ :=
    exists_rawBit_affineNumerator_span hK P0 R hP0 hR
  let a₀ : Fin K → ℝ := a
  let ac : Fin K → Fin (m + 1) → ℝ :=
    fun h ↦ rawBitNumeratorCoeffs lam (μ h) (c h)
  let b₀ : Fin K → ℝ := fun h ↦ 1 + (h : ℕ)
  let bc : Fin K → Fin (m + 1) → ℝ :=
    fun _ ↦ rawBitDenominatorCoeffs lam K
  have hb₀ : ∀ h, 0 < b₀ h := by
    intro h
    dsimp [b₀]
    positivity
  have hbc : ∀ h i, 0 < bc h i := by
    intro h i
    exact rawBitDenominatorCoeffs_pos lam K hK hlam i
  apply computableWithHeadsN_of_positiveAffineRatios a₀ ac b₀ bc hb₀ hbc 0
  intro x
  let z := x 0
  let y := tailBits x
  let u := wT lam y
  have hx : x = consBit z y := by simp [z, y]
  rw [hx]
  have hnum : ∀ h : Fin K,
      affineValue (a₀ h) (ac h) (consBit z y) =
        a h + μ h * u + c h * boolToReal z := by
    intro h
    simpa [a₀, ac, u] using
      affineValue_rawBitNumerator (a h) (μ h) (c h) lam z y
  have hden : ∀ h : Fin K,
      affineValue (b₀ h) (bc h) (consBit z y) =
        u + rawBitShift K z h := by
    intro h
    simpa [b₀, bc, u] using affineValue_rawBitDenominator lam K h z y
  simp only [zero_add]
  simp_rw [hnum, hden]
  let N : Fin K → ℝ := fun h ↦ a h + μ h * u + c h * boolToReal z
  let D : Fin K → ℝ := fun h ↦ u + rawBitShift K z h
  have hDpos : ∀ h, 0 < D h := by
    intro h
    dsimp [D]
    rw [← hden h]
    exact affineValue_pos (b₀ h) (bc h) (hb₀ h) (hbc h) (consBit z y)
  have hQpos : 0 < ∏ h : Fin K, D h :=
    Finset.prod_pos (fun h _ ↦ hDpos h)
  have herase_ne : ∀ h : Fin K,
      (∏ j ∈ Finset.univ.erase h, D j) ≠ 0 :=
    fun h ↦ Finset.prod_ne_zero_iff.mpr
      (fun j _ ↦ (hDpos j).ne')
  have hQfac : ∀ h : Fin K,
      (∏ j : Fin K, D j) =
        D h * ∏ j ∈ Finset.univ.erase h, D j :=
    fun h ↦ (Finset.mul_prod_erase Finset.univ D
      (Finset.mem_univ h)).symm
  have hcommon : (∑ h : Fin K, N h / D h) =
      (∑ h : Fin K, N h * ∏ j ∈ Finset.univ.erase h, D j) /
        (∏ j : Fin K, D j) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h _
    rw [hQfac h, mul_div_mul_right _ _ (herase_ne h)]
  have hscore : (∑ h : Fin K, N h / D h) =
      (P0.eval u + boolToReal z * R.eval u) /
        (∏ j : Fin K, D j) := by
    rw [hcommon]
    congr 1
    simpa [N, D] using (hspan z u).symm
  rw [show (∑ h : Fin K,
      (a h + μ h * u + c h * boolToReal z) /
        (u + rawBitShift K z h)) = ∑ h : Fin K, N h / D h by rfl]
  rw [hscore, div_pos_iff_of_pos_right hQpos]
  exact hsign z y

end PositiveStatisticRawBitDegLE

end HeadComplexity
