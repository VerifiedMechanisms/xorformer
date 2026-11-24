import HeadComplexity.Model.PureRoPERealization
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option linter.style.header false

/-!
# Standard-frequency rotary interpolation

A complex Vandermonde argument gives finite logit interpolation. We use `m`
distinct frequencies for `m` time positions; this sacrifices a factor of two
relative to the sharp real-rank argument but keeps the width finite and shared.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

private noncomputable def complexBlocks {m : ℕ} (v : Fin m → ℂ) : Vec (m * 2) :=
  WithLp.toLp 2 (fun j => if j.modNat = 0 then (v j.divNat).re else (v j.divNat).im)

private theorem blockRotation_complexBlocks {m : ℕ} (ω : Fin m → ℝ) (t : ℝ)
    (v : Fin m → ℂ) :
    blockRotation ω t (complexBlocks v) =
      complexBlocks (fun r => Complex.exp ((t * ω r : ℝ) * Complex.I) * v r) := by
  ext j
  simp [blockRotation, complexBlocks, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im, add_comm]

private theorem complexBlocks_inner_ones {m : ℕ} (v : Fin m → ℂ) :
    ⟪complexBlocks v, complexBlocks (fun _ => 1)⟫_ℝ = (∑ r, v r).re := by
  rw [PiLp.inner_apply]
  change (∑ j : Fin (m * 2), _) = _
  rw [← (finProdFinEquiv (m := m) (n := 2)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp [complexBlocks, Fin.sum_univ_two]

/-- Distinct complex nodes give arbitrary values at the consecutive powers. -/
private theorem complex_vandermonde_interpolation {m : ℕ} (z : Fin m → ℂ)
    (hz : Function.Injective z) (y : Fin m → ℂ) :
    ∃ a : Fin m → ℂ, ∀ j : Fin m, ∑ r, a r * z r ^ j.val = y j := by
  have hu : IsUnit (Matrix.vandermonde z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hz))
  obtain ⟨a, ha⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hu) y
  refine ⟨a, fun j => ?_⟩
  exact congrFun ha j

private theorem exp_nat_angle (ω : ℝ) (j : ℕ) :
    Complex.exp (((j : ℝ) * ω : ℝ) * Complex.I) =
      Complex.exp ((ω : ℂ) * Complex.I) ^ j := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Any sufficiently long list of distinct unit-circle nodes interpolates all
input and self logits at a single common query vector. -/
theorem frequencySchedule_interpolates_of_injective {n m : ℕ}
    (ω : Fin m → ℝ) (hn : n < m)
    (hz : Function.Injective (fun r => Complex.exp ((ω r : ℂ) * Complex.I))) :
    RotaryInterpolates (frequencySchedule (n := n) ω) := by
  classical
  let z (r : Fin m) := Complex.exp ((ω r : ℂ) * Complex.I)
  let q : Vec (m * 2) := complexBlocks (fun r =>
    Complex.exp (-((rotaryPosition (n := n) none * ω r : ℝ) * Complex.I)))
  have hq : frequencySchedule (n := n) ω none q = complexBlocks (fun _ => 1) := by
    dsimp only [frequencySchedule, q]
    rw [blockRotation_complexBlocks]
    congr 1
    funext r
    simp [Complex.exp_neg, Complex.exp_ne_zero]
  refine ⟨q, fun y => ?_⟩
  let yext (j : Fin m) : ℂ :=
    if h : j.val < n then (y (some ⟨j.val, h⟩) : ℂ) else (y none : ℂ)
  obtain ⟨a, ha⟩ := complex_vandermonde_interpolation z hz yext
  let k := complexBlocks (fun r => a r / z r)
  refine ⟨k, fun p => ?_⟩
  rw [hq]
  dsimp only [frequencySchedule, k]
  rw [blockRotation_complexBlocks, complexBlocks_inner_ones]
  let j : Fin m := match p with
    | some i => ⟨i.val, lt_trans i.isLt hn⟩
    | none => ⟨n, hn⟩
  have ht : rotaryPosition p = ((j.val + 1 : ℕ) : ℝ) := by
    cases p <;> simp [rotaryPosition, j]
  have he (r : Fin m) :
      Complex.exp ((rotaryPosition p * ω r : ℝ) * Complex.I) * (a r / z r) =
        a r * z r ^ j.val := by
    rw [ht, exp_nat_angle, pow_succ]
    dsimp [z]
    have hne := Complex.exp_ne_zero ((ω r : ℂ) * Complex.I)
    field_simp
  simp_rw [he]
  rw [ha]
  cases p with
  | some i => simp [yext, j, i.isLt]
  | none => simp [yext, j]

theorem standardRotaryFrequency_pos (m : ℕ) (r : Fin m) :
    0 < standardRotaryFrequency m r :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem standardRotaryFrequency_le_one (m : ℕ) (r : Fin m) :
    standardRotaryFrequency m r ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (Nat.cast_nonneg _)
  · exact Nat.cast_nonneg _

theorem standardRotaryFrequency_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (standardRotaryFrequency m) := by
  intro r s hrs
  have he := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 10000)
    (by norm_num : (10000 : ℝ) ≠ 1)).mp hrs
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have ht := congrArg (fun t : ℝ => t * (m : ℝ)) he
  simp only [div_mul_cancel₀ _ hm0, neg_inj] at ht
  apply Fin.ext
  exact_mod_cast ht

/-- Standard frequencies give distinct complex Vandermonde nodes, since they
are distinct real angles in `(0,1]`, a subinterval of `(-π,π]`. -/
theorem standardRotaryFrequency_exp_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective
      (fun r => Complex.exp ((standardRotaryFrequency m r : ℂ) * Complex.I)) := by
  intro r s hrs
  have hr0 := standardRotaryFrequency_pos m r
  have hs0 := standardRotaryFrequency_pos m s
  have hr1 := standardRotaryFrequency_le_one m r
  have hs1 := standardRotaryFrequency_le_one m s
  have hπ := Real.two_le_pi
  have he : (standardRotaryFrequency m r : ℂ) * Complex.I =
      (standardRotaryFrequency m s : ℂ) * Complex.I :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith) hrs
  apply standardRotaryFrequency_injective hm
  simpa using congrArg Complex.im he

/-- Explicit finite width for standard-schedule interpolation, also at `n=0`.
All heads use this same schedule and common query vector. -/
theorem standardRotarySchedule_interpolates (n : ℕ) :
    RotaryInterpolates
      (frequencySchedule (n := n) (standardRotaryFrequency (n + 2))) := by
  apply frequencySchedule_interpolates_of_injective
  · omega
  · exact standardRotaryFrequency_exp_injective (by omega)

/-- Exact scalar score realization by the fixed standard rotary schedule.
The width `2(n+2)` is finite, common to all heads, and independent of head count. -/
theorem exists_standardPureRotaryFamily_score {n H : ℕ}
    (p : Fin H → PureRoPEAtom n) (c : ℝ) :
    ∃ (M : PureRotaryFamily n ((n + 2) * 2) H)
      (w : Vec ((n + 2) * 2)) (τ : ℝ),
      ∀ x, ⟪w, M.residual (frequencySchedule (standardRotaryFrequency (n + 2))) x⟫_ℝ
        - τ = c + ∑ h, (p h).eval x :=
  exists_pureRotaryFamily_score_of_interpolates _ (by omega)
    (standardRotarySchedule_interpolates n) p c

/-- Literal fixed-standard pure RoPE and the existing scalar class coincide at
every exact head count, including `n=0` and `H=0`. -/
theorem standardPureRotaryComputable_iff_scalar (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    standardPureRotaryComputable n H f ↔ pureRoPEComputable n H f := by
  constructor
  · exact pureRoPEComputable_of_standardPureRotaryComputable
  · intro hf
    refine ⟨n + 2, by omega, ?_⟩
    exact (pureRotaryComputableAt_iff_scalar_of_interpolates _ (by omega)
      (standardRotarySchedule_interpolates n) f).mpr hf

/-- Freely chosen shared frequencies and the existing scalar class coincide. -/
theorem freePureRotaryComputable_iff_scalar (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    freePureRotaryComputable n H f ↔ pureRoPEComputable n H f :=
  ⟨pureRoPEComputable_of_freePureRotaryComputable,
    fun hf => freePureRotaryComputable_of_standard
      ((standardPureRotaryComputable_iff_scalar n H f).mpr hf)⟩

/-- Frequency freedom does not change Boolean expressivity at any head count. -/
theorem standardPureRotaryComputable_iff_free (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    standardPureRotaryComputable n H f ↔ freePureRotaryComputable n H f :=
  (standardPureRotaryComputable_iff_scalar n H f).trans
    (freePureRotaryComputable_iff_scalar n H f).symm

end HeadComplexity
