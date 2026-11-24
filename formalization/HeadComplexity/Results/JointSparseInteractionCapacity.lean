import HeadComplexity.Results.WarrenBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.style.header false

/-!
# A fixed sparse interaction pattern still has a logarithmic capacity budget

The active heads at each input are fixed before the labels. All polynomial
coefficients may depend jointly on the labels. The degree depends on the
number of active heads, not the total number of heads or the size of the cell.
This is a restriction on the stated family, not on unrestricted xorformer
scores or on label-dependent changes of the incidence pattern.
-/

namespace HeadComplexity

open scoped BigOperators
open MvPolynomial

noncomputable def sparseRatioCleared {I J K : Type*} [DecidableEq J]
    (active : I → Finset J) (bias : I → MvPolynomial K ℝ)
    (num den : I → J → MvPolynomial K ℝ) (x : I) : MvPolynomial K ℝ :=
  bias x * ∏ h ∈ active x, den x h +
    ∑ h ∈ active x, num x h * ∏ j ∈ (active x).erase h, den x j

theorem sparseRatioCleared_degree {I J K : Type*} [DecidableEq J]
    (active : I → Finset J) (bias : I → MvPolynomial K ℝ)
    (num den : I → J → MvPolynomial K ℝ) {a b D : ℕ}
    (ha : ∀ x, (bias x).totalDegree ≤ a)
    (hn : ∀ x, ∀ h ∈ active x, (num x h).totalDegree ≤ a)
    (hd : ∀ x, ∀ h ∈ active x, (den x h).totalDegree ≤ b)
    (hD : ∀ x, (active x).card ≤ D) (x : I) :
    (sparseRatioCleared active bias num den x).totalDegree ≤ a + b * D := by
  classical
  have hp (s : Finset J) (hs : s ⊆ active x) :
      (∏ h ∈ s, den x h).totalDegree ≤ b * D := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc
      ∑ h ∈ s, (den x h).totalDegree ≤ ∑ _h ∈ s, b :=
        Finset.sum_le_sum fun h hh ↦ hd x h (hs hh)
      _ = b * s.card := by simp [Nat.mul_comm]
      _ ≤ b * D := Nat.mul_le_mul_left b ((Finset.card_le_card hs).trans (hD x))
  unfold sparseRatioCleared
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add (ha x) (hp _ (by rfl)))
  · apply totalDegree_finsetSum_le
    intro h hh
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (hn x h hh) (hp _ (Finset.erase_subset h _)))

theorem sparseRatioCleared_eval {I J K : Type*} [DecidableEq J]
    (active : I → Finset J) (bias : I → MvPolynomial K ℝ)
    (num den : I → J → MvPolynomial K ℝ) (θ : K → ℝ) (x : I)
    (hden : ∀ h ∈ active x, eval θ (den x h) ≠ 0) :
    eval θ (sparseRatioCleared active bias num den x) =
      (∏ h ∈ active x, eval θ (den x h)) *
        (eval θ (bias x) + ∑ h ∈ active x, eval θ (num x h) / eval θ (den x h)) := by
  classical
  simp only [sparseRatioCleared, map_add, map_mul, map_prod, map_sum]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro h hh
    rw [← Finset.mul_prod_erase (active x) (fun j ↦ eval θ (den x j)) hh]
    field_simp [hden h hh]

/-- The score family shatters its input set, with all parameters selected
jointly for each labeling but a fixed active incidence pattern. -/
def SparseRatioUniversal {I J K : Type*} [DecidableEq J]
    (active : I → Finset J) (bias : I → MvPolynomial K ℝ)
    (num den : I → J → MvPolynomial K ℝ) : Prop :=
  ∀ f : I → Bool, ∃ θ : K → ℝ,
    (∀ x, ∀ h ∈ active x, 0 < eval θ (den x h)) ∧
    ∀ x, if f x then
      0 < eval θ (bias x) + ∑ h ∈ active x, eval θ (num x h) / eval θ (den x h)
    else eval θ (bias x) + ∑ h ∈ active x, eval θ (num x h) / eval θ (den x h) < 0

theorem sparseRatio_universal_capacity {I J K : Type*}
    [Fintype I] [Fintype K] [DecidableEq J]
    (active : I → Finset J) (bias : I → MvPolynomial K ℝ)
    (num den : I → J → MvPolynomial K ℝ) {a b D : ℕ}
    (ha : ∀ x, (bias x).totalDegree ≤ a)
    (hn : ∀ x, ∀ h ∈ active x, (num x h).totalDegree ≤ a)
    (hd : ∀ x, ∀ h ∈ active x, (den x h).totalDegree ≤ b)
    (hD : ∀ x, (active x).card ≤ D)
    (hdeg : 0 < a + b * D) (hK : 0 < Fintype.card K)
    (hKI : Fintype.card K ≤ Fintype.card I)
    (huniv : SparseRatioUniversal active bias num den) :
    (2 : ℝ) ^ Fintype.card I ≤
      (4 * Real.exp 1 * (a + b * D) * Fintype.card I / Fintype.card K) ^ Fintype.card K := by
  classical
  have hfull : strictPolynomialSignPatterns (sparseRatioCleared active bias num den) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    obtain ⟨θ, hpos, hsign⟩ := huniv f
    refine ⟨θ, fun x ↦ ?_⟩
    rw [sparseRatioCleared_eval active bias num den θ x (fun h hh ↦ (hpos x h hh).ne')]
    have hp : 0 < ∏ h ∈ active x, eval θ (den x h) :=
      Finset.prod_pos fun h hh ↦ hpos x h hh
    have hs := hsign x
    split_ifs at hs ⊢
    · exact mul_pos hp hs
    · exact mul_neg_of_pos_of_neg hp hs
  have hw := strictPolynomialSignPatterns_card_le hdeg hK hKI
    (sparseRatioCleared active bias num den)
    (sparseRatioCleared_degree active bias num den ha hn hd hD)
  rw [hfull] at hw
  simpa [Set.ncard_univ, Fintype.card_fun] using hw

/-- An explicit logarithmic form of the Warren budget. -/
theorem warren_capacity_log_budget {M P d : ℕ}
    (hP : 0 < P) (hPM : P ≤ M) (hd : 0 < d)
    (hcap : (2 : ℝ)^M ≤ (4 * Real.exp 1 * d * M / P)^P) :
    (M : ℝ) ≤ 6 * P * Real.log (4 * Real.exp 1 * d) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hMr : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le hP hPM)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  let r : ℝ := (M : ℝ) / P
  have hr : 0 < r := div_pos hMr hPr
  have hrlog : Real.log r ≤ r / 2 := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hr (by norm_num : (0 : ℝ) < 2))
    rw [Real.log_div hr.ne' (by norm_num)] at ht
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hb : 0 < 4 * Real.exp 1 * (d : ℝ) * M / P := by positivity
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^M) hcap
  rw [Real.log_pow, Real.log_pow] at hl
  have heq : 4 * Real.exp 1 * (d : ℝ) * M / P = (4 * Real.exp 1 * d) * r := by
    dsimp [r]
    ring
  rw [heq, Real.log_mul (by positivity : 4 * Real.exp 1 * (d : ℝ) ≠ 0) hr.ne'] at hl
  have hrl : (P : ℝ) * Real.log r ≤ (M : ℝ) / 2 := by
    have ht := mul_le_mul_of_nonneg_left hrlog hPr.le
    dsimp [r] at ht
    field_simp at ht ⊢
    nlinarith
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog2 hMr.le
  nlinarith

theorem sparseRatio_universal_log_budget {I J K : Type*}
    [Fintype I] [Fintype K] [DecidableEq J]
    (active : I → Finset J) (bias : I → MvPolynomial K ℝ)
    (num den : I → J → MvPolynomial K ℝ) {a b D : ℕ}
    (ha : ∀ x, (bias x).totalDegree ≤ a)
    (hn : ∀ x, ∀ h ∈ active x, (num x h).totalDegree ≤ a)
    (hd : ∀ x, ∀ h ∈ active x, (den x h).totalDegree ≤ b)
    (hD : ∀ x, (active x).card ≤ D)
    (hdeg : 0 < a + b * D) (hK : 0 < Fintype.card K)
    (hKI : Fintype.card K ≤ Fintype.card I)
    (huniv : SparseRatioUniversal active bias num den) :
    (Fintype.card I : ℝ) ≤
      6 * Fintype.card K * Real.log (4 * Real.exp 1 * (a + b * D)) := by
  have hc := sparseRatio_universal_capacity active bias num den ha hn hd hD hdeg hK hKI huniv
  have ht := warren_capacity_log_budget hK hKI hdeg
    (by simpa only [Nat.cast_add, Nat.cast_mul] using hc)
  simpa only [Nat.cast_add, Nat.cast_mul] using ht

/-- A finite label-dependent choice of architecture is charged separately.
The degree bound must hold for every architecture in the library. -/
theorem polynomialLibrary_universal_capacity {A I K : Type*}
    [Fintype A] [Fintype I] [Fintype K] {d : ℕ}
    (P : A → I → MvPolynomial K ℝ)
    (hd : 0 < d) (hK : 0 < Fintype.card K)
    (hKI : Fintype.card K ≤ Fintype.card I)
    (hdegree : ∀ a i, (P a i).totalDegree ≤ d)
    (huniv : ∀ f : I → Bool, ∃ a, StrictPolynomialSignPattern (P a) f) :
    (2 : ℝ) ^ Fintype.card I ≤ Fintype.card A *
      (4 * Real.exp 1 * d * Fintype.card I / Fintype.card K) ^ Fintype.card K := by
  classical
  have hfull : (⋃ a, strictPolynomialSignPatterns (P a)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    obtain ⟨a, ha⟩ := huniv f
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  have hc := Set.ncard_iUnion_le_of_fintype (fun a ↦ strictPolynomialSignPatterns (P a))
  rw [hfull] at hc
  have hc' : ((Set.univ : Set (I → Bool)).ncard : ℝ) ≤
      ∑ a, ((strictPolynomialSignPatterns (P a)).ncard : ℝ) := by exact_mod_cast hc
  calc
    (2 : ℝ) ^ Fintype.card I = ((Set.univ : Set (I → Bool)).ncard : ℝ) := by
      simp [Set.ncard_univ, Fintype.card_fun]
    _ ≤ ∑ a, ((strictPolynomialSignPatterns (P a)).ncard : ℝ) := hc'
    _ ≤ ∑ _a : A, (4 * Real.exp 1 * d * Fintype.card I / Fintype.card K) ^ Fintype.card K :=
      Finset.sum_le_sum fun a _ ↦ strictPolynomialSignPatterns_card_le hd hK hKI (P a) (hdegree a)
    _ = _ := by simp

/-- The architecture entropy adds `log T`, rather than replacing the active
degree by the total number of heads. -/
theorem warren_capacity_log_budget_with_choices {M P d : ℕ} {T : ℝ}
    (hT : 0 < T) (hP : 0 < P) (hPM : P ≤ M) (hd : 0 < d)
    (hcap : (2 : ℝ)^M ≤ T * (4 * Real.exp 1 * d * M / P)^P) :
    (M : ℝ) ≤ 6 * Real.log T + 6 * P * Real.log (4 * Real.exp 1 * d) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hMr : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le hP hPM)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  let r : ℝ := (M : ℝ) / P
  have hr : 0 < r := div_pos hMr hPr
  have hrlog : Real.log r ≤ r / 2 := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hr (by norm_num : (0 : ℝ) < 2))
    rw [Real.log_div hr.ne' (by norm_num)] at ht
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hb : 0 < 4 * Real.exp 1 * (d : ℝ) * M / P := by positivity
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^M) hcap
  rw [Real.log_pow, Real.log_mul hT.ne' (pow_pos hb _).ne', Real.log_pow] at hl
  have heq : 4 * Real.exp 1 * (d : ℝ) * M / P = (4 * Real.exp 1 * d) * r := by
    dsimp [r]
    ring
  rw [heq, Real.log_mul (by positivity : 4 * Real.exp 1 * (d : ℝ) ≠ 0) hr.ne'] at hl
  have hrl : (P : ℝ) * Real.log r ≤ (M : ℝ) / 2 := by
    have ht := mul_le_mul_of_nonneg_left hrlog hPr.le
    dsimp [r] at ht
    field_simp at ht ⊢
    nlinarith
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog2 hMr.le
  nlinarith

theorem polynomialLibrary_universal_log_budget {A I K : Type*}
    [Fintype A] [Fintype I] [Fintype K] {d : ℕ}
    (P : A → I → MvPolynomial K ℝ)
    (hA : 0 < Fintype.card A) (hd : 0 < d) (hK : 0 < Fintype.card K)
    (hKI : Fintype.card K ≤ Fintype.card I)
    (hdegree : ∀ a i, (P a i).totalDegree ≤ d)
    (huniv : ∀ f : I → Bool, ∃ a, StrictPolynomialSignPattern (P a) f) :
    (Fintype.card I : ℝ) ≤ 6 * Real.log (Fintype.card A) +
      6 * Fintype.card K * Real.log (4 * Real.exp 1 * d) :=
  warren_capacity_log_budget_with_choices (by exact_mod_cast hA) hK hKI hd
    (polynomialLibrary_universal_capacity P hd hK hKI hdegree huniv)

end HeadComplexity
