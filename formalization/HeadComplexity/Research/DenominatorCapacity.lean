import HeadComplexity.Research.PartialLinearCapacity
import HeadComplexity.Research.NormalizedCounting

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
Margin-free capacity for positive denominator families with polynomial charts.
The linear numerator coefficients remain arbitrary real numbers.
-/

noncomputable section
namespace HeadComplexity.DenominatorCapacity
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {n H : ℕ} {K : Type*}

abbrev Input (n : ℕ) := Fin n → Bool
abbrev LinearParameter (n H : ℕ) := Unit ⊕ (Fin H × Fin n)

@[simp] theorem card_linearParameter : Fintype.card (LinearParameter n H) = n * H + 1 := by
  simp [LinearParameter]
  ring

/-- Clear all positive denominators, retaining linear dependence on the numerator
slopes and the output bias. -/
def clearedFeatures (B : Fin H → Input n → MvPolynomial K ℝ) (x : Input n) :
    LinearParameter n H → MvPolynomial K ℝ
  | Sum.inl _ => ∏ h, B h x
  | Sum.inr (h,i) => C (boolToReal (x i)) * ∏ g ∈ univ.erase h, B g x

private theorem prod_totalDegree_le (s : Finset (Fin H))
    (P : Fin H → MvPolynomial K ℝ) {D : ℕ}
    (hP : ∀ h, (P h).totalDegree ≤ D) :
    (∏ h ∈ s, P h).totalDegree ≤ s.card * D := by
  refine (totalDegree_finsetProd _ _).trans ?_
  exact (sum_le_card_nsmul s (fun h => (P h).totalDegree) D (fun h _ => hP h)).trans
    (by simp)

theorem clearedFeatures_totalDegree_le (B : Fin H → Input n → MvPolynomial K ℝ)
    {D : ℕ} (hB : ∀ h x, (B h x).totalDegree ≤ D)
    (x : Input n) (k : LinearParameter n H) :
    (clearedFeatures B x k).totalDegree ≤ D * H := by
  classical
  rcases k with k | ⟨h,i⟩
  · simpa [clearedFeatures, mul_comm] using
      prod_totalDegree_le univ (fun h => B h x) (fun h => hB h x)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    have hp := prod_totalDegree_le (univ.erase h) (fun g => B g x) (fun g => hB g x)
    have hc : (univ.erase h : Finset (Fin H)).card ≤ H :=
      (card_le_card (erase_subset h univ)).trans_eq (card_fin H)
    exact hp.trans (by nlinarith)

def score (B : Fin H → Input n → MvPolynomial K ℝ) (b : K → ℝ)
    (a : LinearParameter n H → ℝ) (x : Input n) : ℝ :=
  a (Sum.inl ()) + ∑ h, (∑ i, boolToReal (x i) * a (Sum.inr (h,i))) / eval b (B h x)

/-- Exact clearing identity, without a margin or coefficient-size assumption. -/
theorem eval_clearedFeatures (B : Fin H → Input n → MvPolynomial K ℝ)
    (b : K → ℝ) (a : LinearParameter n H → ℝ) (x : Input n)
    (hB : ∀ h, eval b (B h x) ≠ 0) :
    (fun k => eval b (clearedFeatures B x k)) ⬝ᵥ a =
      (∏ h, eval b (B h x)) * score B b a x := by
  classical
  simp only [clearedFeatures, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton, map_prod, map_mul, eval_C, score]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro h _
  have hs : (∑ i, (boolToReal (x i) * ∏ g ∈ univ.erase h, eval b (B g x)) *
      a (Sum.inr (h,i))) =
      (∏ g ∈ univ.erase h, eval b (B g x)) * ∑ i, boolToReal (x i) * a (Sum.inr (h,i)) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs, ← Finset.mul_prod_erase univ (fun g => eval b (B g x)) (mem_univ h)]
  field_simp [hB h]

/-- Truth tables represented in a fixed polynomial denominator chart. -/
def represented (B : Fin H → Input n → MvPolynomial K ℝ) : Set (Input n → Bool) :=
  {f | ∃ b : K → ℝ, ∃ a : LinearParameter n H → ℝ,
    (∀ h x, 0 < eval b (B h x)) ∧
    ∀ x, if f x then 0 < score B b a x else score B b a x < 0}

theorem represented_subset_patterns (B : Fin H → Input n → MvPolynomial K ℝ) :
    represented B ⊆ PartialLinearCapacity.patterns (clearedFeatures B) := by
  rintro f ⟨b,a,hB,hf⟩
  refine ⟨b,a,fun x => ?_⟩
  rw [eval_clearedFeatures B b a x (fun h => (hB h x).ne')]
  have hp : 0 < ∏ h, eval b (B h x) := prod_pos (fun h _ => hB h x)
  have hx := hf x
  cases hfx : f x <;> simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_pos_of_neg hp hx
  · exact mul_pos hp hx

/-- A finite unrestricted-margin count for any polynomial denominator chart. -/
theorem card_represented_le [Fintype K]
    (B : Fin H → Input n → MvPolynomial K ℝ) {D : ℕ}
    (hB : ∀ h x, (B h x).totalDegree ≤ D)
    (hK : Fintype.card K + 1 ≤ 2 ^ n) :
    ((represented B).ncard : ℝ) ≤
      ((2 ^ n + 2 * (n * H + 1)).choose (n * H + 1) : ℝ) *
      2 ^ (n * H + 1) *
      (4 * Real.exp 1 * (2 * (D * H) * (n * H + 1) + 1) * (2 : ℝ) ^ n /
        (Fintype.card K + 1)) ^ (Fintype.card K + 1) := by
  classical
  have hc : ((represented B).ncard : ℝ) ≤
      ((PartialLinearCapacity.patterns (clearedFeatures B)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (represented_subset_patterns B) (Set.toFinite _)
  have hw := PartialLinearCapacity.card_patterns_le (clearedFeatures B)
    (clearedFeatures_totalDegree_le B hB)
    (show 0 < Fintype.card (LinearParameter n H) by simp)
    (show Fintype.card K + 1 ≤ Fintype.card (Input n) by simpa [Input] using hK)
  apply hc.trans
  simpa only [card_linearParameter, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] using hw


abbrev AffineSlopeParameter (n H d : ℕ) :=
  Fin n ⊕ ((Fin d × Fin n) ⊕ (Fin H × Fin d))

@[simp] theorem card_affineSlopeParameter {d : ℕ} :
    Fintype.card (AffineSlopeParameter n H d) = n * (d + 1) + d * H := by
  simp [AffineSlopeParameter]
  ring

/-- A varying affine `d`-plane of normalized denominator slope vectors. -/
def affineSlopeDen {d : ℕ} (h : Fin H) (x : Input n) :
    MvPolynomial (AffineSlopeParameter n H d) ℝ :=
  1 + ∑ i, C (boolToReal (x i)) *
    (X (Sum.inl i) + ∑ j : Fin d,
      X (Sum.inr (Sum.inl (j,i))) * X (Sum.inr (Sum.inr (h,j))))

theorem affineSlopeDen_totalDegree_le {d : ℕ} (h : Fin H) (x : Input n) :
    (affineSlopeDen (d := d) h x).totalDegree ≤ 2 := by
  unfold affineSlopeDen
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

/-- Exact finite count for denominators whose slope vectors lie in a varying affine
subspace of dimension at most `d`. -/
theorem card_affineSlope_le {d : ℕ}
    (hK : n * (d + 1) + d * H + 1 ≤ 2 ^ n) :
    ((represented (affineSlopeDen (n := n) (H := H) (d := d))).ncard : ℝ) ≤
      ((2 ^ n + 2 * (n * H + 1)).choose (n * H + 1) : ℝ) *
      2 ^ (n * H + 1) *
      (4 * Real.exp 1 * (4 * H * (n * H + 1) + 1) * (2 : ℝ) ^ n /
        (n * (d + 1) + d * H + 1)) ^ (n * (d + 1) + d * H + 1) := by
  have h := card_represented_le (affineSlopeDen (n := n) (H := H) (d := d))
    affineSlopeDen_totalDegree_le (by simpa only [card_affineSlopeParameter] using hK)
  simpa only [card_affineSlopeParameter, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num, ← mul_assoc] using h

/-- The chart count applies to unchanged positive affine-fraction certificates after
exact normalization at the zero input. -/
theorem represented_of_affine (B : Fin H → Input n → MvPolynomial K ℝ)
    (A : AffineFractionFamily n H) (c : ℝ) (f : Input n → Bool)
    (b : K → ℝ)
    (hB : ∀ h x, eval b (B h x) =
      eval (NormalizedCounting.parameterPoint A 1) (NormalizedCounting.denPoly h x))
    (hf : ∀ x, if f x then
      0 < c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)
      else c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) < 0) :
    f ∈ represented B := by
  let a : LinearParameter n H → ℝ := Sum.elim
    (fun _ => c + ∑ h, (A.num h).coeff 0 / (A.den h).coeff 0)
    (fun hi => NormalizedCounting.parameterPoint A 1 (hi.1,false,hi.2))
  refine ⟨b,a,fun h x => ?_,fun x => ?_⟩
  · rw [hB]
    exact NormalizedCounting.eval_denPoly_pos A 1 h x
  · have hnum (h : Fin H) :
        (∑ i, boolToReal (x i) * a (Sum.inr (h,i))) =
          eval (NormalizedCounting.parameterPoint A 1)
            (NormalizedCounting.linearPoly false h x) := by
      simp [a, NormalizedCounting.linearPoly]
    have hs : score B b a x =
        c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) := by
      unfold score
      simp_rw [hnum, hB, NormalizedCounting.normalized_head_eval A one_ne_zero, div_one]
      simp only [a, Sum.elim_inl, sum_sub_distrib]
      ring
    simpa only [hs] using hf x

end HeadComplexity.DenominatorCapacity
