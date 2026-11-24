import HeadComplexity.Research.FeasibleChartEntropy

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.CoherentDenominatorCharts
open MvPolynomial Finset
open scoped BigOperators
open PartialLinearCapacity DenominatorCapacity FeasibleRationalBasis

variable {n H : ℕ}

theorem denPoly_slope (φ : FracAtom n) (i : Fin n) :
    φ.denPoly.coeff (Finsupp.single i 1) = φ.ρ i * (φ.α - 1) := by
  classical
  have hs : Finsupp.single i (1 : ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr (by norm_num)
  simp only [FracAtom.denPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_sum]
  simp only [affineAt, MvPolynomial.coeff_add, coeff_C_mul, coeff_X, coeff_C]
  simp [hs, Ne.symm hs, Finsupp.single_left_inj (by norm_num : (1 : ℕ) ≠ 0)]
  ring


/-- Every slope in a head has one common weak sign. Squared coordinates encode
that sign without allowing mixed orientations within one denominator. -/
def orientedDen (σ : Fin H → Bool) (h : Fin H) (x : Input n) :
    MvPolynomial (Parameter n H) ℝ :=
  1 + ∑ i, C (boolToReal (x i) * (if σ h then 1 else -1)) * X (h,i) ^ 2

theorem represented_of_computable {f : Input n → Bool}
    (hf : computableWithHeadsN n H f) :
    ∃ σ : Fin H → Bool, f ∈ represented (orientedDen σ) := by
  classical
  obtain ⟨φ,c,hstrict⟩ := exists_strict_fracCertificate (fracComputable_of_computable hf)
  let A := FracAtom.affineFamily φ
  let u : Parameter n H → ℝ := fun hi =>
    NormalizedCounting.parameterPoint A 1 (hi.1,true,hi.2)
  let σ : Fin H → Bool := fun h => decide (1 ≤ (φ h).α)
  let b : Parameter n H → ℝ := fun hi => Real.sqrt |u hi|
  have hu (h : Fin H) (i : Fin n) :
      (if σ h then (1 : ℝ) else -1) * b (h,i) ^ 2 = u (h,i) := by
    have hs : u (h,i) = (φ h).ρ i * ((φ h).α - 1) / (φ h).denPoly.coeff 0 := by
      change (φ h).denPoly.coeff (Finsupp.single i 1) / (φ h).denPoly.coeff 0 = _
      rw [denPoly_slope]
    have hd : 0 < (φ h).denPoly.coeff 0 := NormalizedCounting.den_constant_pos A h
    have hr := (φ h).hρ i
    dsimp [b]
    rw [Real.sq_sqrt (abs_nonneg _)]
    by_cases ha : 1 ≤ (φ h).α
    · simp only [σ, ha, decide_true, ↓reduceIte, one_mul]
      exact abs_of_nonneg (by rw [hs]; positivity)
    · simp only [σ, ha, decide_false, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
      have hn : u (h,i) ≤ 0 := by
        rw [hs]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith)) hd.le
      rw [abs_of_nonpos hn]
      ring
  refine ⟨σ, DenominatorCapacity.represented_of_affine (orientedDen σ) A c f b ?_ ?_⟩
  · intro h x
    simp only [orientedDen, NormalizedCounting.denPoly, NormalizedCounting.linearPoly,
      map_add, map_one, map_sum, map_mul, eval_C, map_pow, eval_X]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [mul_assoc, hu]
  · intro x
    simpa only [A, FracAtom.affineFamily, ← FracAtom.eval_eq_numPoly_div_denPoly] using hstrict x

/-- A globally feasible active chart, with the union over coherent orientations
included in the extension set rather than charged again as an external choice. -/
def coherentPatterns (c : Certificate (Input n) (LinearParameter n H)) :
    Set (Input n → Bool) := ⋃ σ : Fin H → Bool, patterns (orientedDen σ) c

theorem exists_coherent_certificate {f : Input n → Bool}
    (hf : computableWithHeadsN n H f) :
    ∃ c : Certificate (Input n) (LinearParameter n H), f ∈ coherentPatterns c := by
  obtain ⟨σ, hσ⟩ := represented_of_computable hf
  obtain ⟨c, hc⟩ := exists_certificate (orientedDen σ) hσ
  exact ⟨c, Set.mem_iUnion.mpr ⟨σ, hc⟩⟩

theorem card_original_le_sum :
    (headComputableFunctions n H).ncard ≤ (by classical exact
      (∑ c : Certificate (Input n) (LinearParameter n H), (coherentPatterns c).ncard)) := by
  classical
  have hsub : headComputableFunctions n H ⊆
      ⋃ c : Certificate (Input n) (LinearParameter n H), coherentPatterns c := by
    intro f hf
    obtain ⟨c, hc⟩ := exists_coherent_certificate hf
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (Set.ncard_iUnion_le_of_fintype coherentPatterns)


theorem card_original_le_exp_of_chart_bound {E : ℝ}
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((coherentPatterns c).ncard : ℝ) ≤ Real.exp E) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      Real.exp (((n : ℝ) * H + 1) *
        Real.log (2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1)) + E) := by
  classical
  calc
    _ ≤ ∑ c : Certificate (Input n) (LinearParameter n H),
        ((coherentPatterns c).ncard : ℝ) := by exact_mod_cast (card_original_le_sum (n := n) (H := H))
    _ ≤ ∑ _c : Certificate (Input n) (LinearParameter n H), Real.exp E :=
      sum_le_sum fun c _ => hchart c
    _ = (Fintype.card (Certificate (Input n) (LinearParameter n H)) : ℝ) * Real.exp E := by simp
    _ ≤ Real.exp (((n : ℝ) * H + 1) *
        Real.log (2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1))) * Real.exp E := by
      have hh := FeasibleChartEntropy.card_certificates_le_exp (n := n) (H := H)
      rw [Fintype.card_eq_nat_card] at hh ⊢
      exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- This hypothesis concerns only coherent positive denominators and retains
all full-cube feasibility inequalities. It remains a missing counting lemma. -/
theorem worstCase_gt_of_chart_entropy {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * t))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((coherentPatterns c).ncard : ℝ) ≤ Real.exp (((n : ℝ) * H + 1) * t)) :
    H < worstCaseHeadComplexity n := by
  apply FeasibleChartEntropy.worstCase_gt_of_card_le_exp
  exact (card_original_le_exp_of_chart_bound hchart).trans
    (Real.exp_le_exp.mpr (FeasibleChartEntropy.certificate_entropy_at_budget hn htlo hthi hbudget))

theorem worstCase_gt_of_sqrt_chart_entropy (hn : 32 ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * Real.sqrt n))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((coherentPatterns c).ncard : ℝ) ≤ Real.exp (((n : ℝ) * H + 1) * Real.sqrt n)) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_chart_entropy hn (MarginCapacityEstimates.sqrt_test_range hn).1
    (MarginCapacityEstimates.sqrt_test_range hn).2 hbudget hchart

theorem worstCase_gt_of_logarithmic_chart_entropy (hn : 32 ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * ((n : ℝ) / Real.log n)))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((coherentPatterns c).ncard : ℝ) ≤ Real.exp (((n : ℝ) * H + 1) * ((n : ℝ) / Real.log n))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_chart_entropy hn (MarginCapacityEstimates.logarithmic_test_range hn).1
    (MarginCapacityEstimates.logarithmic_test_range hn).2 hbudget hchart

end HeadComplexity.CoherentDenominatorCharts
