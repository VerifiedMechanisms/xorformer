import HeadComplexity.Results.ReverseGridAxisRepair
import HeadComplexity.Atoms.OrientedAtomTangent

set_option linter.style.header false

/-!
# Joint orientation transfer for two fractions

Two affine fractions with positive denominators on the Boolean cube have the
same strict signs as three original atoms with strictly negative denominator
slopes. The construction is joint, and does not transfer a longer sum by
applying the theorem to pairs. No axis-vanishing assertion is made.
-/

namespace HeadComplexity.TwoHeadOrientationTransfer

open scoped BigOperators
open Filter Topology AxisZeroGluing

variable {n : ℕ}

/-- The joint cancellation identity, before any sign or slope assumptions. -/
theorem three_fraction_identity (a₁ a₂ b₁ b₂ l ε : ℝ)
    (hε : ε ≠ 0) (hl : l ≠ 0)
    (h₁ : l - ε * b₁ ≠ 0) (h₂ : l - ε * b₂ ≠ 0) :
    (a₁ / ε) / (l - ε * b₂) + (a₂ / ε) / (l - ε * b₁) -
        ((a₁ + a₂) / ε) / l =
      (l * (a₁ * b₂ + a₂ * b₁) - ε * (a₁ + a₂) * b₁ * b₂) /
        (l * (l - ε * b₁) * (l - ε * b₂)) := by
  field_simp
  ring

private theorem affine_sub_smul (c d ε : ℝ) (a b : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (c - ε * d) (fun i ↦ a i - ε * b i) x =
      affineValue c a x - ε * affineValue d b x := by
  simp only [affineValue, sub_mul, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum]
  ring

private theorem affine_div (c ε : ℝ) (a : Fin n → ℝ) (x : Fin n → Bool) :
    affineValue (c / ε) (fun i ↦ a i / ε) x = affineValue c a x / ε := by
  simp only [affineValue, div_mul_eq_mul_div, ← Finset.sum_div, add_div]

/-- Any strict finite cube sign pattern of two affine fractions transfers
jointly to three reverse fractions. The input denominator slopes are arbitrary.
All three output denominators remain positive on the entire cube. -/
theorem exists_reverse_three
    (a₁₀ a₂₀ b₁₀ b₂₀ l₀ : ℝ) (a₁ a₂ b₁ b₂ l : Fin n → ℝ)
    (σ : (Fin n → Bool) → ℝ)
    (hb₁ : ∀ x, 0 < affineValue b₁₀ b₁ x)
    (hb₂ : ∀ x, 0 < affineValue b₂₀ b₂ x)
    (hl : ∀ x, 0 < affineValue l₀ l x) (hlneg : ∀ i, l i < 0)
    (hsg : ∀ x, 0 < σ x * (affineValue a₁₀ a₁ x / affineValue b₁₀ b₁ x +
      affineValue a₂₀ a₂ x / affineValue b₂₀ b₂ x)) :
    ∃ Q : Fin 3 → StrictReverseRatio n, ∀ x, 0 < σ x * ∑ h, (Q h).value x := by
  classical
  let A₁ := affineValue a₁₀ a₁
  let A₂ := affineValue a₂₀ a₂
  let B₁ := affineValue b₁₀ b₁
  let B₂ := affineValue b₂₀ b₂
  let L := affineValue l₀ l
  let P := fun x ↦ A₁ x * B₂ x + A₂ x * B₁ x
  let R := fun x ↦ (A₁ x + A₂ x) * B₁ x * B₂ x
  have hP (x : Fin n → Bool) : 0 < σ x * P x := by
    have he : σ x * P x =
        (σ x * (A₁ x / B₁ x + A₂ x / B₂ x)) * (B₁ x * B₂ x) := by
      dsimp [P]
      have h₁ : B₁ x ≠ 0 := (hb₁ x).ne'
      have h₂ : B₂ x ≠ 0 := (hb₂ x).ne'
      field_simp
    rw [he]
    exact mul_pos (hsg x) (mul_pos (hb₁ x) (hb₂ x))
  have he : ∀ᶠ ε : ℝ in 𝓝 0,
      (∀ x, 0 < L x - ε * B₁ x) ∧ (∀ x, 0 < L x - ε * B₂ x) ∧
      (∀ i, l i - ε * b₁ i < 0) ∧ (∀ i, l i - ε * b₂ i < 0) ∧
      ∀ x, 0 < σ x * (L x * P x - ε * R x) := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · apply Filter.eventually_all.mpr
      intro x
      apply continuousAt_const.eventually_lt
        (show ContinuousAt (fun ε : ℝ ↦ L x - ε * B₁ x) 0 from by fun_prop)
      simpa using hl x
    · apply Filter.eventually_all.mpr
      intro x
      apply continuousAt_const.eventually_lt
        (show ContinuousAt (fun ε : ℝ ↦ L x - ε * B₂ x) 0 from by fun_prop)
      simpa using hl x
    · apply Filter.eventually_all.mpr
      intro i
      apply (show ContinuousAt (fun ε : ℝ ↦ l i - ε * b₁ i) 0 from by
        fun_prop).eventually_lt continuousAt_const
      simpa using hlneg i
    · apply Filter.eventually_all.mpr
      intro i
      apply (show ContinuousAt (fun ε : ℝ ↦ l i - ε * b₂ i) 0 from by
        fun_prop).eventually_lt continuousAt_const
      simpa using hlneg i
    · apply Filter.eventually_all.mpr
      intro x
      apply continuousAt_const.eventually_lt
        (show ContinuousAt (fun ε : ℝ ↦ σ x * (L x * P x - ε * R x)) 0 from by
          fun_prop)
      simpa only [zero_mul, sub_zero, mul_left_comm] using mul_pos (hl x) (hP x)
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp he
  let ε := radius / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨hD₁, hD₂, hneg₁, hneg₂, hnum⟩ :=
    hball (show ε ∈ Metric.ball (0 : ℝ) radius from by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
      dsimp [ε]
      linarith)
  let Q₁ : StrictReverseRatio n :=
    { a₀ := a₁₀ / ε, a := fun i ↦ a₁ i / ε
      b₀ := l₀ - ε * b₂₀, b := fun i ↦ l i - ε * b₂ i
      positive := fun x ↦ by rw [affine_sub_smul]; exact hD₂ x
      negative := hneg₂ }
  let Q₂ : StrictReverseRatio n :=
    { a₀ := a₂₀ / ε, a := fun i ↦ a₂ i / ε
      b₀ := l₀ - ε * b₁₀, b := fun i ↦ l i - ε * b₁ i
      positive := fun x ↦ by rw [affine_sub_smul]; exact hD₁ x
      negative := hneg₁ }
  let Q₃ : StrictReverseRatio n :=
    { a₀ := -((a₁₀ + a₂₀) / ε), a := fun i ↦ -((a₁ i + a₂ i) / ε)
      b₀ := l₀, b := l, positive := hl, negative := hlneg }
  refine ⟨![Q₁, Q₂, Q₃], fun x ↦ ?_⟩
  have h₃ : affineValue (-((a₁₀ + a₂₀) / ε))
      (fun i ↦ -((a₁ i + a₂ i) / ε)) x = -(A₁ x + A₂ x) / ε := by
    simp only [affineValue, neg_mul, Finset.sum_neg_distrib, div_mul_eq_mul_div,
      ← Finset.sum_div, add_mul, Finset.sum_add_distrib]
    dsimp [A₁, A₂, affineValue]
    ring
  have heval : (∑ h, (![Q₁, Q₂, Q₃] h).value x) =
      (L x * P x - ε * R x) / (L x * (L x - ε * B₁ x) * (L x - ε * B₂ x)) := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    change Q₁.value x + (Q₂.value x + Q₃.value x) = _
    dsimp [StrictReverseRatio.value, Q₁, Q₂, Q₃]
    rw [affine_div, affine_div, affine_sub_smul, affine_sub_smul, h₃]
    have hi := three_fraction_identity (A₁ x) (A₂ x) (B₁ x) (B₂ x) (L x) ε
      hε.ne' (hl x).ne' (hD₁ x).ne' (hD₂ x).ne'
    dsimp [P, R]
    convert hi using 1 <;> ring
  rw [heval, ← mul_div_assoc]
  exact div_pos (hnum x) (mul_pos (mul_pos (hl x) (hD₁ x)) (hD₂ x))

/-- A strict reverse ratio is exactly one admissible original atom. -/
theorem reverse_ratio_exists_atom (Q : StrictReverseRatio n) :
    ∃ φ : FracAtom n, (∀ x, φ.eval x = Q.value x) ∧ φ.α < 1 := by
  have hb₀ : 0 < Q.b₀ := by
    simpa [affineValue, boolToReal] using Q.positive (fun _ ↦ false)
  have hmargin : ∑ i, -Q.b i < Q.b₀ := by
    have ht := Q.positive (fun _ ↦ true)
    simp only [affineValue, boolToReal, ite_true, mul_one] at ht
    rw [Finset.sum_neg_distrib]
    linarith
  refine ⟨FracAtom.ofNegativeAffineRatio Q.a₀ Q.a Q.b₀ Q.b hb₀ Q.negative hmargin,
    fun x ↦ FracAtom.ofNegativeAffineRatio_eval _ _ _ _ _ _ _ x, ?_⟩
  change 1 - FracAtom.negativeAffineScale Q.b₀ Q.b < 1
  have hs := (FracAtom.negativeAffineScale_pos_lt_one Q.b₀ Q.b hb₀ Q.negative hmargin).1
  linarith

private theorem standard_reverse_positive (x : Fin n → Bool) :
    0 < affineValue ((n : ℝ) + 1) (fun _ ↦ -1) x := by
  have hc : (∑ i : Fin n, boolToReal (x i)) ≤ (n : ℝ) := by
    calc
      (∑ i : Fin n, boolToReal (x i)) ≤ ∑ _ : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        cases x i <;> norm_num [boolToReal]
      _ = _ := by simp
  simp only [affineValue, neg_one_mul, Finset.sum_neg_distrib]
  linarith

/-- A Boolean function computed by two original atoms has a strict
three-atom representation entirely in the reverse orientation. Bias and
zero scores on false inputs are both handled in the original model. -/
theorem exists_reverse_atoms_of_two {f : (Fin n → Bool) → Bool}
    (hf : fracComputable n 2 f) :
    ∃ φ : Fin 3 → FracAtom n, (∀ h, (φ h).α < 1) ∧
      ∀ x, if f x then 0 < ∑ h, (φ h).eval x else (∑ h, (φ h).eval x) < 0 := by
  classical
  obtain ⟨φ, c, hφ⟩ := exists_strict_fracCertificate hf
  let a₁₀ := (φ 0).tangentNumConst + c * (φ 0).tangentDenConst
  let a₁ := fun i ↦ (φ 0).tangentNumCoeff i + c * (φ 0).tangentDenCoeff i
  let a₂₀ := (φ 1).tangentNumConst
  let a₂ := (φ 1).tangentNumCoeff
  let b₁₀ := (φ 0).tangentDenConst
  let b₁ := (φ 0).tangentDenCoeff
  let b₂₀ := (φ 1).tangentDenConst
  let b₂ := (φ 1).tangentDenCoeff
  have hb₁ (x : Fin n → Bool) : 0 < affineValue b₁₀ b₁ x := by
    rw [show affineValue b₁₀ b₁ x = (φ 0).γ + ∑ i, (φ 0).wt x i from
      (φ 0).tangentDen_affineValue x]
    exact (φ 0).denom_pos x
  have hb₂ (x : Fin n → Bool) : 0 < affineValue b₂₀ b₂ x := by
    rw [show affineValue b₂₀ b₂ x = (φ 1).γ + ∑ i, (φ 1).wt x i from
      (φ 1).tangentDen_affineValue x]
    exact (φ 1).denom_pos x
  have hval (x : Fin n → Bool) :
      affineValue a₁₀ a₁ x / affineValue b₁₀ b₁ x +
        affineValue a₂₀ a₂ x / affineValue b₂₀ b₂ x = c + ∑ h, (φ h).eval x := by
    dsimp [a₁₀, a₁, a₂₀, a₂, b₁₀, b₁, b₂₀, b₂]
    rw [absorb_bias c _ _ _ _ x (hb₁ x).ne',
      FracAtom.tangentNum_affineValue, FracAtom.tangentDen_affineValue,
      FracAtom.tangentNum_affineValue, FracAtom.tangentDen_affineValue]
    rw [Fin.sum_univ_two]
    simp only [FracAtom.eval]
    ring
  have hsg (x : Fin n → Bool) :
      0 < outputSign (f x) * (affineValue a₁₀ a₁ x / affineValue b₁₀ b₁ x +
        affineValue a₂₀ a₂ x / affineValue b₂₀ b₂ x) := by
    rw [hval]
    cases hx : f x
    · have hn : c + ∑ h, (φ h).eval x < 0 := by simpa [hx] using hφ x
      simpa only [hx, outputSign, Bool.false_eq_true, ite_false, neg_one_mul,
        neg_pos] using hn
    · simpa only [hx, outputSign, ite_true, one_mul] using hφ x
  obtain ⟨Q, hQ⟩ := exists_reverse_three a₁₀ a₂₀ b₁₀ b₂₀ ((n : ℝ) + 1)
    a₁ a₂ b₁ b₂ (fun _ ↦ -1) (fun x ↦ outputSign (f x)) hb₁ hb₂
    standard_reverse_positive (fun _ ↦ by norm_num) hsg
  choose ψ hψ hα using fun h ↦ reverse_ratio_exists_atom (Q h)
  refine ⟨ψ, hα, fun x ↦ ?_⟩
  simp only [hψ]
  cases hx : f x <;> simpa [hx, outputSign] using hQ x

/-- The three reverse atoms are admissible in the unchanged head model. -/
theorem fracComputable_three_of_two {f : (Fin n → Bool) → Bool}
    (hf : fracComputable n 2 f) : fracComputable n 3 f := by
  obtain ⟨φ, _, hφ⟩ := exists_reverse_atoms_of_two hf
  refine ⟨φ, 0, fun x ↦ ?_⟩
  simp only [zero_add]
  cases hx : f x
  · have hn : (∑ h, (φ h).eval x) < 0 := by simpa [hx] using hφ x
    simpa [hx] using hn.le
  · simpa [hx] using hφ x

end HeadComplexity.TwoHeadOrientationTransfer
