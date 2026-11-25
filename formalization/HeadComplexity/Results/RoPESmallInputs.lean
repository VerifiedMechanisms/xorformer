import HeadComplexity.Results.RoPETwoHeads

set_option linter.style.header false

/-!
# Pure rotary equivalence for at most three input bits

Three fixed vanilla-admissible denominators give an exact interpolation basis
on the three-bit cube. Together with two-head equivalence and zero-head padding,
this proves equality at every head budget for input lengths at most three.
-/

namespace HeadComplexity

open scoped BigOperators

private noncomputable def threeBitCoefficients (s : (Fin 3 → Bool) → ℝ) : Fin 8 → ℝ :=
  let y₀ := s ![false, false, false]
  let y₁ := s ![false, false, true]
  let y₂ := s ![false, true, false]
  let y₃ := s ![false, true, true]
  let y₄ := s ![true, false, false]
  let y₅ := s ![true, false, true]
  let y₆ := s ![true, true, false]
  let y₇ := s ![true, true, true]
  ![y₀,
    -6*y₀ + 54*y₁ + 54*y₂ - 150*y₃ + 36*y₄ - 120*y₅ - 120*y₆ + 252*y₇,
    12*y₀ - 72*y₁ - 54*y₂ + 150*y₃ - 36*y₄ + 120*y₅ + 96*y₆ - 216*y₇,
    -6*y₀ + 54*y₁ + 36*y₂ - 120*y₃ + 36*y₄ - 120*y₅ - 96*y₆ + 216*y₇,
    -6*y₀ + 6*y₁ + 6*y₂ + 6*y₄ - 12*y₇,
    -21*y₀ + 108*y₁ + 84*y₂ - 225*y₃ + 54*y₄ - 180*y₅ - 144*y₆ + 324*y₇,
    6*y₀ - 78*y₁ - 54*y₂ + 180*y₃ - 54*y₄ + 180*y₅ + 144*y₆ - 324*y₇,
    15*y₀ - 90*y₁ - 90*y₂ + 225*y₃ - 60*y₄ + 180*y₅ + 180*y₆ - 360*y₇]

private noncomputable def threeBitRatios (s : (Fin 3 → Bool) → ℝ) :
    Fin 3 → AffineFraction 3 :=
  let a := threeBitCoefficients s
  ![⟨![a 1, a 2, a 3], 0, ![1, 1, 1], 1⟩,
    ⟨![a 4, a 5, a 6], 0, ![1, 2, 2], 1⟩,
    ⟨![a 7, 0, 0], 0, ![2, 1, 2], 1⟩]

private theorem threeBitRatios_admissible (s : (Fin 3 → Bool) → ℝ) (h : Fin 3) :
    (threeBitRatios s h).Admissible := by
  have hc (i : Fin 3) : 0 < (threeBitRatios s h).C i := by
    fin_cases h <;> fin_cases i <;> norm_num [threeBitRatios]
  have hd : (threeBitRatios s h).d = 1 := by fin_cases h <;> rfl
  refine ⟨?_, Or.inl hc, ?_⟩
  · intro x
    unfold AffineFraction.denominator
    rw [hd]
    apply add_pos_of_pos_of_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hc i).le
    cases x i <;> norm_num [boolToReal]
  · intro hz
    exact ((hc 0).ne' (hz 0)).elim

/-- An explicit exact real-score interpolation basis of three admissible ratios
on the three-bit cube. The eight interpolation coefficients are integers. -/
theorem exists_threeBit_affineFraction_score (s : (Fin 3 → Bool) → ℝ) :
    ∃ (r : Fin 3 → AffineFraction 3) (c : ℝ),
      (∀ h, (r h).Admissible) ∧ ∀ x, c + ∑ h, (r h).eval x = s x := by
  refine ⟨threeBitRatios s, threeBitCoefficients s 0, threeBitRatios_admissible s, ?_⟩
  intro x
  have hx : x = ![x 0, x 1, x 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hx]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;>
    simp only [threeBitRatios, threeBitCoefficients, AffineFraction.eval,
      AffineFraction.numerator, AffineFraction.denominator, Fin.sum_univ_succ, boolToReal,
      Matrix.cons_val] <;>
    dsimp <;> norm_num <;> ring

/-- Every three-bit Boolean function is computable by three unchanged vanilla
heads. This is exact interpolation, not merely a sign approximation. -/
theorem vanilla_three_computes_every_threeBit (f : (Fin 3 → Bool) → Bool) :
    computableWithSharedHeadsN 3 3 f := by
  obtain ⟨r, c, hr, hs⟩ := exists_threeBit_affineFraction_score
    (fun x => if f x then (1 : ℝ) else -1)
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 3 f).mpr
  refine ⟨r, c, hr, fun x => ?_⟩
  rw [hs]
  cases f x <;> norm_num

/-- Unused vanilla heads can be padded by identically zero admissible ratios. -/
theorem affineFractionComputable_mono {n H K : ℕ} {f : (Fin n → Bool) → Bool}
    (hHK : H ≤ K) (hf : affineFractionComputable n H f) :
    affineFractionComputable n K f := by
  let zero : AffineFraction n := ⟨fun _ => 0, 0, fun _ => 0, 1⟩
  have hz : zero.Admissible := by
    refine ⟨?_, Or.inr (Or.inr (fun _ => rfl)), ?_⟩
    · intro x
      norm_num [zero, AffineFraction.denominator]
    · intro _
      exact Or.inr (Or.inr (fun _ => rfl))
  have hze (x : Fin n → Bool) : zero.eval x = 0 := by
    simp [zero, AffineFraction.eval, AffineFraction.numerator, AffineFraction.denominator]
  induction K, hHK using Nat.le_induction with
  | base => exact hf
  | succ K hHK ih =>
      obtain ⟨r, c, hr, hs⟩ := ih
      let r' : Fin (K + 1) → AffineFraction n := Fin.lastCases zero r
      refine ⟨r', c, ?_, ?_⟩
      · intro h
        refine Fin.lastCases ?_ (fun i => ?_) h
        · simpa [r'] using hz
        · simpa [r'] using hr i
      · intro x
        simpa [r', Fin.sum_univ_castSucc, hze] using hs x

/-- Padding preserves the exact vanilla head budget semantics. -/
theorem computableWithSharedHeadsN_mono {n H K : ℕ} {f : (Fin n → Bool) → Bool}
    (hHK : H ≤ K) (hf : computableWithSharedHeadsN n H f) :
    computableWithSharedHeadsN n K f := by
  rw [computableWithSharedHeadsN_iff_affineFractionComputable] at hf ⊢
  exact affineFractionComputable_mono hHK hf

/-- A uniform three-head upper bound holds for every function on at most three
bits, including the empty input. -/
theorem vanilla_three_computes_of_input_le_three {n : ℕ} (hn : n ≤ 3)
    (f : (Fin n → Bool) → Bool) : computableWithSharedHeadsN n 3 f := by
  by_cases h3 : n = 3
  · subst n
    exact vanilla_three_computes_every_threeBit f
  · have hn2 : n ≤ 2 := by omega
    have hb : 2 ^ n - 1 ≤ 3 := by
      interval_cases n <;> norm_num
    apply computableWithSharedHeadsN_mono hb
    exact computableWithSharedHeadsN_of_computableWithHeadsN (universal_computable f)

/-- Universal pure/vanilla equivalence at every head count for input lengths
at most three. This places no complement-invariance restriction on the target. -/
theorem pureRoPEComputable_iff_vanilla_of_input_le_three {n H : ℕ}
    (hn : n ≤ 3) (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n H f ↔ computableWithSharedHeadsN n H f := by
  constructor
  · intro hf
    by_cases hH : H ≤ 2
    · exact vanilla_of_pureRoPEComputable_le_two hH hf
    · exact computableWithSharedHeadsN_mono (by omega)
        (vanilla_three_computes_of_input_le_three hn f)
  · exact pureRoPEComputable_of_vanilla

/-- Equality of the scalar pure and unchanged vanilla minima on at most three
input bits. The architectural bridge transfers this to both frequency choices. -/
theorem pureRoPEHStar_eq_vanilla_of_input_le_three {n : ℕ}
    (hn : n ≤ 3) (f : (Fin n → Bool) → Bool) :
    PureRoPEHStar n f = HStar n f := by
  apply le_antisymm (pureRoPEHStar_le_vanilla f)
  have hf := (pureRoPEComputable_iff_vanilla_of_input_le_three hn f).mp
    (pureRoPEHStar_computable f)
  have hc := computableWithHeadsN_of_computableWithSharedHeadsN hf
  classical
  unfold HStar
  rw [dif_pos (exists_computable f)]
  exact Nat.find_min' _ hc

end HeadComplexity
