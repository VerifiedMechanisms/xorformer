import HeadComplexity.Results.RoPEArchitecturalComparison
import HeadComplexity.Results.FiniteDifferenceUpperBound
import HeadComplexity.Results.PureFiniteDifference
import HeadComplexity.Results.RoPEFourInputs

set_option linter.style.header false

/-!
# General bounds for literal pure rotary attention

The lower comparison is head preserving. The reverse bound proved here is
exponential, and does not establish the conjectured equality of the minima.
Both standard and freely chosen frequency schedules use the literal rectangular
architecture and the existing vanilla definitions.
-/

namespace HeadComplexity

theorem vanilla_exponential_of_pureRoPEComputable {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  obtain ⟨p, c, hp⟩ := hf
  exact pureRoPEFamily_vanilla_exponential_bound p c f hp

theorem vanilla_exponential_of_retainedRoPEComputable {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : retainedRoPEComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  obtain ⟨p, c, hp⟩ := hf
  exact retainedRoPEFamily_vanilla_exponential_bound p c f hp

theorem HStar_le_exponential_pureRoPEHStar {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ 2 ^ PureRoPEHStar n f - 1 := by
  classical
  have hc := computableWithHeadsN_of_computableWithSharedHeadsN
    (vanilla_exponential_of_pureRoPEComputable (pureRoPEHStar_computable f))
  unfold HStar
  rw [dif_pos (exists_computable f)]
  exact Nat.find_min' _ hc

theorem HStar_le_exponential_retainedRoPEHStar {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ 2 ^ RetainedRoPEHStar n f - 1 := by
  classical
  have hc := computableWithHeadsN_of_computableWithSharedHeadsN
    (vanilla_exponential_of_retainedRoPEComputable (retainedRoPEHStar_computable f))
  unfold HStar
  rw [dif_pos (exists_computable f)]
  exact Nat.find_min' _ hc

theorem vanilla_exponential_of_standardPureRotaryComputable {n H : ℕ}
    {f : (Fin n → Bool) → Bool}
    (hf : rectangularStandardPureRotaryComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 1) f :=
  vanilla_exponential_of_pureRoPEComputable
    ((rectangularStandardPureRotaryComputable_iff_scalar n H f).mp hf)

theorem vanilla_exponential_of_freePureRotaryComputable {n H : ℕ}
    {f : (Fin n → Bool) → Bool}
    (hf : rectangularFreePureRotaryComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 1) f :=
  vanilla_exponential_of_pureRoPEComputable
    ((rectangularFreePureRotaryComputable_iff_scalar n H f).mp hf)

theorem architecturalPureRoPEHStar_general_bounds {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    StandardPureRoPEHStar n f = FreePureRoPEHStar n f ∧
      StandardPureRoPEHStar n f ≤ HStar n f ∧
      HStar n f ≤ 2 ^ StandardPureRoPEHStar n f - 1 := by
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨rfl, pureRoPEHStar_le_vanilla f, HStar_le_exponential_pureRoPEHStar f⟩

theorem standardPureRotaryComputable_iff_vanilla_of_input_le_four {n H : ℕ}
    (hn : n ≤ 4) (f : (Fin n → Bool) → Bool) :
    rectangularStandardPureRotaryComputable n H f ↔
      computableWithSharedHeadsN n H f :=
  (rectangularStandardPureRotaryComputable_iff_scalar n H f).trans
    (pureRoPEComputable_iff_vanilla_of_input_le_four hn f)

theorem freePureRotaryComputable_iff_vanilla_of_input_le_four {n H : ℕ}
    (hn : n ≤ 4) (f : (Fin n → Bool) → Bool) :
    rectangularFreePureRotaryComputable n H f ↔
      computableWithSharedHeadsN n H f :=
  (rectangularFreePureRotaryComputable_iff_scalar n H f).trans
    (pureRoPEComputable_iff_vanilla_of_input_le_four hn f)

theorem architecturalPureRoPEHStar_eq_vanilla_of_input_le_four {n : ℕ}
    (hn : n ≤ 4) (f : (Fin n → Bool) → Bool) :
    StandardPureRoPEHStar n f = HStar n f ∧ FreePureRoPEHStar n f = HStar n f := by
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨pureRoPEHStar_eq_vanilla_of_input_le_four hn f,
    pureRoPEHStar_eq_vanilla_of_input_le_four hn f⟩

/-- A necessary condition for a strict improvement, not an assertion that any
such improvement exists. -/
theorem pureRoPE_strict_improvement_requires_five_inputs {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : PureRoPEHStar n f < HStar n f) :
    5 ≤ n ∧ 3 ≤ PureRoPEHStar n f ∧ 4 ≤ HStar n f := by
  have hn : ¬ n ≤ 4 := by
    intro hn
    have he := pureRoPEHStar_eq_vanilla_of_input_le_four hn f
    omega
  obtain ⟨hp, hv⟩ := pureRoPE_strict_improvement_lower_bounds f hf
  exact ⟨by omega, hp, hv⟩


/-- The pure numerator structure improves the general bound by one head. -/
theorem HStar_le_improved_exponential_pureRoPEHStar {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : 2 ≤ PureRoPEHStar n f) :
    HStar n f ≤ 2 ^ PureRoPEHStar n f - 2 := by
  classical
  have hc := computableWithHeadsN_of_computableWithSharedHeadsN
    (pureRoPEComputable_vanilla_improved_exponential_bound hf (pureRoPEHStar_computable f))
  unfold HStar
  rw [dif_pos (exists_computable f)]
  exact Nat.find_min' _ hc

theorem vanilla_improved_exponential_of_standardPureRotaryComputable {n H : ℕ}
    (hH : 2 ≤ H) {f : (Fin n → Bool) → Bool}
    (hf : rectangularStandardPureRotaryComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 2) f :=
  pureRoPEComputable_vanilla_improved_exponential_bound hH
    ((rectangularStandardPureRotaryComputable_iff_scalar n H f).mp hf)

theorem vanilla_improved_exponential_of_freePureRotaryComputable {n H : ℕ}
    (hH : 2 ≤ H) {f : (Fin n → Bool) → Bool}
    (hf : rectangularFreePureRotaryComputable n H f) :
    computableWithSharedHeadsN n (2 ^ H - 2) f :=
  pureRoPEComputable_vanilla_improved_exponential_bound hH
    ((rectangularFreePureRotaryComputable_iff_scalar n H f).mp hf)

end HeadComplexity
