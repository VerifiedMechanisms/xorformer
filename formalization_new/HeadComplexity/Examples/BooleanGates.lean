module

public import HeadComplexity.Attention.Complexity.OneHead
public import HeadComplexity.Attention.Complexity.Symmetric
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Two-bit Boolean gates

The number of adjacent changes in a symmetric truth table gives its exact head count.
For XOR, we also give the two affine fractions explicitly and rule out one head using
the checkerboard theorem.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace HeadComplexity.Examples

open BooleanFunction

/-- Regard a binary Boolean gate as a function on the two-dimensional cube. -/
def twoBitGate (g : Bool → Bool → Bool) (x : Fin 2 → Bool) : Bool :=
  g (x 0) (x 1)

/-- The Hamming weight of a two-bit input is the sum of its two zero-or-one bit values. -/
private theorem hammingWeight_two (x : Fin 2 → Bool) :
    Bool.hammingWeight x = (x 0).toNat + (x 1).toNat := by
  simpa [Fin.sum_univ_two] using (Bool.sum_cubePoint (R := ℕ) x).symm

/-- A symmetric binary gate is determined by its values at weights zero, one, and two. -/
theorem twoBitGate_eq_symmetricFn (g : Bool → Bool → Bool) (hg : ∀ a b, g a b = g b a) :
    twoBitGate g = symmetricFn ![g false false, g false true, g true true] := by
  funext x
  cases h₀ : x 0 <;> cases h₁ : x 1
  · rw [symmetricFn_apply_of_hammingWeight_eq _ (k := 0) (by simp [hammingWeight_two, h₀, h₁])]
    simp [twoBitGate, h₀, h₁]
  · rw [symmetricFn_apply_of_hammingWeight_eq _ (k := 1) (by simp [hammingWeight_two, h₀, h₁])]
    simp [twoBitGate, h₀, h₁]
  · rw [symmetricFn_apply_of_hammingWeight_eq _ (k := 1) (by simp [hammingWeight_two, h₀, h₁])]
    simpa [twoBitGate, h₀, h₁] using hg true false
  · rw [symmetricFn_apply_of_hammingWeight_eq _ (k := 2) (by simp [hammingWeight_two, h₀, h₁])]
    simp [twoBitGate, h₀, h₁]

/-- The exact head count for all eight symmetric two-bit truth tables. -/
theorem headComplexity_symmetricFn_two (a b c : Bool) :
    headComplexity (symmetricFn ![a, b, c]) =
      (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) := by
  rw [headComplexity_symmetricFn]
  simp [signChanges, Finset.card_filter, Fin.sum_univ_two]
  by_cases h : a = b <;> simp [h]

/-- The head complexity of a symmetric binary gate counts its changes across the three Hamming
weights. -/
theorem headComplexity_twoBitGate (g : Bool → Bool → Bool) (hg : ∀ a b, g a b = g b a) :
    headComplexity (twoBitGate g) =
      (if g false false ≠ g false true then 1 else 0) +
        (if g false true ≠ g true true then 1 else 0) := by
  rw [twoBitGate_eq_symmetricFn g hg, headComplexity_symmetricFn_two]

/-- The two-bit function that is always false needs zero heads. -/
theorem headComplexity_false : headComplexity (fun _ : Fin 2 → Bool ↦ false) = 0 :=
  headComplexity_eq_zero_iff.mpr fun _ _ ↦ rfl

/-- The two-bit function that is always true needs zero heads. -/
theorem headComplexity_true : headComplexity (fun _ : Fin 2 → Bool ↦ true) = 0 :=
  headComplexity_eq_zero_iff.mpr fun _ _ ↦ rfl

/-- The two-input OR gate needs exactly one head. -/
theorem headComplexity_or : headComplexity (twoBitGate (· || ·)) = 1 :=
  (headComplexity_twoBitGate _ Bool.or_comm).trans rfl

/-- The two-input AND gate needs exactly one head. -/
theorem headComplexity_and : headComplexity (twoBitGate (· && ·)) = 1 :=
  (headComplexity_twoBitGate _ Bool.and_comm).trans rfl

/-- The two-input NOR gate needs exactly one head. -/
theorem headComplexity_nor : headComplexity (twoBitGate fun a b ↦ !(a || b)) = 1 :=
  (headComplexity_twoBitGate _ fun a b ↦ congrArg Bool.not (Bool.or_comm a b)).trans rfl

/-- The two-input NAND gate needs exactly one head. -/
theorem headComplexity_nand : headComplexity (twoBitGate fun a b ↦ !(a && b)) = 1 :=
  (headComplexity_twoBitGate _ fun a b ↦ congrArg Bool.not (Bool.and_comm a b)).trans rfl

/-- The two-input XNOR gate needs exactly two heads. -/
theorem headComplexity_xnor : headComplexity (twoBitGate fun a b ↦ !(xor a b)) = 2 :=
  (headComplexity_twoBitGate _ fun a b ↦ congrArg Bool.not (Bool.xor_comm a b)).trans rfl

private def hammingReciprocal (b d : ℝ) : Attention.AffineFraction 2 where
  numerator := (AffineMap.constCoeffEquiv ℝ (Fin 2)).symm (b, 0)
  denominator := (AffineMap.constCoeffEquiv ℝ (Fin 2)).symm (d, fun _ ↦ 1)

/-- The denominator of the reciprocal example is its offset plus the input's Hamming weight. -/
private theorem hammingReciprocal_denominator_apply (b d : ℝ) (x : Fin 2 → Bool) :
    (hammingReciprocal b d).denominator (Bool.cubePoint ℝ x) = d + (Bool.hammingWeight x : ℝ) := by
  change (AffineMap.constCoeffEquiv ℝ (Fin 2)).symm (d, fun _ ↦ 1) (Bool.cubePoint ℝ x) = _
  rw [AffineMap.constCoeffEquiv_symm_apply]
  simp only [dotProduct, one_mul, Bool.sum_cubePoint]

/-- A positive offset makes the reciprocal example admissible for any constant numerator. -/
private theorem hammingReciprocal_admissible (b d : ℝ) (hd : 0 < d) :
    (hammingReciprocal b d).Admissible := by
  refine ⟨fun x ↦ ?_, Or.inl fun i ↦ by simp [hammingReciprocal]⟩
  rw [hammingReciprocal_denominator_apply]
  exact add_pos_of_pos_of_nonneg hd (Nat.cast_nonneg _)

/-- The reciprocal example evaluates to its constant numerator divided by the offset plus the
Hamming weight. -/
private theorem hammingReciprocal_eval (b d : ℝ) (x : Fin 2 → Bool) :
    (hammingReciprocal b d).eval x = b / (d + (Bool.hammingWeight x : ℝ)) := by
  simp only [Attention.AffineFraction.eval, hammingReciprocal_denominator_apply]
  simp [hammingReciprocal, AffineMap.constCoeffEquiv_symm_apply]

/-- An explicit two-head score for XOR, with residues `-15` and `35` and shifts `1` and `2`. -/
def xorScore (x : Fin 2 → Bool) : ℝ :=
  let k := (Bool.hammingWeight x : ℝ)
  (-4) + ((-15) / (1 + k) + 35 / (2 + k))

/-- The displayed rational score for XOR is realized exactly with two heads. -/
theorem hasHeadScore_xorScore : HasHeadScore xorScore 2 := by
  let r : Fin 2 → Attention.AffineFraction 2 := ![hammingReciprocal (-15) 1, hammingReciprocal 35 2]
  refine hasHeadScore_iff_exists_affineFractions.mpr ⟨-4, r, ?_, fun x ↦ ?_⟩
  · intro i
    fin_cases i
    · exact hammingReciprocal_admissible (-15) 1 zero_lt_one
    · exact hammingReciprocal_admissible 35 2 zero_lt_two
  · simp [xorScore, r, Fin.sum_univ_two, hammingReciprocal_eval]

/-- The displayed XOR score is positive precisely when the two bits differ. -/
theorem signRepresents_xorScore : Function.SignRepresents xorScore (twoBitGate xor) := by
  intro x
  change 0 < xorScore x ↔ xor (x 0) (x 1) = true
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> norm_num [xorScore, hammingWeight_two, h₀, h₁, xor]

/-- The explicit score gives a two-head model that computes XOR. -/
theorem computableWithHeads_xor_two : ComputableWithHeads (twoBitGate xor) 2 :=
  hasHeadScore_xorScore.computableWithHeads signRepresents_xorScore

/-- A single head cannot compute XOR on two bits. -/
theorem not_computableWithHeads_xor_one : ¬ComputableWithHeads (twoBitGate xor) 1 := by
  refine not_computableWithHeads_one_of_checkerboard (fun _ ↦ false) Fin.zero_ne_one true
    (fun u v ↦ ?_)
  simp [twoBitGate]

/-- The two-input XOR gate needs exactly two heads. -/
theorem headComplexity_xor : headComplexity (twoBitGate xor) = 2 :=
  (headComplexity_eq_succ_iff (H := 1)).mpr
    ⟨computableWithHeads_xor_two, not_computableWithHeads_xor_one⟩

end HeadComplexity.Examples
