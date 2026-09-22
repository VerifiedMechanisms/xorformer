import HeadComplexity.Results.AffineSlab
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.RestrictionLowerBounds
import HeadComplexity.Results.StructuralInvariances

set_option linter.style.header false

/-!
# Exact head complexity of equality

Equality of two nonempty Boolean blocks is an affine level set after encoding
each block by binary weights.  A one-coordinate checkerboard restriction gives
the matching lower bound.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- The left block of a pair of `m`-bit strings. -/
def equalityLeftBlock {m : ℕ} (bits : Fin (m + m) → Bool) : Fin m → Bool :=
  fun i ↦ bits (Fin.castAdd m i)

/-- The right block of a pair of `m`-bit strings. -/
def equalityRightBlock {m : ℕ} (bits : Fin (m + m) → Bool) : Fin m → Bool :=
  fun i ↦ bits (Fin.natAdd m i)

/-- Equality of two adjacent `m`-bit blocks. -/
def equalityFn (m : ℕ) : (Fin (m + m) → Bool) → Bool :=
  fun bits ↦ decide (equalityLeftBlock bits = equalityRightBlock bits)

/-- Signed binary weights whose zero level is block equality. -/
noncomputable def equalityCoeffs (m : ℕ) : Fin (m + m) → ℝ :=
  Fin.addCases (fun i ↦ (2 : ℝ) ^ (i : ℕ))
    (fun i ↦ -((2 : ℝ) ^ (i : ℕ)))

theorem equality_affineValue (m : ℕ) (bits : Fin (m + m) → Bool) :
    affineValue 0 (equalityCoeffs m) bits =
      wT (fun i : Fin m ↦ (2 : ℝ) ^ (i : ℕ)) (equalityLeftBlock bits) -
        wT (fun i : Fin m ↦ (2 : ℝ) ^ (i : ℕ)) (equalityRightBlock bits) := by
  unfold affineValue equalityCoeffs equalityLeftBlock equalityRightBlock wT
  rw [Fin.sum_univ_add (a := m) (b := m)]
  simp only [Fin.addCases_left, Fin.addCases_right, zero_add]
  have hbool (r : ℝ) (b : Bool) :
      r * boolToReal b = if b = true then r else 0 := by
    cases b <;> simp [boolToReal]
  simp_rw [hbool]
  have hneg (b : Bool) (r : ℝ) :
      (if b = true then -r else 0) = -(if b = true then r else 0) := by
    cases b <;> simp
  simp_rw [hneg, Finset.sum_neg_distrib]
  ring

theorem equalityFn_eq_affineLevelSet (m : ℕ) :
    equalityFn m = affineSlab 0 (equalityCoeffs m) 0 0 := by
  funext bits
  simp only [equalityFn, affineSlab, decide_eq_decide]
  rw [equality_affineValue]
  have hinj := wT_two_pow_injective (n := m)
  constructor
  · intro h
    have hw :
        wT (fun i : Fin m ↦ (2 : ℝ) ^ (i : ℕ)) (equalityLeftBlock bits) =
          wT (fun i : Fin m ↦ (2 : ℝ) ^ (i : ℕ)) (equalityRightBlock bits) :=
      congrArg (wT (fun i : Fin m ↦ (2 : ℝ) ^ (i : ℕ))) h
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    apply hinj
    linarith

/-- Equality of two nonempty Boolean blocks has head complexity at most two. -/
theorem HStar_equality_le_two (m : ℕ) : HStar (m + m) (equalityFn m) ≤ 2 := by
  rw [equalityFn_eq_affineLevelSet]
  exact HStar_affineLevelSet_le_two 0 (equalityCoeffs m) 0

private def equalityBase (m : ℕ) : Fin (m + m) → Bool := fun _ ↦ false

private def equalityLeftIndex {m : ℕ} (hm : 0 < m) : Fin (m + m) :=
  Fin.castAdd m ⟨0, hm⟩

private def equalityRightIndex {m : ℕ} (hm : 0 < m) : Fin (m + m) :=
  Fin.natAdd m ⟨0, hm⟩

private theorem equalityIndices_ne {m : ℕ} (hm : 0 < m) :
    equalityLeftIndex hm ≠ equalityRightIndex hm := by
  intro h
  have hv := congrArg Fin.val h
  simp [equalityLeftIndex, equalityRightIndex] at hv
  omega

private theorem complementEquality_checkerboard {m : ℕ} (hm : 0 < m) :
    let f := complementFn (equalityFn m)
    f (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
        (equalityRightIndex hm) (false, false)) = false ∧
    f (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
        (equalityRightIndex hm) (true, true)) = false ∧
    f (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
        (equalityRightIndex hm) (false, true)) = true ∧
    f (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
        (equalityRightIndex hm) (true, false)) = true := by
  dsimp only [complementFn, equalityFn]
  have hcast_nat (i j : Fin m) :
      Fin.castAdd m i ≠ Fin.natAdd m j := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hnat_cast (i j : Fin m) :
      Fin.natAdd m i ≠ Fin.castAdd m j := by
    exact Ne.symm (hcast_nat j i)
  have hleft (a b : Bool) :
      equalityLeftBlock
          (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
            (equalityRightIndex hm) (a, b)) =
        fun i ↦ if i = ⟨0, hm⟩ then a else false := by
    funext i
    by_cases hi : i = ⟨0, hm⟩
    · subst i
      simp [equalityLeftBlock, Head.restrictBits, equalityLeftIndex]
    · have hsame : Fin.castAdd m i ≠ equalityLeftIndex hm := by
        intro h
        apply hi
        apply Fin.ext
        simpa [equalityLeftIndex] using congrArg Fin.val h
      have hcross : Fin.castAdd m i ≠ equalityRightIndex hm := by
        simpa [equalityRightIndex] using hcast_nat i ⟨0, hm⟩
      simp [equalityLeftBlock, Head.restrictBits, equalityBase,
        hi, hsame, hcross]
  have hright (a b : Bool) :
      equalityRightBlock
          (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
            (equalityRightIndex hm) (a, b)) =
        fun i ↦ if i = ⟨0, hm⟩ then b else false := by
    funext i
    simp only [equalityRightBlock]
    by_cases hi : i = ⟨0, hm⟩
    · subst i
      have hcross : Fin.natAdd m ⟨0, hm⟩ ≠ equalityLeftIndex hm := by
        simpa [equalityLeftIndex] using hnat_cast ⟨0, hm⟩ ⟨0, hm⟩
      simp only [Head.restrictBits]
      rw [if_neg hcross]
      simp [equalityRightIndex]
    · have hsame : Fin.natAdd m i ≠ equalityRightIndex hm := by
        intro h
        apply hi
        apply Fin.ext
        simpa [equalityRightIndex] using congrArg Fin.val h
      have hcross : Fin.natAdd m i ≠ equalityLeftIndex hm := by
        simpa [equalityLeftIndex] using hnat_cast i ⟨0, hm⟩
      simp only [Head.restrictBits]
      rw [if_neg hcross, if_neg hsame, if_neg hi]
      rfl
  have heq (b : Bool) :
      equalityLeftBlock
          (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
            (equalityRightIndex hm) (b, b)) =
        equalityRightBlock
          (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
            (equalityRightIndex hm) (b, b)) := by
    rw [hleft, hright]
  have hne (a b : Bool) (hab : a ≠ b) :
      equalityLeftBlock
          (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
            (equalityRightIndex hm) (a, b)) ≠
        equalityRightBlock
          (Head.restrictBits (equalityBase m) (equalityLeftIndex hm)
            (equalityRightIndex hm) (a, b)) := by
    intro hEq
    rw [hleft, hright] at hEq
    have h0 : a = b := by
      simpa using congrFun hEq ⟨0, hm⟩
    exact hab h0
  simp [heq, hne]

/-- Equality of two nonempty Boolean blocks has exact head complexity two. -/
theorem HStar_equality (m : ℕ) (hm : 0 < m) :
    HStar (m + m) (equalityFn m) = 2 := by
  have hcb := complementEquality_checkerboard hm
  have hlowerComp : 2 ≤ HStar (m + m) (complementFn (equalityFn m)) :=
    checkerboard_restriction_HStar_ge_two
      (complementFn (equalityFn m)) (equalityBase m)
      (equalityLeftIndex hm) (equalityRightIndex hm) (equalityIndices_ne hm)
      hcb.1 hcb.2.1 hcb.2.2.1 hcb.2.2.2
  have hlower : 2 ≤ HStar (m + m) (equalityFn m) := by
    change 2 ≤ HStar (m + m) (fun x ↦ !(equalityFn m x)) at hlowerComp
    rw [HStar_complement] at hlowerComp
    exact hlowerComp
  exact Nat.le_antisymm (HStar_equality_le_two m) hlower

/-- Equality has threshold degree exactly two on every nonempty block. -/
theorem thresholdDeg_equality (m : ℕ) (hm : 0 < m) :
    thresholdDeg (equalityFn m) = 2 := by
  apply Nat.le_antisymm
  · exact (thresholdDeg_le_HStar (equalityFn m)).trans_eq (HStar_equality m hm)
  · by_contra hnot
    have hdeg : thresholdDeg (equalityFn m) ≤ 1 := by omega
    obtain ⟨P, hPdeg, hPsign⟩ := thresholdDeg_spec (equalityFn m)
    have hcert : ThresholdDegLE (equalityFn m) 1 :=
      ⟨P, hPdeg.trans hdeg, hPsign⟩
    have hltf : isLTF (equalityFn m) :=
      (ThresholdDegLE_one_iff_isLTF (equalityFn m)).1 hcert
    have hnonconst : ¬ ∀ x y, equalityFn m x = equalityFn m y := by
      intro hconst
      have hzero := (HStar_eq_zero_iff (equalityFn m)).2 hconst
      rw [HStar_equality m hm] at hzero
      omega
    have hone : HStar (m + m) (equalityFn m) = 1 :=
      (HStar_eq_one_iff (equalityFn m)).2 ⟨hnonconst, hltf⟩
    rw [HStar_equality m hm] at hone
    omega

end HeadComplexity
