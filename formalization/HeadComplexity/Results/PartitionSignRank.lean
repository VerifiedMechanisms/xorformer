import HeadComplexity.Polynomial.PartitionPolynomial
import HeadComplexity.Polynomial.PartitionDegreeRank
import HeadComplexity.Polynomial.SignRank
import HeadComplexity.Results.LowComplexity
import Mathlib.Data.Nat.Log

set_option linter.style.header false

/-!
# Partition sign-rank bounds from head complexity

The evaluation matrix of a strict cleared atom score realizes the Boolean sign
matrix of the target function.  Its affine tangent factorization gives rank at
most `2^(H+1)-2` for every nonempty `H`-head representation and every input
partition.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ} {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Sign rank of a Boolean function across the displayed coordinate
partition. -/
noncomputable def partitionSignRank (part : Fin n ≃ ι ⊕ κ)
    (f : (Fin n → Bool) → Bool) : ℕ :=
  signRank (partitionFunction part f)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A strict shifted atom score gives a strict realization of every partition
sign matrix. -/
theorem clearedAtomPartitionMatrix_strict
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ)
    (hscore : ∀ x : Fin n → Bool,
      if f x then 0 < c + ∑ h, (phi h).eval x
      else c + ∑ h, (phi h).eval x < 0) :
    StrictSignMatrix (polynomialPartitionMatrix part (clearedAtomPoly phi c))
      (partitionFunction part f) := by
  intro u v
  let x := mergePartitionBits part u v
  change if f x then
      0 < eval (cubePoint x) (clearedAtomPoly phi c)
    else eval (cubePoint x) (clearedAtomPoly phi c) < 0
  rw [clearedAtomPoly_eval]
  cases hfx : f x with
  | false =>
      have hs := hscore x
      rw [hfx] at hs
      exact mul_neg_of_pos_of_neg (atomDenProduct_eval_pos phi x)
        hs
  | true =>
      have hs := hscore x
      rw [hfx] at hs
      exact mul_pos (atomDenProduct_eval_pos phi x)
        hs

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A fixed-head computation has a strict cleared polynomial realization
across every coordinate partition. -/
private theorem exists_strict_clearedAtomPartitionMatrix
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n H f) :
    ∃ (phi : Fin H → FracAtom n) (c : ℝ),
      StrictSignMatrix
        (polynomialPartitionMatrix part (clearedAtomPoly phi c))
        (partitionFunction part f) := by
  classical
  obtain ⟨phi, c, hscore⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hf)
  exact ⟨phi, c, clearedAtomPartitionMatrix_strict part f phi c hscore⟩

omit [Fintype ι] in
/-- Every nonempty fixed-head computation bounds sign rank across every
partition by the tangent cap. -/
theorem partitionSignRank_le_of_computableWithHeadsN (hH : 0 < H)
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n H f) :
    partitionSignRank part f ≤ 2 ^ (H + 1) - 2 := by
  classical
  obtain ⟨phi, c, hstrict⟩ :=
    exists_strict_clearedAtomPartitionMatrix part f hf
  let M := polynomialPartitionMatrix part (clearedAtomPoly phi c)
  refine (signRank_le_of_strict hstrict).trans ?_
  have hrank := clearedAffinePartitionMatrix_rank_le hH part
    (FracAtom.affineFamily phi) c
  simpa [M, clearedAffinePartitionMatrix] using hrank

/-- The low-degree monomial factorization gives the left-side binomial cap
for every fixed-head computation. -/
theorem partitionSignRank_le_degree_left_of_computableWithHeadsN
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n H f) :
    partitionSignRank part f ≤
      ∑ k ∈ Finset.range (min H (Fintype.card ι) + 1),
        (Fintype.card ι).choose k := by
  classical
  obtain ⟨phi, c, hstrict⟩ :=
    exists_strict_clearedAtomPartitionMatrix part f hf
  refine (signRank_le_of_strict hstrict).trans ?_
  exact polynomialPartitionMatrix_rank_le_left part
    (clearedAtomPoly phi c) H (clearedAtomPoly_totalDegree_le phi c)

omit [Fintype ι] in
/-- The low-degree monomial factorization gives the right-side binomial cap
for every fixed-head computation. -/
theorem partitionSignRank_le_degree_right_of_computableWithHeadsN
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n H f) :
    partitionSignRank part f ≤
      ∑ k ∈ Finset.range (min H (Fintype.card κ) + 1),
        (Fintype.card κ).choose k := by
  classical
  obtain ⟨phi, c, hstrict⟩ :=
    exists_strict_clearedAtomPartitionMatrix part f hf
  refine (signRank_le_of_strict hstrict).trans ?_
  exact polynomialPartitionMatrix_rank_le_right part
    (clearedAtomPoly phi c) H (clearedAtomPoly_totalDegree_le phi c)

/-- Every nonempty fixed-head computation satisfies the tangent cap and both
degree-side binomial caps simultaneously. -/
theorem partitionSignRank_le_all_of_computableWithHeadsN (hH : 0 < H)
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n H f) :
    partitionSignRank part f ≤
      min (2 ^ (H + 1) - 2)
        (min
          (∑ k ∈ Finset.range (min H (Fintype.card ι) + 1),
            (Fintype.card ι).choose k)
          (∑ k ∈ Finset.range (min H (Fintype.card κ) + 1),
            (Fintype.card κ).choose k)) := by
  apply le_min
  · exact partitionSignRank_le_of_computableWithHeadsN hH part f hf
  · apply le_min
    · exact partitionSignRank_le_degree_left_of_computableWithHeadsN part f hf
    · exact partitionSignRank_le_degree_right_of_computableWithHeadsN part f hf

omit [Fintype ι] in
/-- **Theorem 28, tangent sign-rank cap.** For a nonconstant Boolean function,
every coordinate partition has sign rank at most `2^(HStar+1)-2`. -/
theorem partitionSignRank_le_tangent
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    partitionSignRank part f ≤ 2 ^ (HStar n f + 1) - 2 := by
  have hH : 0 < HStar n f := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnonconstant ((HStar_eq_zero_iff f).mp hzero)
  exact partitionSignRank_le_of_computableWithHeadsN hH part f
    (HStar_computable f)

/-- **Theorem 28, full partition sign-rank cap.** For a nonconstant Boolean
function, every coordinate partition satisfies the tangent cap and both
degree-side binomial caps. -/
theorem partitionSignRank_le_all
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    partitionSignRank part f ≤
      min (2 ^ (HStar n f + 1) - 2)
        (min
          (∑ k ∈ Finset.range
              (min (HStar n f) (Fintype.card ι) + 1),
            (Fintype.card ι).choose k)
          (∑ k ∈ Finset.range
              (min (HStar n f) (Fintype.card κ) + 1),
            (Fintype.card κ).choose k)) := by
  have hH : 0 < HStar n f := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnonconstant ((HStar_eq_zero_iff f).mp hzero)
  exact partitionSignRank_le_all_of_computableWithHeadsN hH part f
    (HStar_computable f)

omit [Fintype ι] in
/-- Exponential form of the sign-rank lower bound. -/
theorem partitionSignRank_add_two_le_pow_HStar
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    partitionSignRank part f + 2 ≤ 2 ^ (HStar n f + 1) := by
  have hbound := partitionSignRank_le_tangent part f hnonconstant
  have hH : 0 < HStar n f := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnonconstant ((HStar_eq_zero_iff f).mp hzero)
  have hpow : 2 ≤ 2 ^ (HStar n f + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2)
      (by omega : 1 ≤ HStar n f + 1)
  omega

omit [Fintype ι] in
/-- Ceiling-logarithm inversion of the tangent sign-rank cap. -/
theorem clog_partitionSignRank_sub_one_le_HStar
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    Nat.clog 2 (partitionSignRank part f + 2) - 1 ≤ HStar n f := by
  have hlog : Nat.clog 2 (partitionSignRank part f + 2) ≤ HStar n f + 1 :=
    (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).mpr
      (partitionSignRank_add_two_le_pow_HStar part f hnonconstant)
  omega

/-- The generic matrix-size screen for partition sign rank. -/
theorem partitionSignRank_le_partitionSize
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool) :
    partitionSignRank part f ≤
      min (2 ^ Fintype.card ι) (2 ^ Fintype.card κ) := by
  classical
  simpa [partitionSignRank, Fintype.card_fun, Fintype.card_bool] using
    signRank_le_min_card (partitionFunction part f)

/-- A tangent sign-rank certificate capable of ruling out `h` heads needs at
least `h + 1` coordinates on each side of the partition.  The assumption
`0 < h` is necessary for the stated exponent screen at `h = 0`. -/
theorem partition_min_side_screen {h : ℕ} (hh : 0 < h)
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hlarge : 2 ^ (h + 1) - 1 ≤ partitionSignRank part f) :
    h + 1 ≤ min (Fintype.card ι) (Fintype.card κ) := by
  have hsize := partitionSignRank_le_partitionSize part f
  apply le_min
  · by_contra hnot
    have hcard : Fintype.card ι ≤ h := by omega
    have hpowle : 2 ^ Fintype.card ι ≤ 2 ^ h :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hcard
    have htwo : 2 ≤ 2 ^ h := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hh
    have hchain : 2 ^ (h + 1) - 1 ≤ 2 ^ Fintype.card ι :=
      hlarge.trans (hsize.trans (min_le_left _ _))
    rw [pow_succ] at hchain
    omega
  · by_contra hnot
    have hcard : Fintype.card κ ≤ h := by omega
    have hpowle : 2 ^ Fintype.card κ ≤ 2 ^ h :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hcard
    have htwo : 2 ≤ 2 ^ h := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hh
    have hchain : 2 ^ (h + 1) - 1 ≤ 2 ^ Fintype.card κ :=
      hlarge.trans (hsize.trans (min_le_right _ _))
    rw [pow_succ] at hchain
    omega

omit [Fintype ι] in
/-- Consequently, a partition capable of the same `h`-head exclusion needs
at least `2h + 2` ambient input coordinates. -/
theorem partition_ambient_size_screen {h : ℕ} (hh : 0 < h)
    (part : Fin n ≃ ι ⊕ κ) (f : (Fin n → Bool) → Bool)
    (hlarge : 2 ^ (h + 1) - 1 ≤ partitionSignRank part f) :
    2 * h + 2 ≤ n := by
  letI := partitionLeftFintype part
  have hmin := partition_min_side_screen hh part f hlarge
  have hleft : h + 1 ≤ Fintype.card ι :=
    hmin.trans (min_le_left _ _)
  have hright : h + 1 ≤ Fintype.card κ :=
    hmin.trans (min_le_right _ _)
  have hcard : n = Fintype.card ι + Fintype.card κ := by
    simpa using Fintype.card_congr part
  omega

end HeadComplexity
