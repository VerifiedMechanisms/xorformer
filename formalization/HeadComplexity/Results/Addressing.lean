import HeadComplexity.BooleanCube.BinaryEncoding
import HeadComplexity.Polynomial.AffineSubstitution
import HeadComplexity.Results.IntegralClearedCertificate
import HeadComplexity.Results.OneBitGateThresholdDegree

set_option linter.style.header false

/-!
# Addressing functions

The first `r` inputs specify a little-endian address into the remaining `2^r`
data inputs. Affine identification with a fresh parity bit proves the general
threshold-degree lower bound. Small exact head counts use integral certificates.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

/-- The data bit selected by the first `r` input bits. -/
def IDX (r : ℕ) (bits : Fin (r + 2 ^ r) → Bool) : Bool :=
  bits (Fin.natAdd r (cubeIndex (fun i ↦ bits (Fin.castAdd (2 ^ r) i))))

/-- Identify each data input with the fresh bit or its complement according
to the parity of that data input's address. -/
def addressParitySubstitution (r : ℕ) (bits : Fin (r + 1) → Bool) :
    Fin (r + 2 ^ r) → Bool :=
  Fin.addCases (fun i ↦ bits i.succ)
    (fun word ↦ xor (bits 0) (PARITY r (cubeBits word)))

theorem IDX_addressParitySubstitution (r : ℕ) :
    (fun bits ↦ IDX r (addressParitySubstitution r bits)) = freshXor (PARITY r) := by
  funext bits
  simp [IDX, addressParitySubstitution, freshXor, freshBitGate]
  rfl

/-- Affine real interpolants for the parity-identification coordinates. -/
noncomputable def addressParityPolynomial (r : ℕ) :
    Fin (r + 2 ^ r) → MvPolynomial (Fin (r + 1)) ℝ :=
  Fin.addCases (fun i ↦ X i.succ)
    (fun word ↦ if PARITY r (cubeBits word) then 1 - X 0 else X 0)

theorem addressParityPolynomial_degree (r : ℕ) (i : Fin (r + 2 ^ r)) :
    (addressParityPolynomial r i).totalDegree ≤ 1 := by
  refine Fin.addCases (fun _ ↦ ?_) (fun word ↦ ?_) i
  · simp [addressParityPolynomial]
  · simp only [addressParityPolynomial, Fin.addCases_right]
    split
    · exact (totalDegree_sub _ _).trans (by simp)
    · simp

theorem addressParityPolynomial_eval (r : ℕ) (bits : Fin (r + 1) → Bool)
    (i : Fin (r + 2 ^ r)) :
    eval (cubePoint bits) (addressParityPolynomial r i) =
      boolToReal (addressParitySubstitution r bits i) := by
  refine Fin.addCases (fun _ ↦ ?_) (fun word ↦ ?_) i
  · simp [addressParityPolynomial, addressParitySubstitution, cubePoint]
  · cases hp : PARITY r (cubeBits word) <;> cases hb : bits 0 <;>
      simp [addressParityPolynomial, addressParitySubstitution, cubePoint, boolToReal, hp, hb]

/-- Addressing contains parity on `r+1` variables under an affine substitution. -/
theorem addressCount_succ_le_thresholdDeg (r : ℕ) :
    r + 1 ≤ thresholdDeg (IDX r) := by
  have h := (thresholdDeg_spec (IDX r)).affineSubstitution
    (addressParitySubstitution r) (addressParityPolynomial r)
    (addressParityPolynomial_degree r) (addressParityPolynomial_eval r)
  rw [IDX_addressParitySubstitution] at h
  have hdeg := thresholdDeg_le_of_ThresholdDegLE h
  simpa [thresholdDeg_freshXor, thresholdDeg_parity] using hdeg

theorem addressCount_succ_le_HStar (r : ℕ) :
    r + 1 ≤ HStar (r + 2 ^ r) (IDX r) :=
  (addressCount_succ_le_thresholdDeg r).trans (thresholdDeg_le_HStar (IDX r))

/-- The multilinear indicator of one address. -/
noncomputable def addressSelector (r : ℕ) (word : Fin (2 ^ r)) :
    MvPolynomial (Fin (r + 2 ^ r)) ℝ :=
  ∏ i : Fin r, if cubeBits word i then X (Fin.castAdd (2 ^ r) i)
    else 1 - X (Fin.castAdd (2 ^ r) i)

theorem addressSelector_eval (r : ℕ) (word : Fin (2 ^ r))
    (bits : Fin (r + 2 ^ r) → Bool) :
    eval (cubePoint bits) (addressSelector r word) =
      if word = cubeIndex (fun i ↦ bits (Fin.castAdd (2 ^ r) i)) then 1 else 0 := by
  classical
  rw [addressSelector, map_prod]
  let address : Fin r → Bool := fun i ↦ bits (Fin.castAdd (2 ^ r) i)
  by_cases heq : word = cubeIndex address
  · subst word
    rw [ite_eq_left rfl]
    apply Finset.prod_eq_one
    intro i _
    cases hi : address i <;>
      simp [cubeBits_cubeIndex, address, cubePoint, boolToReal, hi]
  · rw [ite_eq_right heq]
    have hne : cubeBits word ≠ address := by
      intro h
      exact heq (by rw [← cubeIndex_cubeBits word, h])
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hw : cubeBits word i <;> cases hb : address i <;>
      simp_all [cubePoint, boolToReal, address]

theorem addressSelector_degree (r : ℕ) (word : Fin (2 ^ r)) :
    (addressSelector r word).totalDegree ≤ r := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin r, 1 := Finset.sum_le_sum fun i _ ↦ by
      split
      · simp
      · exact (totalDegree_sub _ _).trans (by simp)
    _ = r := by simp

/-- Exact selector score, before taking its threshold. -/
noncomputable def addressScorePolynomial (r : ℕ) :
    MvPolynomial (Fin (r + 2 ^ r)) ℝ :=
  C 2 * (∑ word : Fin (2 ^ r), X (Fin.natAdd r word) * addressSelector r word) - 1

theorem addressScorePolynomial_eval (r : ℕ) (bits : Fin (r + 2 ^ r) → Bool) :
    eval (cubePoint bits) (addressScorePolynomial r) = 2 * boolToReal (IDX r bits) - 1 := by
  classical
  simp only [addressScorePolynomial, map_sub, map_mul, eval_C, map_one, map_sum,
    eval_X, addressSelector_eval]
  simp [IDX, cubePoint]

theorem IDX_thresholdDegLE (r : ℕ) : ThresholdDegLE (IDX r) (r + 1) := by
  refine ⟨addressScorePolynomial r, ?_, fun bits ↦ ?_⟩
  · refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    apply totalDegree_finsetSum_le
    intro word _
    exact (totalDegree_mul _ _).trans (by
      simpa [Nat.add_comm] using Nat.add_le_add_left (addressSelector_degree r word) 1)
  · rw [addressScorePolynomial_eval]
    cases IDX r bits <;> simp [boolToReal]

theorem thresholdDeg_IDX (r : ℕ) : thresholdDeg (IDX r) = r + 1 :=
  Nat.le_antisymm (thresholdDeg_le_of_ThresholdDegLE (IDX_thresholdDegLE r))
    (addressCount_succ_le_thresholdDeg r)

end HeadComplexity
