module

public import HeadComplexity.Data.Bool.Cube
public import Mathlib.Algebra.Ring.Parity

/-!
# Symmetric Boolean functions

A Boolean profile assigns a value to every possible Hamming weight. Its sign
changes are counted across adjacent weights. We use this description for parity,
thresholds, and exact counts.
-/

@[expose] public section

namespace HeadComplexity.BooleanFunction

variable {n : ℕ}

/-- Evaluate a Boolean profile at the Hamming weight of the input. -/
def symmetricFn (F : Fin (n + 1) → Bool) (x : Fin n → Bool) : Bool :=
  F ⟨Bool.hammingWeight x, Nat.lt_succ_of_le (by simpa using Bool.hammingWeight_le_card x)⟩

/-- At an input of known Hamming weight, a symmetric function takes the value of its profile at
that weight. -/
theorem symmetricFn_apply_of_hammingWeight_eq (F : Fin (n + 1) → Bool)
    {x : Fin n → Bool} {k : Fin (n + 1)} (hx : Bool.hammingWeight x = k.val) :
    symmetricFn F x = F k :=
  congrArg F (Fin.ext hx)

/-- The number of adjacent pairs of weights with different profile values. -/
def signChanges (F : Fin (n + 1) → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ F i.castSucc ≠ F i.succ).card

/-- There are at most as many profile changes as adjacent pairs of Hamming weights. -/
theorem signChanges_le (F : Fin (n + 1) → Bool) : signChanges F ≤ n := by
  simpa [signChanges] using
    Finset.card_filter_le Finset.univ (fun i : Fin n ↦ F i.castSucc ≠ F i.succ)

/-- A constant profile has no sign changes. -/
@[simp] theorem signChanges_const (b : Bool) : signChanges (fun _ : Fin (n + 1) ↦ b) = 0 := by
  simp [signChanges]

/-- The profile that is true at odd weights. -/
def parityProfile (n : ℕ) (k : Fin (n + 1)) : Bool := if Odd k.val then true else false

/-- Parity is true when the number of true input bits is odd. -/
def parity (n : ℕ) : (Fin n → Bool) → Bool := symmetricFn (parityProfile n)

/-- Parity is true exactly when the number of true input bits is odd. -/
@[simp] theorem parity_apply (x : Fin n → Bool) :
    parity n x = (if Odd (Bool.hammingWeight x) then true else false) :=
  rfl

/-- The parity profile changes at every adjacent pair of Hamming weights. -/
@[simp] theorem signChanges_parityProfile (n : ℕ) : signChanges (parityProfile n) = n := by
  rw [signChanges, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro i _
  simp only [parityProfile, Fin.val_castSucc, Fin.val_succ, Nat.odd_add_one]
  by_cases h : Odd i.val <;> simp [h]

/-- The profile that is true at weights at least `t`. -/
def thresholdProfile (n t : ℕ) (k : Fin (n + 1)) : Bool := if t ≤ k.val then true else false

/-- The Hamming-weight threshold at `t`. -/
def threshold (n t : ℕ) : (Fin n → Bool) → Bool := symmetricFn (thresholdProfile n t)

/-- The threshold function is true exactly when the Hamming weight reaches or exceeds the
threshold. -/
@[simp] theorem threshold_apply (t : ℕ) (x : Fin n → Bool) :
    threshold n t x = (if t ≤ Bool.hammingWeight x then true else false) :=
  rfl

/-- The profile that is true exactly at weight `t`. -/
def exactCountProfile (n t : ℕ) (k : Fin (n + 1)) : Bool := if k.val = t then true else false

/-- The predicate that exactly `t` of the input bits are true. -/
def exactCount (n t : ℕ) : (Fin n → Bool) → Bool := symmetricFn (exactCountProfile n t)

/-- The exact-count function is true exactly when the Hamming weight equals the prescribed
count. -/
@[simp] theorem exactCount_apply (t : ℕ) (x : Fin n → Bool) :
    exactCount n t x = (if Bool.hammingWeight x = t then true else false) :=
  rfl

/-- A threshold strictly above zero and at most the input length gives exactly one profile
change. -/
theorem signChanges_thresholdProfile {n t : ℕ} (ht : 0 < t) (htn : t ≤ n) :
    signChanges (thresholdProfile n t) = 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  suffices (Finset.univ.filter fun j : Fin n ↦
      thresholdProfile n (t + 1) j.castSucc ≠ thresholdProfile n (t + 1) j.succ) =
        {⟨t, htn⟩} by
    simp [signChanges, this]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    thresholdProfile, Fin.val_castSucc, Fin.val_succ, Nat.succ_le_succ_iff, Fin.ext_iff]
  rcases lt_trichotomy (j.val) t with hj | rfl | hj
  · simp [hj.not_ge, hj.ne, (hj.trans (Nat.lt_succ_self t)).not_ge]
  · simp
  · simp [hj.le, hj.ne', Nat.succ_le_of_lt hj]

/-- An exact count strictly between zero and the input length gives two profile changes. -/
theorem signChanges_exactCountProfile {n t : ℕ} (ht : 0 < t) (htn : t < n) :
    signChanges (exactCountProfile n t) = 2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  let i : Fin n := ⟨t, (Nat.lt_succ_self t).trans htn⟩
  let j : Fin n := ⟨t + 1, htn⟩
  suffices (Finset.univ.filter fun k : Fin n ↦
      exactCountProfile n (t + 1) k.castSucc ≠ exactCountProfile n (t + 1) k.succ) = {i, j} by
    simp [signChanges, this, i, j, Fin.ext_iff]
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, exactCountProfile, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff,
    Nat.succ.injEq, i, j]
  by_cases h : k.val = t <;> simp [h, or_comm]

end HeadComplexity.BooleanFunction
