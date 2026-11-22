import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

set_option linter.style.header false

/-! Appending unused coordinates to a selected two-flip cover preserves the
cover and multiplies the number of centers by the size of the appended cube. -/
namespace HeadComplexity.PairCoverExtension

open Finset
open scoped symmDiff

variable {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def leftPart (x : Finset (I ⊕ J)) : Finset I :=
  Finset.univ.filter (fun i ↦ Sum.inl i ∈ x)

def rightPart (x : Finset (I ⊕ J)) : Finset J :=
  Finset.univ.filter (fun j ↦ Sum.inr j ∈ x)

def center (c : V → Finset I) (v : V × Finset J) : Finset (I ⊕ J) :=
  (c v.1).map ⟨Sum.inl, Sum.inl_injective⟩ ∪ v.2.map ⟨Sum.inr, Sum.inr_injective⟩

def owner (o : Finset I → V) (x : Finset (I ⊕ J)) : V × Finset J :=
  (o (leftPart x), rightPart x)

def pair (p : Finset I → Finset I) (x : Finset (I ⊕ J)) : Finset (I ⊕ J) :=
  (p (leftPart x)).map ⟨Sum.inl, Sum.inl_injective⟩

omit [Fintype J] in
theorem pair_card (p : Finset I → Finset I) (hp : ∀ x, (p x).card = 2)
    (x : Finset (I ⊕ J)) : (pair p x).card = 2 := by
  simp [pair, hp]

theorem target_pair (c : V → Finset I) (o : Finset I → V)
    (p : Finset I → Finset I) (htarget : ∀ x, x ∆ c (o x) = p x)
    (x : Finset (I ⊕ J)) : x ∆ center c (owner o x) = pair p x := by
  ext i
  rcases i with i | j
  · have h := Finset.ext_iff.mp (htarget (leftPart x)) i
    simpa [Finset.mem_symmDiff, leftPart, center, owner, pair] using h
  · simp [Finset.mem_symmDiff, center, owner, rightPart, pair]

omit [DecidableEq J] in
theorem center_card [Fintype V] :
    Fintype.card (V × Finset J) = Fintype.card V * 2 ^ Fintype.card J := by
  simp [Fintype.card_prod, Fintype.card_finset]

end HeadComplexity.PairCoverExtension
