import HeadComplexity.Model.Head

set_option linter.style.header false

/-!
# Partitions of Boolean-cube coordinates

A coordinate partition is represented by an equivalence from ambient
coordinates to a sum type.  This permits arbitrary, rather than only
contiguous, left and right blocks while keeping matrix row and column types
explicit.
-/

namespace HeadComplexity

variable {n : ℕ} {ι κ : Type*}

/-- The left block of a finite coordinate partition is finite. -/
@[reducible] noncomputable def partitionLeftFintype
    (part : Fin n ≃ ι ⊕ κ) : Fintype ι := by
  letI : Finite ι := Finite.of_injective
    (fun i ↦ part.symm (Sum.inl i))
    (fun _ _ hij ↦ Sum.inl_injective (part.symm.injective hij))
  exact Fintype.ofFinite ι

/-- The right block of a finite coordinate partition is finite. -/
@[reducible] noncomputable def partitionRightFintype
    (part : Fin n ≃ ι ⊕ κ) : Fintype κ := by
  letI : Finite κ := Finite.of_injective
    (fun j ↦ part.symm (Sum.inr j))
    (fun _ _ hij ↦ Sum.inr_injective (part.symm.injective hij))
  exact Fintype.ofFinite κ

/-- Merge left and right bit assignments according to a coordinate
partition. -/
def mergePartitionBits (part : Fin n ≃ ι ⊕ κ)
    (u : ι → Bool) (v : κ → Bool) : Fin n → Bool :=
  fun i ↦ match part i with
    | Sum.inl a => u a
    | Sum.inr b => v b

/-- Extract the left assignment from an ambient bit vector. -/
def leftPartitionBits (part : Fin n ≃ ι ⊕ κ)
    (x : Fin n → Bool) : ι → Bool :=
  fun a ↦ x (part.symm (Sum.inl a))

/-- Extract the right assignment from an ambient bit vector. -/
def rightPartitionBits (part : Fin n ≃ ι ⊕ κ)
    (x : Fin n → Bool) : κ → Bool :=
  fun b ↦ x (part.symm (Sum.inr b))

@[simp] theorem mergePartitionBits_left (part : Fin n ≃ ι ⊕ κ)
    (u : ι → Bool) (v : κ → Bool) (a : ι) :
    mergePartitionBits part u v (part.symm (Sum.inl a)) = u a := by
  simp [mergePartitionBits]

@[simp] theorem mergePartitionBits_right (part : Fin n ≃ ι ⊕ κ)
    (u : ι → Bool) (v : κ → Bool) (b : κ) :
    mergePartitionBits part u v (part.symm (Sum.inr b)) = v b := by
  simp [mergePartitionBits]

@[simp] theorem leftPartitionBits_merge (part : Fin n ≃ ι ⊕ κ)
    (u : ι → Bool) (v : κ → Bool) :
    leftPartitionBits part (mergePartitionBits part u v) = u := by
  funext a
  simp [leftPartitionBits]

@[simp] theorem rightPartitionBits_merge (part : Fin n ≃ ι ⊕ κ)
    (u : ι → Bool) (v : κ → Bool) :
    rightPartitionBits part (mergePartitionBits part u v) = v := by
  funext b
  simp [rightPartitionBits]

@[simp] theorem mergePartitionBits_split (part : Fin n ≃ ι ⊕ κ)
    (x : Fin n → Bool) :
    mergePartitionBits part (leftPartitionBits part x)
      (rightPartitionBits part x) = x := by
  funext i
  cases h : part i with
  | inl a =>
      have hi : part.symm (Sum.inl a) = i := by
        apply part.injective
        simp [h]
      simp [mergePartitionBits, leftPartitionBits, h, hi]
  | inr b =>
      have hi : part.symm (Sum.inr b) = i := by
        apply part.injective
        simp [h]
      simp [mergePartitionBits, rightPartitionBits, h, hi]

/-- View an ambient Boolean function as the communication matrix associated
with a coordinate partition. -/
def partitionFunction (part : Fin n ≃ ι ⊕ κ)
    (f : (Fin n → Bool) → Bool) : (ι → Bool) → (κ → Bool) → Bool :=
  fun u v ↦ f (mergePartitionBits part u v)

end HeadComplexity
