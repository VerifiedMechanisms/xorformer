import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

set_option linter.style.header false

/-! An explicit open-neighborhood partition used in the auxiliary reciprocal
jet construction. No asymptotic head-complexity lower bound is asserted. -/
namespace HeadComplexity.OpenCodePartition

open Finset
open scoped BigOperators

abbrev Address (r : ℕ) := Fin r → ZMod 2
abbrev Word (r : ℕ) := Address r → ZMod 2

noncomputable def syndrome {r : ℕ} (x : Word r) : Address r :=
  ∑ g, x g • g

noncomputable def flip {r : ℕ} (x : Word r) (g : Address r) : Word r :=
  x + Pi.single g 1

theorem syndrome_add {r : ℕ} (x y : Word r) :
    syndrome (x + y) = syndrome x + syndrome y := by
  simp [syndrome, add_smul, Finset.sum_add_distrib]

theorem syndrome_single {r : ℕ} (g : Address r) :
    syndrome (Pi.single g 1) = g := by
  classical
  simp [syndrome, Pi.single_apply]

theorem syndrome_flip {r : ℕ} (x : Word r) (g : Address r) :
    syndrome (flip x g) = syndrome x + g := by
  rw [flip, syndrome_add, syndrome_single]

theorem flip_flip {r : ℕ} (x : Word r) (g : Address r) :
    flip (flip x g) g = x := by
  funext i
  simp only [flip, Pi.add_apply]
  exact CharTwo.add_cancel_right _ _

abbrev Code (r : ℕ) := {x : Word r // syndrome x = 0}

theorem repaired_syndrome {r : ℕ} (x : Word r) :
    syndrome (flip x (syndrome x)) = 0 := by
  rw [syndrome_flip]
  ext i
  exact CharTwo.add_self_eq_zero _

noncomputable def repair {r : ℕ} (x : Word r) : Code r :=
  ⟨flip x (syndrome x), repaired_syndrome x⟩

theorem repair_flip_code {r : ℕ} (c : Code r) (g : Address r) :
    repair (flip c.val g) = c := by
  apply Subtype.ext
  change flip (flip c.val g) (syndrome (flip c.val g)) = c.val
  rw [syndrome_flip, c.property, zero_add, flip_flip]

/-- Every word is uniquely a codeword with exactly one specified bit flipped. -/
noncomputable def openCodeEquiv (r : ℕ) : Word r ≃ Code r × Address r where
  toFun x := (repair x, syndrome x)
  invFun cg := flip cg.1.val cg.2
  left_inv x := flip_flip x (syndrome x)
  right_inv cg := by
    rcases cg with ⟨c, g⟩
    simp [repair_flip_code, syndrome_flip, c.property]

theorem flip_eq_iff {r : ℕ} (c d : Code r) (g h : Address r) :
    flip c.val g = flip d.val h ↔ c = d ∧ g = h := by
  constructor
  · intro he
    have he' : (c, g) = (d, h) := (openCodeEquiv r).symm.injective he
    exact Prod.mk.inj he'
  · rintro ⟨rfl, rfl⟩
    rfl

theorem card_code_mul (r : ℕ) :
    Fintype.card (Code r) * 2 ^ r = 2 ^ (2 ^ r) := by
  classical
  have h := Fintype.card_congr (openCodeEquiv r)
  simpa [Fintype.card_prod, Fintype.card_fun, ZMod.card] using h.symm

/-- Product partitions have a square number of points per center. -/
noncomputable def productOpenCodeEquiv (r : ℕ) :
    Word r × Word r ≃ (Code r × Code r) × (Address r × Address r) :=
  (Equiv.prodCongr (openCodeEquiv r) (openCodeEquiv r)).trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem card_product_code_mul (r : ℕ) :
    Fintype.card (Code r × Code r) * (2 ^ r) ^ 2 = 2 ^ (2 * 2 ^ r) := by
  classical
  rw [Fintype.card_prod]
  have h := card_code_mul r
  calc
    Fintype.card (Code r) * Fintype.card (Code r) * (2 ^ r) ^ 2 =
        (Fintype.card (Code r) * 2 ^ r) ^ 2 := by ring
    _ = (2 ^ (2 ^ r)) ^ 2 := by rw [h]
    _ = 2 ^ (2 * 2 ^ r) := by rw [← pow_mul]; congr 1; omega

end HeadComplexity.OpenCodePartition
