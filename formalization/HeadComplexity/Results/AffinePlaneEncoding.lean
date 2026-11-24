import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-field tokens for affine-plane bit decoders

One field element stores one Boolean word.  A finite row set embeds into
point/bit pairs, and every Boolean table therefore has a token assignment at
each affine-plane point and memory column.  No algebraic structure is used in
the encoding lemma itself; the finite-field instance is supplied separately.
-/

namespace HeadComplexity
namespace AxisZeroGluing

universe u

/-- A field-sized alphabet of cardinality `2^a` stores exactly `a` bits. -/
noncomputable def affinePlaneBinaryEquiv (F : Type u) [Fintype F] {a : ℕ}
    (hcard : Fintype.card F = 2 ^ a) : F ≃ (Fin a → Bool) :=
  Fintype.equivOfCardEq (by simp [hcard])

/-- The point/bit pairs have the row capacity used in the asymptotic bound. -/
theorem affinePlaneRow_card (F : Type u) [Fintype F] {a : ℕ}
    (hcard : Fintype.card F = 2 ^ a) :
    Fintype.card ((F × F) × Fin a) = a * 4 ^ a := by
  simp only [Fintype.card_prod, Fintype.card_fin, hcard]
  rw [← mul_pow]
  norm_num
  ring

/-- Restrict a full affine-plane decoder to any smaller requested row count. -/
noncomputable def affinePlaneRowEmbedding (F : Type u) [Fintype F] {a r : ℕ}
    (hcard : Fintype.card F = 2 ^ a) (hr : r ≤ a * 4 ^ a) :
    Fin r ↪ ((F × F) × Fin a) :=
  (Fin.castLEEmb hr).trans
    (Fintype.equivFinOfCardEq (affinePlaneRow_card F hcard)).symm.toEmbedding

/-- Extend the requested labels to every point/bit pair and encode the resulting
word by a single token. -/
theorem exists_affinePlane_tokens {F : Type u} {a r s : ℕ}
    (decode : F ≃ (Fin a → Bool)) (row : Fin r ↪ ((F × F) × Fin a))
    (table : Fin r → Fin s → Bool) :
    ∃ code : (F × F) → Fin s → F,
      ∀ i j, decode (code (row i).1 j) (row i).2 = table i j := by
  classical
  let full : ((F × F) × Fin a) → Fin s → Bool :=
    fun p j ↦ Function.extend row (fun i ↦ table i j) (fun _ ↦ false) p
  let code : (F × F) → Fin s → F :=
    fun p j ↦ decode.symm (fun b ↦ full (p, b) j)
  refine ⟨code, ?_⟩
  intro i j
  simp only [code, Equiv.apply_symm_apply]
  change Function.extend row (fun i ↦ table i j) (fun _ ↦ false) (row i) = _
  exact row.injective.extend_apply _ _ _

/-- Combined generic finite encoding interface for the decoder assembly. -/
theorem exists_affinePlane_encoding (F : Type u) [Fintype F] {a r s : ℕ}
    (hcard : Fintype.card F = 2 ^ a) (hr : r ≤ a * 4 ^ a)
    (table : Fin r → Fin s → Bool) :
    ∃ (row : Fin r ↪ ((F × F) × Fin a)) (decode : F ≃ (Fin a → Bool))
      (code : (F × F) → Fin s → F),
      ∀ i j, decode (code (row i).1 j) (row i).2 = table i j := by
  let row := affinePlaneRowEmbedding F hcard hr
  let decode := affinePlaneBinaryEquiv F hcard
  obtain ⟨code, hc⟩ := exists_affinePlane_tokens decode row table
  exact ⟨row, decode, code, hc⟩

/-- A field of the required binary alphabet size exists in every positive
dimension, using mathlib's splitting-field construction. -/
abbrev BinaryGaloisField (a : ℕ) := GaloisField 2 a

noncomputable instance binaryGaloisFieldFintype (a : ℕ) :
    Fintype (BinaryGaloisField a) := Fintype.ofFinite _

theorem binaryGaloisField_card {a : ℕ} (ha : 1 ≤ a) :
    Fintype.card (BinaryGaloisField a) = 2 ^ a := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 a (by omega)

end AxisZeroGluing
end HeadComplexity
