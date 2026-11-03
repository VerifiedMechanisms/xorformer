import HeadComplexity.BooleanCube.BinaryEncoding
import HeadComplexity.Results.SyndromeCover

set_option linter.style.header false

/-! # Cartesian lifting of finite syndrome covers -/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {a r : ℕ}

/-- The binary linear map with the prescribed syndrome columns. -/
def syndromeLinear (column : Fin a → BinaryVector r) :
    BinaryVector a →ₗ[ZMod 2] BinaryVector r where
  toFun x := ∑ i, x i • column i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z x := by simp [Finset.smul_sum, mul_smul]

@[simp] theorem syndromeLinear_single (column : Fin a → BinaryVector r) (i : Fin a) :
    syndromeLinear column (Pi.single i 1) = column i := by
  classical
  simp [syndromeLinear, Pi.single_apply]

/-- A finite list of preimages for the standard basis proves surjectivity. -/
theorem syndromeLinear_surjective (column : Fin a → BinaryVector r)
    (preimage : Fin r → BinaryVector a)
    (checked : ∀ j, syndromeLinear column (preimage j) = Pi.single j 1) :
    Function.Surjective (syndromeLinear column) := by
  classical
  intro y
  refine ⟨∑ j, y j • preimage j, ?_⟩
  simp only [map_sum, map_smul, checked]
  funext j
  simp [Pi.single_apply]

/-- An additive cover in the finite syndrome space. -/
structure SyndromeRecipe (a r : ℕ) where
  column : Fin a → BinaryVector r
  surjective : Function.Surjective (syndromeLinear column)
  targets : Finset (BinaryVector r)
  covers : ∀ v, ∃ t ∈ targets, ∃ i, v = t + column i

namespace SyndromeRecipe

def toSyndromeCover (R : SyndromeRecipe a r) : SyndromeCover a (BinaryVector r) where
  syndrome := (syndromeLinear R.column).toAddMonoidHom
  surjective := R.surjective
  targets := R.targets
  covers := by simpa using R.covers

/-- Interpret a binary word as a binary-field vector. -/
def wordVector (s : ℕ) (word : Fin (2 ^ s)) : BinaryVector s :=
  binaryCubeEquiv s (cubeBits word)

@[simp] theorem wordVector_zero (s : ℕ) : wordVector s 0 = 0 := by
  funext i
  simp [wordVector, binaryCubeEquiv, binaryBitEquiv, cubeBits]

@[simp] theorem wordVector_cubeIndex (s : ℕ) (u : BinaryVector s) :
    wordVector s (cubeIndex ((binaryCubeEquiv s).symm u)) = u := by
  simp [wordVector]

def liftColumn (R : SyndromeRecipe a r) (s : ℕ) (i : Fin (a * 2 ^ s)) :
    BinaryVector r × BinaryVector s :=
  (R.column (finProdFinEquiv.symm i).1, wordVector s (finProdFinEquiv.symm i).2)

/-- The lifted linear map, with a product syndrome space. -/
def liftLinear (R : SyndromeRecipe a r) (s : ℕ) :
    BinaryVector (a * 2 ^ s) →ₗ[ZMod 2] (BinaryVector r × BinaryVector s) where
  toFun x := ∑ i, x i • R.liftColumn s i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z x := by simp [Finset.smul_sum, mul_smul]

@[simp] theorem liftLinear_single (R : SyndromeRecipe a r) (s : ℕ)
    (i : Fin a) (word : Fin (2 ^ s)) :
    R.liftLinear s (Pi.single (finProdFinEquiv (i, word)) 1) =
      (R.column i, wordVector s word) := by
  classical
  change (∑ j, (Pi.single (finProdFinEquiv (i, word)) 1 : BinaryVector (a * 2 ^ s)) j •
    R.liftColumn s j) = _
  rw [Finset.sum_eq_single (finProdFinEquiv (i, word))]
  · simp [liftColumn]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem liftLinear_surjective (R : SyndromeRecipe a r) (ha : 0 < a) (s : ℕ) :
    Function.Surjective (R.liftLinear s) := by
  classical
  have hbase (v : BinaryVector r) : ∃ x, R.liftLinear s x = (v, 0) := by
    obtain ⟨b, hb⟩ := R.surjective v
    refine ⟨∑ i : Fin a, b i • Pi.single (finProdFinEquiv (i, (0 : Fin (2 ^ s)))) 1, ?_⟩
    simp only [map_sum, map_smul, liftLinear_single, wordVector_zero]
    apply Prod.ext
    · change (AddMonoidHom.fst (BinaryVector r) (BinaryVector s))
        (∑ i : Fin a, (b i • R.column i, 0)) = v
      rw [map_sum]
      exact hb
    · change (AddMonoidHom.snd (BinaryVector r) (BinaryVector s))
        (∑ i : Fin a, (b i • R.column i, 0)) = 0
      rw [map_sum]
      simp
  have htail (u : BinaryVector s) : ∃ x, R.liftLinear s x = (0, u) := by
    let i : Fin a := ⟨0, ha⟩
    refine ⟨Pi.single (finProdFinEquiv (i, cubeIndex ((binaryCubeEquiv s).symm u))) 1 -
      Pi.single (finProdFinEquiv (i, (0 : Fin (2 ^ s)))) 1, ?_⟩
    simp
  rintro ⟨v, u⟩
  obtain ⟨x, hx⟩ := hbase v
  obtain ⟨y, hy⟩ := htail u
  exact ⟨x + y, by simp [hx, hy]⟩

/-- Cartesian product of the columns with every additional syndrome. -/
def lift (R : SyndromeRecipe a r) (ha : 0 < a) (s : ℕ) :
    SyndromeCover (a * 2 ^ s) (BinaryVector r × BinaryVector s) where
  syndrome := (R.liftLinear s).toAddMonoidHom
  surjective := R.liftLinear_surjective ha s
  targets := R.targets.image fun t ↦ (t, 0)
  covers := by
    classical
    rintro ⟨v, u⟩
    obtain ⟨t, ht, i, hi⟩ := R.covers v
    refine ⟨(t, 0), Finset.mem_image.mpr ⟨t, ht, rfl⟩,
      finProdFinEquiv (i, cubeIndex ((binaryCubeEquiv s).symm u)), ?_⟩
    simp only [LinearMap.toAddMonoidHom_coe, liftLinear_single, wordVector_cubeIndex]
    exact Prod.ext hi (by simp)

@[simp] theorem lift_targets_card (R : SyndromeRecipe a r) (ha : 0 < a) (s : ℕ) :
    (R.lift ha s).targets.card = R.targets.card := by
  classical
  exact Finset.card_image_of_injective _ (fun x y h ↦ congrArg Prod.fst h)

end SyndromeRecipe

end HeadComplexity
