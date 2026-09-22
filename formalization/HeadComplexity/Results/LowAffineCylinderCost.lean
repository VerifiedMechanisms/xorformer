import HeadComplexity.Results.AffineCylinderThreshold

set_option linter.style.header false

/-!
# Exactness at affine-cylinder cost at most two

The affine-cylinder compiler gives the upper bound.  The universal zero- and
one-head characterizations then leave no room between two heads and a
nonconstant non-LTF.
-/

namespace HeadComplexity

variable {n : ℕ}

/-- A nonconstant non-LTF of affine-cylinder cost at most two has exact head
complexity two. -/
theorem HStar_eq_two_of_actc_le_two
    (f : (Fin n → Bool) → Bool) (hcost : actc f ≤ 2)
    (hnconst : ¬ (∀ x y, f x = f y)) (hnLTF : ¬ isLTF f) :
    HStar n f = 2 := by
  have hle : HStar n f ≤ 2 := (HStar_le_actc f).trans hcost
  have hne0 : HStar n f ≠ 0 :=
    fun h0 ↦ hnconst ((HStar_eq_zero_iff f).mp h0)
  have hne1 : HStar n f ≠ 1 :=
    fun h1 ↦ hnLTF ((HStar_eq_one_iff f).mp h1).2
  omega

/-- **Low affine-cylinder cost is exact.**  Under `actc f ≤ 2`, the universal
constant/LTF/neither trichotomy is exactly the `0/1/2` head trichotomy. -/
theorem HStar_low_actc_classification
    (f : (Fin n → Bool) → Bool) (hcost : actc f ≤ 2) :
    ((∀ x y, f x = f y) ∧ HStar n f = 0) ∨
      (¬ (∀ x y, f x = f y) ∧ isLTF f ∧ HStar n f = 1) ∨
      (¬ (∀ x y, f x = f y) ∧ ¬ isLTF f ∧ HStar n f = 2) := by
  by_cases hconst : ∀ x y, f x = f y
  · exact Or.inl ⟨hconst, (HStar_eq_zero_iff f).2 hconst⟩
  · by_cases hltf : isLTF f
    · exact Or.inr (Or.inl
        ⟨hconst, hltf, (HStar_eq_one_iff f).2 ⟨hconst, hltf⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hconst, hltf,
          HStar_eq_two_of_actc_le_two f hcost hconst hltf⟩)

/-- The exact-two consequence also applies when cylinder-threshold cost is at
most two. -/
theorem HStar_eq_two_of_ctc_le_two
    (f : (Fin n → Bool) → Bool) (hcost : ctc f ≤ 2)
    (hnconst : ¬ (∀ x y, f x = f y)) (hnLTF : ¬ isLTF f) :
    HStar n f = 2 :=
  HStar_eq_two_of_actc_le_two f ((actc_le_ctc f).trans hcost) hnconst hnLTF

/-- The exact-two consequence also applies when affine-free PTF sparsity is at
most two. -/
theorem HStar_eq_two_of_affineFreeSparsity_le_two
    (f : (Fin n → Bool) → Bool) (hcost : affineFreeSparsity f ≤ 2)
    (hnconst : ¬ (∀ x y, f x = f y)) (hnLTF : ¬ isLTF f) :
    HStar n f = 2 :=
  HStar_eq_two_of_actc_le_two f
    ((actc_le_affineFreeSparsity f).trans hcost) hnconst hnLTF

end HeadComplexity
