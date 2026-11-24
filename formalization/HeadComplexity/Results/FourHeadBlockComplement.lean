import HeadComplexity.Results.FourHeadCrossOnlyPattern

set_option linter.style.header false

/-!
# Four-head local lower bounds after complementing one coordinate block

Vanilla denominator directions remain uniformly signed within each block.
Their signs may differ between the two blocks: independently orienting the
two factors in the cross-matrix argument preserves its obstruction.
-/

namespace HeadComplexity.FourHeadBlockComplement

noncomputable section

open Finset PureRoPEThreeHead FourHeadLocalPattern
open scoped BigOperators

def flipY (z : Fin 16 → Bool) : Fin 16 → Bool :=
  assemble (fun i ↦ z (left i)) (fun i ↦ !(z (right i)))

def fullFlipY (x : Fin 17 → Bool) : Fin 17 → Bool :=
  join (x 16) (flipY (fun i ↦ x (i.castAdd 1)))

def flipVector (u : Fin 16 → ℝ) : Fin 16 → ℝ :=
  ![u 0, -u 1, u 2, -u 3, u 4, -u 5, u 6, -u 7,
    u 8, -u 9, u 10, -u 11, u 12, -u 13, u 14, -u 15]

theorem flipVector_left (u : Fin 16 → ℝ) (i : Fin 8) :
    flipVector u (left i) = u (left i) := by fin_cases i <;> rfl

theorem flipVector_right (u : Fin 16 → ℝ) (i : Fin 8) :
    flipVector u (right i) = -u (right i) := by fin_cases i <;> rfl

theorem linear_flipY (u : Fin 16 → ℝ) (z : Fin 16 → Bool) :
    linear u (flipY z) = linear (flipVector u) z := by
  have hs (b : Bool) : spin (!b) = -spin b := by cases b <;> norm_num [spin]
  simp [linear, flipY, assemble, flipVector, left, right, Fin.sum_univ_succ, hs]

theorem productScore_flipY (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ) (z : Fin 16 → Bool) :
    productScore q A B (flipY z) =
      productScore q (fun h ↦ flipVector (A h)) (fun h ↦ flipVector (B h)) z := by
  simp only [productScore, linear_flipY]

theorem flipY_flip (z : Fin 16 → Bool) : flipY (flip z) = flip (flipY z) := by
  funext i
  fin_cases i <;> simp [flipY, assemble, left, right, PureRoPEThreeHead.flip]

theorem fullFlipY_join (t : Bool) (z : Fin 16 → Bool) :
    fullFlipY (join t z) = join t (flipY z) := by
  have hlast : join t z 16 = t := rfl
  have hrest : (fun i : Fin 16 ↦ join t z (i.castAdd 1)) = z := by
    funext i
    exact Fin.append_left z (fun _ : Fin 1 ↦ t) i
  simp only [fullFlipY, hlast, hrest]

theorem orbitLabel_flipY (f : (Fin 17 → Bool) → Bool) (z : Fin 16 → Bool) (b : Bool)
    (h : OrbitLabel (fun x ↦ f (fullFlipY x)) z b) : OrbitLabel f (flipY z) b := by
  simpa only [OrbitLabel, fullFlipY_join, flipY_flip] using h

theorem cross_obstruction (A B : Fin 4 → Fin 16 → ℝ)
    (hL : ∀ h, (∀ i, 0 < B h (left i)) ∨ (∀ i, B h (left i) = 0))
    (hR : ∀ h, (∀ i, B h (right i) < 0) ∨ (∀ i, B h (right i) = 0))
    (hoff : ∀ i j : Fin 8, i ≠ j → crossCoefficient A B i j ≤ 0)
    (hcol : ∀ j, 0 < ∑ i, crossCoefficient A B i j) : False := by
  apply PositiveHalfRankCross.obstruction
    (fun h i ↦ -A h (left i)) (fun h i ↦ B h (left i))
    (fun h j ↦ A h (right j)) (fun h j ↦ -B h (right j)) hL
  · intro h
    rcases hR h with hn | hz
    · exact Or.inl (fun i ↦ neg_pos.mpr (hn i))
    · exact Or.inr (fun i ↦ by rw [hz i, neg_zero])
  · simpa only [crossCoefficient, neg_mul_neg] using hoff
  · simpa only [crossCoefficient, neg_mul_neg] using hcol

theorem quadratic_obstruction (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ)
    (hL : ∀ h, (∀ i, 0 < B h (left i)) ∨ (∀ i, B h (left i) = 0))
    (hR : ∀ h, (∀ i, B h (right i) < 0) ∨ (∀ i, B h (right i) = 0))
    (hz : productScore q A B zeroInput < 0)
    (hs : ∀ i, 0 < productScore q A B (singleInput i))
    (hc : ∀ i j : Fin 8, i ≠ j → productScore q A B (doubleInput (left i) (right j)) < 0)
    (hp : ∀ i j : Fin 8, i ≠ j → productScore q A B (doubleInput (right i) (right j)) < 0) :
    False := by
  apply cross_obstruction A B hL hR
  · intro i j hij
    have hidx : left i ≠ right j := by fin_cases i <;> fin_cases j <;> decide
    have he := product_face_difference q A B (left i) (right j) hidx
    change (∑ h, (A h (left i) * B h (right j) + B h (left i) * A h (right j))) ≤ 0
    linarith [hs (left i), hs (right j), hc i j hij]
  · intro j
    have he := column_identity q A B j
    have hsum : 0 ≤ ∑ k : Fin 8, if k = j then 0 else
        productScore q A B (singleInput (right k)) -
          productScore q A B (doubleInput (right j) (right k)) := by
      apply Finset.sum_nonneg
      intro k _
      split_ifs with h
      · exact le_refl 0
      · linarith [hs (right k), hp j k (Ne.symm h)]
    linarith [hs (right j)]

theorem quadratic_crossOnly_obstruction (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ)
    (hL : ∀ h, (∀ i, 0 < B h (left i)) ∨ (∀ i, B h (left i) = 0))
    (hR : ∀ h, (∀ i, B h (right i) < 0) ∨ (∀ i, B h (right i) = 0))
    (hz : productScore q A B zeroInput < 0)
    (hs : ∀ i, 0 < productScore q A B (singleInput i))
    (hc : ∀ i j : Fin 8, i ≠ j → productScore q A B (doubleInput (left i) (right j)) < 0)
    (hm : ∀ j s, productScore q A B (middleInput j s true) < 0 ∧
      0 < productScore q A B (middleInput j s false)) : False := by
  apply cross_obstruction A B hL hR
  · intro i j hij
    have hidx : left i ≠ right j := by fin_cases i <;> fin_cases j <;> decide
    have he := product_face_difference q A B (left i) (right j) hidx
    change (∑ h, (A h (left i) * B h (right j) + B h (left i) * A h (right j))) ≤ 0
    linarith [hs (left i), hs (right j), hc i j hij]
  · intro j
    have he := middle_difference q A B j
    linarith [(hm j true).1, (hm j true).2, (hm j false).1, (hm j false).2]

theorem exists_flipped_quadratic (r : Fin 4 → AffineFraction 17) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) :
    ∃ q A B,
      (∀ h, (∀ i, 0 < B h (left i)) ∨ (∀ i, B h (left i) = 0)) ∧
      (∀ h, (∀ i, B h (right i) < 0) ∨ (∀ i, B h (right i) = 0)) ∧
      ∀ z, extractedFunction r c (flipY z) = productScore q A B z := by
  obtain ⟨q, A, B, hB, hq⟩ := exists_quadratic r c hr
  obtain ⟨A', B', hB', ho⟩ := orient_quadratic q A B hB
  refine ⟨q, fun h ↦ flipVector (A' h), fun h ↦ flipVector (B' h), ?_, ?_, ?_⟩
  · intro h
    simpa only [flipVector_left] using (hB' h).imp
      (fun hp i ↦ hp (left i)) (fun hz i ↦ hz (left i))
  · intro h
    rcases hB' h with hp | hz
    · refine Or.inl (fun i ↦ ?_)
      change flipVector (B' h) (right i) < 0
      rw [flipVector_right]
      exact neg_neg_of_pos (hp _)
    · refine Or.inr (fun i ↦ ?_)
      change flipVector (B' h) (right i) = 0
      rw [flipVector_right, hz, neg_zero]
  · intro z
    rw [hq, ho, productScore_flipY]

theorem not_computable_four (f : (Fin 17 → Bool) → Bool)
    (hf : LocalPattern (fun x ↦ f (fullFlipY x))) : ¬ computableWithHeadsN 17 4 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 4 f).mp hc
  obtain ⟨q, A, B, hL, hR, hq⟩ := exists_flipped_quadratic r c hr
  obtain ⟨hz, hs, hcross, hp⟩ := hf
  apply quadratic_obstruction q A B hL hR
  · rw [← hq]
    exact extractedFunction_negative r c hr f hsign _ (orbitLabel_flipY f _ _ hz)
  · intro i
    rw [← hq]
    exact extractedFunction_positive r c hr f hsign _ (orbitLabel_flipY f _ _ (hs i))
  · intro i j hij
    rw [← hq]
    exact extractedFunction_negative r c hr f hsign _
      (orbitLabel_flipY f _ _ (hcross i j hij))
  · intro i j hij
    rw [← hq]
    exact extractedFunction_negative r c hr f hsign _
      (orbitLabel_flipY f _ _ (hp i j hij))

theorem crossOnly_not_computable_four (f : (Fin 17 → Bool) → Bool)
    (hf : CrossOnlyPattern (fun x ↦ f (fullFlipY x))) : ¬ computableWithHeadsN 17 4 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 4 f).mp hc
  obtain ⟨q, A, B, hL, hR, hq⟩ := exists_flipped_quadratic r c hr
  obtain ⟨hz, hs, hcross, hm⟩ := hf
  apply quadratic_crossOnly_obstruction q A B hL hR
  · rw [← hq]
    exact extractedFunction_negative r c hr f hsign _ (orbitLabel_flipY f _ _ hz)
  · intro i
    rw [← hq]
    exact extractedFunction_positive r c hr f hsign _ (orbitLabel_flipY f _ _ (hs i))
  · intro i j hij
    rw [← hq]
    exact extractedFunction_negative r c hr f hsign _
      (orbitLabel_flipY f _ _ (hcross i j hij))
  · intro j s
    constructor
    · rw [← hq]
      exact extractedFunction_negative r c hr f hsign _
        (orbitLabel_flipY f _ _ (hm j s).1)
    · rw [← hq]
      exact extractedFunction_positive r c hr f hsign _
        (orbitLabel_flipY f _ _ (hm j s).2)

theorem HStar_ge_five (f : (Fin 17 → Bool) → Bool)
    (hf : LocalPattern (fun x ↦ f (fullFlipY x))) : 5 ≤ HStar 17 f := by
  by_contra h
  have hle : HStar 17 f ≤ 4 := by omega
  apply not_computable_four f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 4 f).mpr
  exact affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

theorem crossOnly_HStar_ge_five (f : (Fin 17 → Bool) → Bool)
    (hf : CrossOnlyPattern (fun x ↦ f (fullFlipY x))) : 5 ≤ HStar 17 f := by
  by_contra h
  have hle : HStar 17 f ≤ 4 := by omega
  apply crossOnly_not_computable_four f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 4 f).mpr
  exact affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

end

end HeadComplexity.FourHeadBlockComplement
