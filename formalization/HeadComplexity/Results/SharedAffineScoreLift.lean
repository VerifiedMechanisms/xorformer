import HeadComplexity.Results.SharedAffineFractionLift
import HeadComplexity.Atoms.UniformApproximation

set_option linter.style.header false

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n M : ℕ}

/-- The two nonnegative parts of the shape statistic on the Boolean cube. -/
private theorem shape_parts (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (bits : Fin n → Bool) :
    0 ≤ affineValue 0 p bits ∧
      0 ≤ (∑ i, p i) - affineValue 0 p bits := by
  constructor
  · simp only [affineValue, zero_add]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i).le (boolToReal_nonneg _)
  · have hle : affineValue 0 p bits ≤ ∑ i, p i := by
      simp only [affineValue, zero_add]
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_of_le_one_right (hp i).le (boolToReal_le_one _)
    linarith

/-- A score chart that includes the orientation-crossing limit. The final
affine term must be charged as one additional head. -/
noncomputable def sharedAffineScore (c : ℝ) (cs : Fin n → ℝ)
    (a₀ : Fin M → ℝ) (a p : Fin M → Fin n → ℝ) (q : Fin M → ℝ)
    (bits : Fin n → Bool) : ℝ :=
  affineValue c cs bits + ∑ h, affineValue (a₀ h) (a h) bits *
    orientationCrossingFeature (q h) (affineValue 0 (p h) bits)
      ((∑ i, p h i) - affineValue 0 (p h) bits)

/-- Away from the crossing, each rational remainder is an actual fractional
atom. The affine correction is kept outside this atom. -/
private theorem exists_orientation_remainder_atom
    (a₀ : ℝ) (a p : Fin n → ℝ) (q : ℝ)
    (hp : ∀ i, 0 < p i) (hP : 0 < ∑ i, p i)
    (hq : 0 < q) (hone : q ≠ 1) :
    ∃ φ : FracAtom n, ∀ bits,
      affineValue a₀ a bits * orientationCrossingFeature q
        (affineValue 0 p bits) ((∑ i, p i) - affineValue 0 p bits) =
      (2 * q / (q ^ 2 - 1)) * affineValue a₀ a bits + φ.eval bits := by
  let P := ∑ i, p i
  let k := -(q * P / (q - 1))
  have hex : ∃ φ : FracAtom n, ∀ bits,
      φ.eval bits = affineValue (k * a₀) (fun i ↦ k * a i) bits /
        affineValue P (fun i ↦ (q - 1) * p i) bits := by
    rcases lt_or_gt_of_ne hone with hlt | hgt
    · have hb : ∀ i, (q - 1) * p i < 0 := fun i ↦ mul_neg_of_neg_of_pos
        (by linarith) (hp i)
      have hm : (∑ i, -((q - 1) * p i)) < P := by
        have he : (∑ i, -((q - 1) * p i)) = (1 - q) * P := by
          simp only [P, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [he]
        have hqP : 0 < q * P := mul_pos hq hP
        nlinarith
      exact ⟨FracAtom.ofNegativeAffineRatio (k * a₀) (fun i ↦ k * a i)
        P (fun i ↦ (q - 1) * p i) hP hb hm,
        fun bits ↦ FracAtom.ofNegativeAffineRatio_eval _ _ _ _ _ _ _ bits⟩
    · have hb : ∀ i, 0 < (q - 1) * p i := fun i ↦ mul_pos
        (by linarith) (hp i)
      exact ⟨FracAtom.ofPositiveAffineRatio (k * a₀) (fun i ↦ k * a i)
        P (fun i ↦ (q - 1) * p i) hP hb,
        fun bits ↦ FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ bits⟩
  obtain ⟨φ, hφ⟩ := hex
  refine ⟨φ, fun bits ↦ ?_⟩
  let t := affineValue 0 p bits
  have ht := shape_parts p hp bits
  have hB : 0 < q * t + (P - t) := by
    by_cases hz : t = 0
    · simpa [hz] using hP
    · exact add_pos_of_pos_of_nonneg (mul_pos hq
        (lt_of_le_of_ne ht.1 (Ne.symm hz))) ht.2
  have hden : affineValue P (fun i ↦ (q - 1) * p i) bits =
      q * t + (P - t) := by
    dsimp [affineValue, t]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [hφ, affineValue_smul, hden,
    orientationCrossingFeature_decomposition q t (P - t) hq hone hB.ne']
  dsimp [k]
  have hs : q ^ 2 - 1 ≠ 0 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hone) (by positivity)
  field_simp [sub_ne_zero.mpr hone, hB.ne', hs]
  ring

/-- A strict score in the chart, with no unit exactly at the crossing,
computes its Boolean predicate with one more head than chart units. This
uses the existing one-atom affine approximation theorem, rather than an
unavailable exact constant-denominator realization. -/
theorem computableWithHeadsN_of_sharedAffineScore_nonzero
    (c : ℝ) (cs : Fin n → ℝ) (a₀ : Fin M → ℝ)
    (a p : Fin M → Fin n → ℝ) (q : Fin M → ℝ)
    (hp : ∀ h i, 0 < p h i) (hP : ∀ h, 0 < ∑ i, p h i)
    (hq : ∀ h, 0 < q h) (hone : ∀ h, q h ≠ 1)
    (f : (Fin n → Bool) → Bool)
    (hstrict : StrictSignRepresentsScore (sharedAffineScore c cs a₀ a p q) f) :
    computableWithHeadsN n (M + 1) f := by
  classical
  choose φ hφ using fun h ↦ exists_orientation_remainder_atom
    (a₀ h) (a h) (p h) (q h) (hp h) (hP h) (hq h) (hone h)
  let k : Fin M → ℝ := fun h ↦ 2 * q h / (q h ^ 2 - 1)
  let C := c + ∑ h, k h * a₀ h
  let Cs : Fin n → ℝ := fun i ↦ cs i + ∑ h, k h * a h i
  have hcorrection (bits : Fin n → Bool) :
      affineValue C Cs bits = affineValue c cs bits +
        ∑ h, k h * affineValue (a₀ h) (a h) bits := by
    simp only [C, Cs, affineValue, add_mul, mul_add,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
    ring
  let g : Fin (M + 1) → (Fin n → Bool) → ℝ :=
    Fin.cases (affineValue C Cs) (fun h bits ↦ (φ h).eval bits)
  apply computableWithHeadsN_of_uniformlyOneAtomApproximable g _ 0
  · intro bits
    have heq : 0 + ∑ h, g h bits = sharedAffineScore c cs a₀ a p q bits := by
      rw [zero_add, Fin.sum_univ_succ]
      change affineValue C Cs bits + ∑ h, (φ h).eval bits = _
      rw [hcorrection]
      dsimp [sharedAffineScore]
      simp_rw [hφ]
      rw [Finset.sum_add_distrib]
      dsimp [k]
      ring
    change ((0 < 0 + ∑ h, g h bits ↔ f bits = true) ∧
      0 + ∑ h, g h bits ≠ 0)
    rw [heq]
    exact hstrict bits
  · intro j
    refine Fin.cases ?_ (fun h ↦ ?_) j
    · exact uniformlyOneAtomApproximable_affineValue C Cs
    · intro ε hε
      exact ⟨φ h, fun bits ↦ by simpa [g] using hε⟩

private theorem strictSignRepresentsScore_of_error
    {score approx : (Fin n → Bool) → ℝ} {f : (Fin n → Bool) → Bool}
    (hs : StrictSignRepresentsScore score f)
    (herr : ∀ bits, |approx bits - score bits| < |score bits|) :
    StrictSignRepresentsScore approx f := by
  intro bits
  have he := abs_lt.mp (herr bits)
  rcases lt_or_gt_of_ne (hs bits).2 with hn | hp
  · rw [abs_of_neg hn] at he
    have ha : approx bits < 0 := by linarith
    refine ⟨?_, ha.ne⟩
    have hf : ¬ f bits = true := fun h ↦ (not_lt_of_gt hn) ((hs bits).1.mpr h)
    simp only [not_lt_of_gt ha, false_iff]
    exact hf
  · rw [abs_of_pos hp] at he
    have ha : 0 < approx bits := by linarith
    exact ⟨iff_of_true ha ((hs bits).1.mp hp), ha.ne'⟩

/-- Every strict score in the complete chart, including units at q = 1,
has a realization in the attention model using M + 1 heads. The statement
is conditional on an already existing strict score, not a universal fitting
or head-complexity upper bound. -/
theorem computableWithHeadsN_of_sharedAffineScore
    (c : ℝ) (cs : Fin n → ℝ) (a₀ : Fin M → ℝ)
    (a p : Fin M → Fin n → ℝ) (q : Fin M → ℝ)
    (hp : ∀ h i, 0 < p h i) (hP : ∀ h, 0 < ∑ i, p h i)
    (hq : ∀ h, 0 < q h) (f : (Fin n → Bool) → Bool)
    (hstrict : StrictSignRepresentsScore (sharedAffineScore c cs a₀ a p q) f) :
    computableWithHeadsN n (M + 1) f := by
  classical
  let S := sharedAffineScore c cs a₀ a p q
  obtain ⟨nearest, -, hmin⟩ :=
    (Finset.univ : Finset (Fin n → Bool)).exists_min_image
      (fun bits ↦ |S bits|) Finset.univ_nonempty
  let γ := |S nearest|
  have hγ : 0 < γ := abs_pos.mpr (hstrict nearest).2
  let K : ℝ := 1 + ∑ h, ∑ bits : Fin n → Bool, |affineValue (a₀ h) (a h) bits|
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let δ := min 1 (γ / (2 * K))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hγ (by positivity))
  have hbudget : K * δ ≤ γ / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp
      (show δ ≤ γ / (2 * K) from min_le_right _ _)
    nlinarith
  let q' : Fin M → ℝ := fun h ↦ if q h = 1 then 1 + δ else q h
  have hq' : ∀ h, 0 < q' h := by
    intro h
    dsimp [q']
    split_ifs <;> first | positivity | exact hq h
  have hone' : ∀ h, q' h ≠ 1 := by
    intro h
    dsimp [q']
    split_ifs with he
    · linarith
    · exact he
  apply computableWithHeadsN_of_sharedAffineScore_nonzero
    c cs a₀ a p q' hp hP hq' hone' f
  apply strictSignRepresentsScore_of_error hstrict
  intro bits
  have hterm (h : Fin M) :
      |orientationCrossingFeature (q' h) (affineValue 0 (p h) bits)
          ((∑ i, p h i) - affineValue 0 (p h) bits) -
        orientationCrossingFeature (q h) (affineValue 0 (p h) bits)
          ((∑ i, p h i) - affineValue 0 (p h) bits)| ≤ δ := by
    by_cases he : q h = 1
    · have ht := shape_parts (p h) (hp h) bits
      have htotal : 0 < affineValue 0 (p h) bits +
          ((∑ i, p h i) - affineValue 0 (p h) bits) := by
        simpa using hP h
      have hb := orientationCrossingFeature_error_le (1 + δ)
        (affineValue 0 (p h) bits) ((∑ i, p h i) - affineValue 0 (p h) bits)
        (by positivity) ht.1 ht.2 htotal
      simp only [q', he, ite_true]
      apply hb.trans
      rw [show 1 + δ - 1 = δ by ring, abs_of_pos hδ]
      apply (div_le_iff₀ (show 0 < 2 * (1 + δ + 1) by positivity)).mpr
      nlinarith
    · simp only [q', he, ite_false, sub_self, abs_zero]
      exact hδ.le
  have hKpoint : (∑ h, |affineValue (a₀ h) (a h) bits|) ≤ K := by
    calc
      _ ≤ ∑ h, ∑ b : Fin n → Bool, |affineValue (a₀ h) (a h) b| := by
        apply Finset.sum_le_sum
        intro h _
        exact Finset.single_le_sum
          (fun b _ ↦ abs_nonneg (affineValue (a₀ h) (a h) b)) (Finset.mem_univ bits)
      _ ≤ K := by dsimp [K]; linarith
  have hdiff : sharedAffineScore c cs a₀ a p q' bits - S bits =
      ∑ h, affineValue (a₀ h) (a h) bits *
        (orientationCrossingFeature (q' h) (affineValue 0 (p h) bits)
            ((∑ i, p h i) - affineValue 0 (p h) bits) -
          orientationCrossingFeature (q h) (affineValue 0 (p h) bits)
            ((∑ i, p h i) - affineValue 0 (p h) bits)) := by
    dsimp [S, sharedAffineScore]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  calc
    |sharedAffineScore c cs a₀ a p q' bits - S bits| ≤
        (∑ h, |affineValue (a₀ h) (a h) bits|) * δ := by
      rw [hdiff, Finset.sum_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hterm h) (abs_nonneg _)
    _ ≤ K * δ := mul_le_mul_of_nonneg_right hKpoint hδ.le
    _ ≤ γ / 2 := hbudget
    _ < γ := by linarith
    _ ≤ |S bits| := hmin bits (Finset.mem_univ bits)

/-- The same conditional lift in the literal shared-token-embedding model. -/
theorem computableWithSharedHeadsN_of_sharedAffineScore
    (c : ℝ) (cs : Fin n → ℝ) (a₀ : Fin M → ℝ)
    (a p : Fin M → Fin n → ℝ) (q : Fin M → ℝ)
    (hp : ∀ h i, 0 < p h i) (hP : ∀ h, 0 < ∑ i, p h i)
    (hq : ∀ h, 0 < q h) (f : (Fin n → Bool) → Bool)
    (hstrict : StrictSignRepresentsScore (sharedAffineScore c cs a₀ a p q) f) :
    computableWithSharedHeadsN n (M + 1) f :=
  computableWithSharedHeadsN_of_computableWithHeadsN
    (computableWithHeadsN_of_sharedAffineScore c cs a₀ a p q hp hP hq f hstrict)

end HeadComplexity
