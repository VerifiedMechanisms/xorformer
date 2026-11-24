import HeadComplexity.Atoms.RoPE
import HeadComplexity.Results.SymmetricComplexity
import HeadComplexity.Polynomial.ParityThresholdDegree

set_option linter.style.header false

/-!
# Head-count comparisons for rotary scalar normal forms

All declarations here concern the explicitly defined scalar atoms and the
repository's existing vanilla model. `Results/PureRoPEArchitecture` proves their
equivalence to literal fixed-frequency rotary attention, including the residual.
-/

namespace HeadComplexity

open MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- Positive affine fractions with no sign restriction on denominator slopes. -/
def positiveFractionComputable (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (r : Fin H → AffineFraction n) (c : ℝ),
    (∀ h x, 0 < (r h).denominator x) ∧
      ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true)

theorem positiveFractionComputable_of_retained {H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : retainedRoPEComputable n H f) : positiveFractionComputable n H f := by
  obtain ⟨p, c, hp⟩ := hf
  exact ⟨fun h ↦ (p h).toAffineFraction, c,
    fun h x ↦ (p h).denominator_pos x, hp⟩

private noncomputable def affinePolynomial (c : ℝ) (v : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ := C c + ∑ i, affineAt i 0 (v i)

private theorem affinePolynomial_eval (c : ℝ) (v : Fin n → ℝ) (x : Fin n → Bool) :
    eval (cubePoint x) (affinePolynomial c v) = c + ∑ i, v i * boolToReal (x i) := by
  simp only [affinePolynomial, map_add, eval_C, map_sum, affineAt_eval]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

private theorem affinePolynomial_degree (c : ℝ) (v : Fin n → ℝ) :
    (affinePolynomial c v).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  exact max_le (by simp) (totalDegree_finsetSum_le fun i _ ↦ affineAt_totalDegree_le _ _ _)

/-- Denominator clearing needs positivity, not uniform denominator slopes. -/
theorem thresholdDegLE_of_positiveFractionComputable {H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : positiveFractionComputable n H f) :
    ThresholdDegLE f H := by
  classical
  obtain ⟨r, c, hdpos, hsign⟩ := hf
  let N (h : Fin H) := affinePolynomial (r h).b (r h).A
  let D (h : Fin H) := affinePolynomial (r h).d (r h).C
  have hN (h) : (N h).totalDegree ≤ 1 := affinePolynomial_degree _ _
  have hD (h) : (D h).totalDegree ≤ 1 := affinePolynomial_degree _ _
  have hNe (h) (x) : eval (cubePoint x) (N h) = (r h).numerator x :=
    affinePolynomial_eval _ _ _
  have hDe (h) (x) : eval (cubePoint x) (D h) = (r h).denominator x :=
    affinePolynomial_eval _ _ _
  refine ⟨C c * ∏ h, D h + ∑ h, N h * ∏ g ∈ Finset.univ.erase h, D g, ?_, ?_⟩
  · apply (totalDegree_add _ _).trans
    refine max_le ?_ (totalDegree_finsetSum_le fun h _ ↦ ?_)
    · apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, Nat.zero_add]
      simpa using totalDegree_prod_le_card Finset.univ D hD
    · apply (totalDegree_mul _ _).trans
      have he : (∏ g ∈ Finset.univ.erase h, D g).totalDegree ≤ H - 1 := by
        simpa using totalDegree_prod_le_card (Finset.univ.erase h) D hD
      have hH : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact h.elim0)
      have := hN h
      omega
  · intro x
    have hp : 0 < ∏ h, (r h).denominator x := Finset.prod_pos fun h _ ↦ hdpos h x
    have hi (h : Fin H) :
        (r h).numerator x * ∏ g ∈ Finset.univ.erase h, (r g).denominator x =
          (∏ g, (r g).denominator x) * (r h).eval x := by
      rw [← Finset.mul_prod_erase Finset.univ (fun g ↦ (r g).denominator x)
        (Finset.mem_univ h)]
      unfold AffineFraction.eval
      have hn := (hdpos h x).ne'
      field_simp
    simp only [map_add, map_mul, map_sum, map_prod, eval_C, hNe, hDe]
    simp_rw [hi]
    rw [← Finset.mul_sum, mul_comm c, ← mul_add, mul_pos_iff_of_pos_left hp]
    exact hsign x

theorem thresholdDegLE_of_retainedRoPEComputable {H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : retainedRoPEComputable n H f) :
    ThresholdDegLE f H :=
  thresholdDegLE_of_positiveFractionComputable (positiveFractionComputable_of_retained hf)

theorem thresholdDegLE_of_pureRoPEComputable {H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n H f) :
    ThresholdDegLE f H :=
  thresholdDegLE_of_retainedRoPEComputable (retainedRoPEComputable_of_pure hf)

theorem pureRoPEComputable_one_iff_isLTF (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n 1 f ↔ isLTF f := by
  constructor
  · intro hf
    exact (ThresholdDegLE_one_iff_isLTF f).mp (thresholdDegLE_of_pureRoPEComputable hf)
  · intro hf
    apply pureRoPEComputable_of_vanilla
    exact (computableWithHeadsN_iff_computableWithSharedHeadsN n 1 f).mp
      (computable_one_of_isLTF f hf)

theorem retainedRoPEComputable_one_iff_isLTF (f : (Fin n → Bool) → Bool) :
    retainedRoPEComputable n 1 f ↔ isLTF f := by
  constructor
  · intro hf
    exact (ThresholdDegLE_one_iff_isLTF f).mp (thresholdDegLE_of_retainedRoPEComputable hf)
  · intro hf
    exact retainedRoPEComputable_of_pure ((pureRoPEComputable_one_iff_isLTF f).mpr hf)

theorem exists_pureRoPEComputable (f : (Fin n → Bool) → Bool) :
    ∃ H, pureRoPEComputable n H f := by
  refine ⟨HStar n f, pureRoPEComputable_of_vanilla ?_⟩
  exact (computableWithHeadsN_iff_computableWithSharedHeadsN n _ f).mp (HStar_computable f)

theorem exists_retainedRoPEComputable (f : (Fin n → Bool) → Bool) :
    ∃ H, retainedRoPEComputable n H f := by
  obtain ⟨H, hH⟩ := exists_pureRoPEComputable f
  exact ⟨H, retainedRoPEComputable_of_pure hH⟩

/-- Minimum count in the pure scalar model. -/
noncomputable def PureRoPEHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_pureRoPEComputable f)

/-- Minimum count in the retained scalar model. -/
noncomputable def RetainedRoPEHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_retainedRoPEComputable f)

theorem pureRoPEHStar_computable (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n (PureRoPEHStar n f) f := by
  classical
  exact Nat.find_spec (exists_pureRoPEComputable f)

theorem retainedRoPEHStar_computable (f : (Fin n → Bool) → Bool) :
    retainedRoPEComputable n (RetainedRoPEHStar n f) f := by
  classical
  exact Nat.find_spec (exists_retainedRoPEComputable f)

theorem pureRoPEHStar_le_vanilla (f : (Fin n → Bool) → Bool) :
    PureRoPEHStar n f ≤ HStar n f := by
  classical
  apply Nat.find_min'
  apply pureRoPEComputable_of_vanilla
  exact (computableWithHeadsN_iff_computableWithSharedHeadsN n _ f).mp (HStar_computable f)

theorem retainedRoPEHStar_le_pure (f : (Fin n → Bool) → Bool) :
    RetainedRoPEHStar n f ≤ PureRoPEHStar n f := by
  classical
  exact Nat.find_min' _ (retainedRoPEComputable_of_pure (pureRoPEHStar_computable f))

theorem thresholdDeg_le_retainedRoPEHStar (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ RetainedRoPEHStar n f := by
  classical
  have ht := thresholdDegLE_of_retainedRoPEComputable (retainedRoPEHStar_computable f)
  have hex : ∃ k, ThresholdDegLE f k := ⟨_, ht⟩
  unfold thresholdDeg
  rw [dif_pos hex]
  exact Nat.find_min' hex ht

theorem ropeHStar_eq_vanilla_of_degree_tight (f : (Fin n → Bool) → Bool)
    (ht : HStar n f = thresholdDeg f) :
    RetainedRoPEHStar n f = HStar n f ∧ PureRoPEHStar n f = HStar n f := by
  have ha := thresholdDeg_le_retainedRoPEHStar f
  have hb := retainedRoPEHStar_le_pure f
  have hc := pureRoPEHStar_le_vanilla f
  omega

theorem ropeHStar_symmetric (F : ℕ → Bool) (n : ℕ) :
    RetainedRoPEHStar n (symmetricFn F) = signChanges n F ∧
      PureRoPEHStar n (symmetricFn F) = signChanges n F := by
  have ha := signChanges_le_of_ThresholdDegLE
    (thresholdDegLE_of_retainedRoPEComputable
      (retainedRoPEHStar_computable (n := n) (symmetricFn F)))
  have hb := retainedRoPEHStar_le_pure (n := n) (symmetricFn F)
  have hc := pureRoPEHStar_le_vanilla (n := n) (symmetricFn F)
  rw [HStar_symmetricFn] at hc
  omega

end HeadComplexity
