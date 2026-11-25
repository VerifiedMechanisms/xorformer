import HeadComplexity.Research.MinZeroPositivePartition
import HeadComplexity.Research.MidrangeMarginCentering
import HeadComplexity.Research.MarginInvariance

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.NonnegativePartitionEmbedding
open Finset RelativeMarginQuantifiers MidrangeMarginCentering
open scoped BigOperators

variable {n H : ℕ}

def minCenter (φ : FracAtom n) : FracAtom n := φ.translate (-rangeMin φ)

@[simp] theorem minCenter_eval (φ : FracAtom n) (x : Fin n → Bool) :
    (minCenter φ).eval x = φ.eval x-rangeMin φ := by
  simp [minCenter, sub_eq_add_neg]

theorem minCenter_nonneg (φ : FracAtom n) (x : Fin n → Bool) :
    0 ≤ (minCenter φ).eval x := by
  rw [minCenter_eval]
  exact sub_nonneg.mpr (rangeMin_le_eval φ x)

theorem minCenter_has_zero (φ : FracAtom n) :
    ∃ x, (minCenter φ).eval x = 0 := by
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n → Bool)).Nonempty) φ.eval
  refine ⟨x,?_⟩
  rw [minCenter_eval]
  simp only [rangeMin]
  linarith

theorem abs_rangeMin_le (φ : FracAtom n) : |rangeMin φ| ≤ atomSup φ := by
  apply abs_le.mpr
  constructor
  · apply Finset.le_inf'
    intro x _
    exact (abs_le.mp (abs_eval_le_atomSup φ x)).1
  · exact (rangeMin_le_eval φ (fun _ => false)).trans
      ((abs_le.mp (abs_eval_le_atomSup φ (fun _ => false))).2)

theorem minCenter_atomSup_le (φ : FracAtom n) : atomSup (minCenter φ) ≤ 2*atomSup φ := by
  apply Finset.sup'_le
  intro x _
  rw [minCenter_eval]
  calc
    |φ.eval x-rangeMin φ| ≤ |φ.eval x|+|rangeMin φ| := abs_sub _ _
    _ ≤ atomSup φ+atomSup φ := add_le_add (abs_eval_le_atomSup φ x) (abs_rangeMin_le φ)
    _ = 2*atomSup φ := by ring

def constantPart (φ : Fin H → FracAtom n) (bias : ℝ) : ℝ :=
  bias+∑ h, rangeMin (φ h)

theorem abs_constantPart_le (φ : Fin H → FracAtom n) (bias : ℝ) :
    |constantPart φ bias| ≤ amplitude φ bias := by
  calc
    _ ≤ |bias|+|∑ h, rangeMin (φ h)| := abs_add_le _ _
    _ ≤ |bias|+∑ h, |rangeMin (φ h)| := add_le_add le_rfl (abs_sum_le_sum_abs _ _)
    _ ≤ amplitude φ bias := add_le_add le_rfl (sum_le_sum fun h _ => abs_rangeMin_le (φ h))

/-- Two nonnegative genuine heads carry the constant partition; every source
head is shifted by its actual full-cube minimum and scaled positively. -/
def embeddedHeads (φ : Fin H → FracAtom (n+1)) (bias ε : ℝ) :
    Fin (2+H) → FracAtom (n+1) :=
  Fin.addCases
    (fun j => (MinZeroPositivePartition.partition n j).scale (1+ε*constantPart φ bias))
    (fun h => (minCenter (φ h)).scale ε)

theorem embedded_score (φ : Fin H → FracAtom (n+1)) (bias ε : ℝ)
    (x : Fin (n+1) → Bool) :
    score (embeddedHeads φ bias ε) (-1) x = ε*score φ bias x := by
  simp only [score, embeddedHeads, Fin.sum_univ_add, Fin.addCases_left,
    Fin.addCases_right, FracAtom.scale_eval, minCenter_eval, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [MinZeroPositivePartition.partition_sum]
  unfold constantPart
  ring

theorem partition_scale_pos (φ : Fin H → FracAtom (n+1)) (bias ε : ℝ)
    (hε : 0 ≤ ε) (hsmall : ε*amplitude φ bias ≤ 1/4) :
    0 < 1+ε*constantPart φ bias := by
  have h := (abs_le.mp (abs_constantPart_le φ bias)).1
  have hm := mul_le_mul_of_nonneg_left h hε
  nlinarith

theorem embedded_nonneg (φ : Fin H → FracAtom (n+1)) (bias ε : ℝ)
    (hε : 0 ≤ ε) (hsmall : ε*amplitude φ bias ≤ 1/4)
    (j : Fin (2+H)) (x : Fin (n+1) → Bool) :
    0 ≤ (embeddedHeads φ bias ε j).eval x := by
  have hr := (partition_scale_pos φ bias ε hε hsmall).le
  refine Fin.addCases (fun j => ?_) (fun h => ?_) j
  · simp only [embeddedHeads, Fin.addCases_left, FracAtom.scale_eval]
    exact mul_nonneg hr (MinZeroPositivePartition.partition_nonneg n j x)
  · simp only [embeddedHeads, Fin.addCases_right, FracAtom.scale_eval]
    exact mul_nonneg hε (minCenter_nonneg (φ h) x)

theorem embedded_has_zero (φ : Fin H → FracAtom (n+1)) (bias ε : ℝ)
    (j : Fin (2+H)) : ∃ x, (embeddedHeads φ bias ε j).eval x = 0 := by
  refine Fin.addCases (fun j => ?_) (fun h => ?_) j
  · obtain ⟨x,hx⟩ := MinZeroPositivePartition.partition_has_zero n j
    exact ⟨x,by simp [embeddedHeads,hx]⟩
  · obtain ⟨x,hx⟩ := minCenter_has_zero (φ h)
    exact ⟨x,by simp [embeddedHeads,hx]⟩

theorem embedded_amplitude_le (φ : Fin H → FracAtom (n+1)) (bias ε : ℝ)
    (hε : 0 ≤ ε) (hsmall : ε*amplitude φ bias ≤ 1/4) :
    amplitude (embeddedHeads φ bias ε) (-1) ≤ 4 := by
  let r := 1+ε*constantPart φ bias
  have hr : 0 ≤ r := (partition_scale_pos φ bias ε hε hsmall).le
  have hfirst : (∑ j : Fin 2, atomSup ((MinZeroPositivePartition.partition n j).scale r)) ≤ 2*r := by
    calc
      _ ≤ ∑ _j : Fin 2, r := sum_le_sum fun j _ => by
        rw [atomSup_scale, abs_of_nonneg hr]
        simpa using mul_le_mul_of_nonneg_left (MinZeroPositivePartition.partition_atomSup_le n j) hr
      _ = 2*r := by simp
  have hrest : (∑ h, atomSup ((minCenter (φ h)).scale ε)) ≤ 2*ε*(∑ h, atomSup (φ h)) := by
    simp only [atomSup_scale, abs_of_nonneg hε, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left
      (sum_le_sum (s := Finset.univ) fun h _ => minCenter_atomSup_le (φ h)) hε
    simp only [← Finset.mul_sum] at hh
    nlinarith
  have hC := (abs_le.mp (abs_constantPart_le φ bias)).2
  have hCr := mul_le_mul_of_nonneg_left hC hε
  have hs : (∑ h, atomSup (φ h)) ≤ amplitude φ bias := by
    unfold amplitude
    linarith [abs_nonneg bias]
  have hsm := mul_le_mul_of_nonneg_left hs hε
  have ha : amplitude (embeddedHeads φ bias ε) (-1) =
      1+(∑ j : Fin 2, atomSup ((MinZeroPositivePartition.partition n j).scale r))+
        ∑ h, atomSup ((minCenter (φ h)).scale ε) := by
    simp [amplitude, embeddedHeads, Fin.sum_univ_add, r]
    ring
  rw [ha]
  dsimp [r] at hfirst
  nlinarith

/-- Every original strict representation has arbitrarily close min-zero
positive-partition representatives with only two additional heads and actual
full-cube amplitude at most four. The complete truth table is preserved. -/
theorem exists_bounded_near_partition
    (f : (Fin (n+1) → Bool) → Bool) (φ : Fin H → FracAtom (n+1)) (bias : ℝ)
    (hs : StrictlyRepresents f φ bias) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ε : ℝ) (ψ : Fin (2+H) → FracAtom (n+1)),
      0 < ε ∧
      (∀ j x, 0 ≤ (ψ j).eval x) ∧
      (∀ j, ∃ x, (ψ j).eval x = 0) ∧
      amplitude ψ (-1) ≤ 4 ∧
      (∀ x, score ψ (-1) x = ε*score φ bias x) ∧
      (∀ x, |score ψ (-1) x| ≤ δ) ∧ StrictlyRepresents f ψ (-1) := by
  let A := amplitude φ bias
  have hA : 0 < A := amplitude_pos_of_strict hs
  let ε := min ((1/4)/A) (δ/A)
  have hε : 0 < ε := lt_min (div_pos (by norm_num) hA) (div_pos hδ hA)
  have hsmall : ε*A ≤ 1/4 := (le_div_iff₀ hA).mp (min_le_left _ _)
  have hclose : ε*A ≤ δ := (le_div_iff₀ hA).mp (min_le_right _ _)
  refine ⟨ε,embeddedHeads φ bias ε,hε,embedded_nonneg φ bias ε hε.le hsmall,
    embedded_has_zero φ bias ε,embedded_amplitude_le φ bias ε hε.le hsmall,
    embedded_score φ bias ε,?_,?_⟩
  · intro x
    rw [embedded_score, abs_mul, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left (abs_score_le_amplitude φ bias x) hε.le).trans hclose
  · intro x
    rw [embedded_score]
    have hh := mul_pos hε (hs x)
    nlinarith

/-- The truth-table formulation uses the original unrestricted computability
predicate; its strictification does not increase width. -/
theorem exists_bounded_near_partition_of_computable
    (f : (Fin (n+1) → Bool) → Bool)
    (hf : computableWithHeadsN (n+1) H f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ψ : Fin (2+H) → FracAtom (n+1),
      (∀ j x, 0 ≤ (ψ j).eval x) ∧
      (∀ j, ∃ x, (ψ j).eval x = 0) ∧
      amplitude ψ (-1) ≤ 4 ∧
      (∀ x, |score ψ (-1) x| ≤ δ) ∧ StrictlyRepresents f ψ (-1) := by
  obtain ⟨γ,hγ,φ,bias,hs,hmargin⟩ := exists_positive_margin_of_computable hf
  obtain ⟨ε,ψ,hε,hn,hz,ha,he,hclose,hstrict⟩ :=
    exists_bounded_near_partition f φ bias hs δ hδ
  exact ⟨ψ,hn,hz,ha,hclose,hstrict⟩


/-- Choosing the normalization scale at its fixed upper bound loses at most
sixteen in relative margin, while retaining the bounded positive normal form. -/
theorem exists_normalized_certificate
    (f : (Fin (n+1) → Bool) → Bool) (φ : Fin H → FracAtom (n+1)) (bias : ℝ)
    (hs : StrictlyRepresents f φ bias) :
    ∃ ψ : Fin (2+H) → FracAtom (n+1),
      (∀ j x, 0 ≤ (ψ j).eval x) ∧
      (∀ j, ∃ x, (ψ j).eval x = 0) ∧
      amplitude ψ (-1) ≤ 4 ∧
      (∀ x, |score ψ (-1) x| ≤ 1/4) ∧
      StrictlyRepresents f ψ (-1) ∧
      relativeMargin f φ bias / 16 ≤ relativeMargin f ψ (-1) := by
  let A := amplitude φ bias
  have hA : 0 < A := amplitude_pos_of_strict hs
  let ε := (1/4)/A
  have hε : 0 < ε := div_pos (by norm_num) hA
  have hεA : ε*A = 1/4 := div_mul_cancel₀ _ hA.ne'
  let ψ := embeddedHeads φ bias ε
  have hsmall : ε*amplitude φ bias ≤ 1/4 := hεA.le
  have hD : amplitude ψ (-1) ≤ 4 := embedded_amplitude_le φ bias ε hε.le hsmall
  have hstrict : StrictlyRepresents f ψ (-1) := by
    intro x
    change 0 < signedLabel f x * score (embeddedHeads φ bias ε) (-1) x
    rw [embedded_score]
    have hh := mul_pos hε (hs x)
    nlinarith
  refine ⟨ψ,embedded_nonneg φ bias ε hε.le hsmall,
    embedded_has_zero φ bias ε,hD,?_,hstrict,?_⟩
  · intro x
    change |score (embeddedHeads φ bias ε) (-1) x| ≤ 1/4
    rw [embedded_score,abs_mul,abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left (abs_score_le_amplitude φ bias x) hε.le).trans hsmall
  · apply (le_relativeMargin_iff hstrict).mpr
    intro x
    have hg : 0 ≤ relativeMargin f φ bias := (relativeMargin_pos hs).le
    have hx := (le_relativeMargin_iff hs).mp (le_refl (relativeMargin f φ bias)) x
    have hscale := mul_le_mul_of_nonneg_left hx hε.le
    calc
      relativeMargin f φ bias / 16 * amplitude ψ (-1)
          ≤ relativeMargin f φ bias / 4 := by nlinarith
      _ = ε * (relativeMargin f φ bias * amplitude φ bias) := by
        change _ = ε * (relativeMargin f φ bias * A)
        calc
          _ = relativeMargin f φ bias * (1/4) := by ring
          _ = relativeMargin f φ bias * (ε*A) := by rw [hεA]
          _ = _ := by ring
      _ ≤ ε * (signedLabel f x * score φ bias x) := hscale
      _ = signedLabel f x * score ψ (-1) x := by
        change _ = signedLabel f x * score (embeddedHeads φ bias ε) (-1) x
        rw [embedded_score]
        ring

/-- Any original margin certificate admits the min-zero nonnegative normal
form with two additional heads and only a factor-sixteen margin loss. -/
theorem exists_normalized_certificate_of_margin
    {f : (Fin (n+1) → Bool) → Bool} {γ : ℝ}
    (hf : HasRelativeMargin (n+1) H f γ) :
    ∃ ψ : Fin (2+H) → FracAtom (n+1),
      (∀ j x, 0 ≤ (ψ j).eval x) ∧
      (∀ j, ∃ x, (ψ j).eval x = 0) ∧
      amplitude ψ (-1) ≤ 4 ∧
      (∀ x, |score ψ (-1) x| ≤ 1/4) ∧
      StrictlyRepresents f ψ (-1) ∧
      γ/16 ≤ relativeMargin f ψ (-1) := by
  obtain ⟨φ,bias,hs,hγ⟩ := hf
  obtain ⟨ψ,hn,hz,hD,hclose,hstrict,hm⟩ := exists_normalized_certificate f φ bias hs
  exact ⟨ψ,hn,hz,hD,hclose,hstrict,(div_le_div_of_nonneg_right hγ (by norm_num)).trans hm⟩

end HeadComplexity.NonnegativePartitionEmbedding
