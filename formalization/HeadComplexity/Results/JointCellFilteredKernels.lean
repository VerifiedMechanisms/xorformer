import HeadComplexity.Results.AffineFractionAlternation
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
Exact shared finite-difference filters for reciprocal heads on the Boolean
cube. These identities expose a larger-domain decoder candidate. They do not
claim an improved universal head bound or that a filtered kernel decodes
arbitrary bit words.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The full mixed Boolean difference of a reciprocal affine form. -/
noncomputable def jointCellFilteredKernel (s : Finset ι) (w : ι → ℝ) (d : ℝ) : ℝ :=
  (-1 : ℝ) ^ s.card * faceAlternation s (fun t ↦ 1 / (d - ∑ i ∈ t, w i))

private theorem faceAlternation_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (v : Finset ι → ℝ) :
    faceAlternation (insert i s) v =
      faceAlternation s v - faceAlternation s (fun t ↦ v (insert i t)) := by
  unfold faceAlternation
  rw [Finset.sum_powerset_insert hi]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun hit ↦ hi ((Finset.mem_powerset.mp ht) hit)
  rw [Finset.card_insert_of_notMem hit, pow_succ]
  ring

/-- An alternating face sum vanishes if one face coordinate is irrelevant. -/
theorem jointCell_faceAlternation_zero_of_irrelevant (s : Finset ι) (i : ι)
    (hi : i ∈ s) (v : Finset ι → ℝ)
    (hv : ∀ t ⊆ s.erase i, v (insert i t) = v t) :
    faceAlternation s v = 0 := by
  have he := faceAlternation_insert (s.erase i) i (Finset.notMem_erase i s) v
  rw [Finset.insert_erase hi] at he
  rw [he]
  have hc : faceAlternation (s.erase i) (fun t ↦ v (insert i t)) =
      faceAlternation (s.erase i) v := faceAlternation_congr _ hv
  rw [hc, sub_self]

/-- A shared reciprocal family extracts the full support monomial exactly.
Every summand is one affine reciprocal. The same summands can be reused in
linear combinations of filters for different subsets. -/
theorem jointCell_filtered_reciprocal_eq (s : Finset ι) (w : ι → ℝ) (d : ℝ)
    (bits : ι → Bool) :
    (-1 : ℝ) ^ s.card * faceAlternation s
      (fun t ↦ 1 / (d - ∑ i ∈ t, w i * boolToReal (bits i))) =
      if ∀ i ∈ s, bits i = true then jointCellFilteredKernel s w d else 0 := by
  classical
  by_cases h : ∀ i ∈ s, bits i = true
  · rw [ite_eq_left h]
    unfold jointCellFilteredKernel
    congr 1
    apply faceAlternation_congr
    intro t ht
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i (ht hi)]
    simp [boolToReal]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    obtain ⟨his, hbi⟩ := not_forall.mp hi
    have hfalse : bits i = false := by cases he : bits i <;> simp_all
    have hz : faceAlternation s
        (fun t ↦ 1 / (d - ∑ j ∈ t, w j * boolToReal (bits j))) = 0 := by
      apply jointCell_faceAlternation_zero_of_irrelevant s i his
      intro t ht
      have hit : i ∉ t := fun hit ↦ (Finset.mem_erase.mp (ht hit)).1 rfl
      rw [Finset.sum_insert hit, hfalse]
      simp [boolToReal]
    rw [hz, mul_zero]

/-- Exact positive recurrence for a full mixed reciprocal difference. -/
theorem jointCell_filtered_kernel_recurrence (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (d : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hd : ∑ i ∈ s, w i < d) :
    (d - ∑ i ∈ s, w i) * jointCellFilteredKernel s w d =
      ∑ i ∈ s, w i * jointCellFilteredKernel (s.erase i) w d := by
  let v : Finset ι → ℝ := fun t ↦ 1 / (d - ∑ i ∈ t, w i)
  have hz : faceAlternation s (fun t ↦ (d + ∑ i ∈ t, -w i) * v t) = 0 := by
    calc
      _ = faceAlternation s (fun _ ↦ 1) := by
        apply faceAlternation_congr
        intro t ht
        have hsum : (∑ i ∈ t, w i) ≤ ∑ i ∈ s, w i :=
          Finset.sum_le_sum_of_subset_of_nonneg ht (fun i hi _ ↦ hw i hi)
        have hden : d - ∑ i ∈ t, w i ≠ 0 := by linarith
        rw [Finset.sum_neg_distrib]
        change (d - ∑ i ∈ t, w i) * (1 / (d - ∑ i ∈ t, w i)) = 1
        field_simp [hden]
      _ = 0 := faceAlternation_constant s hs 1
  rw [faceAlternation_affine_mul] at hz
  simp only [Finset.sum_neg_distrib, neg_mul] at hz
  have he : (d - ∑ i ∈ s, w i) * faceAlternation s v =
      -(∑ i ∈ s, w i * faceAlternation (s.erase i) v) := by
    simpa only [sub_eq_add_neg, sub_neg_eq_add] using sub_eq_zero.mp hz
  unfold jointCellFilteredKernel
  change (d - ∑ i ∈ s, w i) * ((-1 : ℝ) ^ s.card * faceAlternation s v) = _
  rw [mul_left_comm, he, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : s.card = (s.erase i).card + 1 := by
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr hs
    omega
  rw [hc, pow_succ]
  change -((-1 : ℝ) ^ (s.erase i).card * -1 *
    (w i * faceAlternation (s.erase i) v)) =
      w i * ((-1 : ℝ) ^ (s.erase i).card * faceAlternation (s.erase i) v)
  ring

/-- All full reciprocal differences are strictly positive for positive slopes
and a positive full-cube denominator margin. -/
theorem jointCell_filtered_kernel_pos (s : Finset ι) (w : ι → ℝ) (d : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hd : ∑ i ∈ s, w i < d) :
    0 < jointCellFilteredKernel s w d := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s.Nonempty
    · have hrec := jointCell_filtered_kernel_recurrence s hs w d
        (fun i hi ↦ (hw i hi).le) hd
      have hp : 0 < ∑ i ∈ s, w i * jointCellFilteredKernel (s.erase i) w d := by
        apply Finset.sum_pos
        · intro i hi
          apply mul_pos (hw i hi)
          apply ih (s.erase i) (Finset.erase_ssubset hi)
          · intro j hj
            exact hw j (Finset.mem_of_mem_erase hj)
          · have hsum : (∑ j ∈ s.erase i, w j) ≤ ∑ j ∈ s, w j :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i s)
                (fun j hj _ ↦ (hw j hj).le)
            linarith
        · exact hs
      have hden : 0 < d - ∑ i ∈ s, w i := sub_pos.mpr hd
      rw [← hrec] at hp
      exact (mul_pos_iff_of_pos_left hden).mp hp
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simp only [Finset.sum_empty] at hd
      simpa [jointCellFilteredKernel, faceAlternation] using one_div_pos.mpr hd

/-- Every finite downward-closed monomial family has one shared reciprocal
basis with exactly one denominator per member. Coefficients may be arbitrary
and independently chosen; no cancellation assumption is imposed on them. -/
theorem jointCell_exists_shared_reciprocal_basis
    (F : Finset (Finset ι))
    (hdown : ∀ U ∈ F, ∀ T ⊆ U, T ∈ F)
    (w : ι → ℝ) (d : ℝ)
    (hw : ∀ U ∈ F, ∀ i ∈ U, 0 < w i)
    (hd : ∀ U ∈ F, ∑ i ∈ U, w i < d)
    (coeff : Finset ι → ℝ) :
    ∃ headCoeff : Finset ι → ℝ, ∀ bits : ι → Bool,
      (∑ T ∈ F, headCoeff T / (d - ∑ i ∈ T, w i * boolToReal (bits i))) =
        ∑ U ∈ F, coeff U * (if ∀ i ∈ U, bits i = true then 1 else 0) := by
  classical
  let A : Finset ι → ℝ := fun U ↦ coeff U / jointCellFilteredKernel U w d
  let headCoeff : Finset ι → ℝ := fun T ↦
    ∑ U ∈ F, if T ⊆ U then A U * (-1 : ℝ) ^ U.card * (-1 : ℝ) ^ T.card else 0
  refine ⟨headCoeff, ?_⟩
  intro bits
  have hsum (U : Finset ι) (hU : U ∈ F) :
      (∑ T ∈ F,
        (if T ⊆ U then A U * (-1 : ℝ) ^ U.card * (-1 : ℝ) ^ T.card else 0) /
          (d - ∑ i ∈ T, w i * boolToReal (bits i))) =
      A U * (-1 : ℝ) ^ U.card * faceAlternation U
        (fun T ↦ 1 / (d - ∑ i ∈ T, w i * boolToReal (bits i))) := by
    have hp : U.powerset ⊆ F := fun T hT ↦ hdown U hU T (Finset.mem_powerset.mp hT)
    calc
      _ = ∑ T ∈ U.powerset,
          (if T ⊆ U then A U * (-1 : ℝ) ^ U.card * (-1 : ℝ) ^ T.card else 0) /
            (d - ∑ i ∈ T, w i * boolToReal (bits i)) := by
        symm
        apply Finset.sum_subset hp
        intro T hT hn
        have hn' : ¬ T ⊆ U := fun h ↦ hn (Finset.mem_powerset.mpr h)
        simp [hn']
      _ = ∑ T ∈ U.powerset,
          A U * (-1 : ℝ) ^ U.card * ((-1 : ℝ) ^ T.card *
            (1 / (d - ∑ i ∈ T, w i * boolToReal (bits i)))) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [ite_eq_left (Finset.mem_powerset.mp hT)]
        ring
      _ = _ := by simp only [faceAlternation, Finset.mul_sum]
  calc
    _ = ∑ T ∈ F, ∑ U ∈ F,
        (if T ⊆ U then A U * (-1 : ℝ) ^ U.card * (-1 : ℝ) ^ T.card else 0) /
          (d - ∑ i ∈ T, w i * boolToReal (bits i)) := by
      simp only [headCoeff, Finset.sum_div]
    _ = ∑ U ∈ F, ∑ T ∈ F,
        (if T ⊆ U then A U * (-1 : ℝ) ^ U.card * (-1 : ℝ) ^ T.card else 0) /
          (d - ∑ i ∈ T, w i * boolToReal (bits i)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [hsum U hU, mul_assoc, jointCell_filtered_reciprocal_eq]
      have hK : jointCellFilteredKernel U w d ≠ 0 :=
        (jointCell_filtered_kernel_pos U w d (hw U hU) (hd U hU)).ne'
      split_ifs <;> simp [A, hK]

omit [DecidableEq ι] in
/-- Every reciprocal appearing in a filtered kernel has a positive denominator
on the entire Boolean cube when the total nonnegative slope budget is below d. -/
theorem jointCell_filtered_denominator_pos (s t : Finset ι) (w : ι → ℝ) (d : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hd : ∑ i ∈ s, w i < d)
    (ht : t ⊆ s) (bits : ι → Bool) :
    0 < d - ∑ i ∈ t, w i * boolToReal (bits i) := by
  have hterm : ∀ i ∈ t, w i * boolToReal (bits i) ≤ w i := by
    intro i hi
    cases bits i <;> simp [boolToReal, hw i (ht hi)]
  have hsum : (∑ i ∈ t, w i * boolToReal (bits i)) ≤ ∑ i ∈ s, w i := by
    calc
      _ ≤ ∑ i ∈ t, w i := Finset.sum_le_sum hterm
      _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum_of_subset_of_nonneg ht
        (fun i hi _ ↦ hw i hi)
  linarith

/-- A weak reverse ratio becomes one original-model atom without changing
any value on a prescribed Hamming-weight slice. This fills every zero slope
with a strict negative slope while preserving full-cube positivity. -/
theorem jointCell_exists_atom_on_weight_slice {n : ℕ}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (k : ℕ)
    (hb : ∀ i, b i ≤ 0) (hmargin : ∑ i, -b i < b₀) :
    ∃ atom : FracAtom n, ∀ bits : Fin n → Bool,
      (∑ i, boolToReal (bits i)) = (k : ℝ) →
      atom.eval bits = affineValue a₀ a bits / affineValue b₀ b bits := by
  let margin : ℝ := b₀ - ∑ i, -b i
  have hm : 0 < margin := sub_pos.mpr hmargin
  let ε : ℝ := margin / (2 * ((n : ℝ) + 1))
  have he : 0 < ε := by dsimp [ε]; positivity
  have hprod : 2 * ((n : ℝ) + 1) * ε = margin := by
    dsimp [ε]
    field_simp
  let B : ℝ := b₀ + (k : ℝ) * ε
  let bs : Fin n → ℝ := fun i ↦ b i - ε
  have hbs : ∀ i, bs i < 0 := by intro i; dsimp [bs]; linarith [hb i]
  have hb₀ : 0 < b₀ := by
    have hs : 0 ≤ ∑ i, -b i := Finset.sum_nonneg (fun i _ ↦ neg_nonneg.mpr (hb i))
    linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : (∑ i, -bs i) = (∑ i, -b i) + (n : ℝ) * ε := by
    calc
      _ = ∑ i, (-b i + ε) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [bs]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbudget : ∑ i, -bs i < B := by
    rw [hs]
    have hke : 0 ≤ (k : ℝ) * ε := mul_nonneg (Nat.cast_nonneg k) he.le
    dsimp [B]
    dsimp [margin] at hprod
    nlinarith
  let atom := FracAtom.ofNegativeAffineRatio a₀ a B bs hB hbs hbudget
  refine ⟨atom, ?_⟩
  intro bits hweight
  rw [FracAtom.ofNegativeAffineRatio_eval]
  congr 1
  simp only [affineValue, B, bs, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hweight]
  ring

end HeadComplexity.AxisZeroGluing
