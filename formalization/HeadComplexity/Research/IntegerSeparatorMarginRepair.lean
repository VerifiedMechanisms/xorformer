import HeadComplexity.Research.RelativeMarginQuantifiers
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.LowComplexity
import HeadComplexity.Polynomial.StrictSign
import Mathlib

set_option linter.style.header false

/-!
Quantitative integer-separator infrastructure for positive margin repair.
All vectors are evaluated on finite bounded-integer feature matrices.
No unrestricted many-head repair is asserted here.
-/

noncomputable section

namespace HeadComplexity.IntegerSeparatorMarginRepair

open Finset Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {d : ℕ}

def active (A : Matrix ι (Fin d) ℝ) (w : Fin d → ℝ) : Finset ι :=
  Finset.univ.filter fun i ↦ dotProduct (A i) w = 1

def feasible (A : Matrix ι (Fin d) ℝ) (w : Fin d → ℝ) : Prop :=
  ∀ i, 1 ≤ dotProduct (A i) w

lemma dot_dual (f : Module.Dual ℝ (Fin d → ℝ)) (a : Fin d → ℝ) :
    dotProduct a (fun j ↦ f (Pi.single j 1)) = f a := by
  calc
    _ = f (∑ j : Fin d, a j • Pi.single j (1 : ℝ)) := by
      simp [dotProduct, map_sum, map_smul]
    _ = f a := by
      congr 1
      ext j
      simp [Pi.single_apply, Pi.smul_apply]

/-- Moving in a direction annihilating the active rows reaches a new active
row without losing any old one, provided some row decreases. -/
theorem active_increase (A : Matrix ι (Fin d) ℝ) (w v : Fin d → ℝ)
    (hw : feasible A w)
    (hactive : ∀ i ∈ active A w, dotProduct (A i) v = 0)
    (hnegative : ∃ i, dotProduct (A i) v < 0) :
    ∃ w', feasible A w' ∧ active A w ⊂ active A w' := by
  classical
  let neg : Finset ι := Finset.univ.filter fun i ↦ dotProduct (A i) v < 0
  have hneg : neg.Nonempty := by
    rcases hnegative with ⟨i, hi⟩
    exact ⟨i, by simp [neg, hi]⟩
  let ratio : ι → ℝ := fun i ↦
    (dotProduct (A i) w - 1) / (-dotProduct (A i) v)
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image neg ratio hneg
  have hjneg : dotProduct (A j) v < 0 := (Finset.mem_filter.mp hj).2
  have hstrict : ∀ i ∈ neg, 1 < dotProduct (A i) w := by
    intro i hi
    have hineg : dotProduct (A i) v < 0 := (Finset.mem_filter.mp hi).2
    have hne : dotProduct (A i) w ≠ 1 := by
      intro heq
      have hzero := hactive i (by simp [active, heq])
      linarith
    exact lt_of_le_of_ne (hw i) hne.symm
  have ht : 0 < ratio j := div_pos (sub_pos.mpr (hstrict j hj)) (neg_pos.mpr hjneg)
  let w' : Fin d → ℝ := w + ratio j • v
  have heval : ∀ i, dotProduct (A i) w' =
      dotProduct (A i) w + ratio j * dotProduct (A i) v := by
    intro i
    simp [w', dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hw' : feasible A w' := by
    intro i
    rw [heval]
    by_cases hi : dotProduct (A i) v < 0
    · have hm := hmin i (by simp [neg, hi])
      have hm' : ratio j * (-dotProduct (A i) v) ≤ dotProduct (A i) w - 1 :=
        (le_div_iff₀ (neg_pos.mpr hi)).mp hm
      nlinarith
    · have hp : 0 ≤ ratio j * dotProduct (A i) v :=
        mul_nonneg ht.le (le_of_not_gt hi)
      linarith [hw i]
  have hsub : active A w ⊆ active A w' := by
    intro i hi
    have heq : dotProduct (A i) w = 1 := (Finset.mem_filter.mp hi).2
    simp [active, heval, heq, hactive i hi]
  have hjnew : j ∈ active A w' := by
    have heq : ratio j * (-dotProduct (A j) v) = dotProduct (A j) w - 1 := by
      dsimp [ratio]
      exact div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hjneg))
    have hval : dotProduct (A j) w' = 1 := by rw [heval]; nlinarith
    simp [active, hval]
  have hjold : j ∉ active A w := by
    intro hjold
    have hz := hactive j hjold
    linarith
  exact ⟨w', hw', Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun heq ↦ hjold (heq.symm ▸ hjnew)⟩⟩


/-- Every nonempty feasible system with spanning rows has a feasible point
whose active rows span the ambient space. -/
theorem exists_spanning_active (A : Matrix ι (Fin d) ℝ)
    (hspan : Submodule.span ℝ (Set.range A) = ⊤)
    (hex : ∃ w, feasible A w) :
    ∃ w, feasible A w ∧
      Submodule.span ℝ (A '' (active A w : Set ι)) = ⊤ := by
  classical
  let pats : Finset (Finset ι) := Finset.univ.filter fun s ↦
    ∃ w, feasible A w ∧ active A w = s
  have hpats : pats.Nonempty := by
    rcases hex with ⟨w, hw⟩
    refine ⟨active A w, ?_⟩
    simp only [pats, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, rfl⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image pats Finset.card hpats
  obtain ⟨w, hw, hws⟩ := (Finset.mem_filter.mp hs).2
  refine ⟨w, hw, ?_⟩
  by_contra hn
  let p : Submodule ℝ (Fin d → ℝ) :=
    Submodule.span ℝ (A '' (active A w : Set ι))
  obtain ⟨f, hfne, hfmap⟩ := p.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hn) inferInstance
  have hfrow : ∃ i, f (A i) ≠ 0 := by
    by_contra h
    have hzero : ∀ i, f (A i) = 0 := by simpa using h
    have hker : Submodule.span ℝ (Set.range A) ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hzero i
    rw [hspan] at hker
    apply hfne
    ext a
    exact hker (Submodule.mem_top)
  have hfact : ∀ i ∈ active A w, f (A i) = 0 := by
    intro i hi
    have hm : A i ∈ p := Submodule.subset_span ⟨i, hi, rfl⟩
    have hm' : f (A i) ∈ p.map f := Submodule.mem_map.mpr ⟨A i, hm, rfl⟩
    simpa only [hfmap, Submodule.mem_bot] using hm'
  let v : Fin d → ℝ := fun j ↦ f (Pi.single j 1)
  have hdot : ∀ i, dotProduct (A i) v = f (A i) := fun i ↦ dot_dual f (A i)
  obtain ⟨i, hi⟩ := hfrow
  have hincrease : ∃ w', feasible A w' ∧ active A w ⊂ active A w' := by
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · apply active_increase A w v hw
      · intro j hj
        rw [hdot, hfact j hj]
      · exact ⟨i, by rwa [hdot]⟩
    · apply active_increase A w (-v) hw
      · intro j hj
        rw [dotProduct_neg, hdot, hfact j hj, neg_zero]
      · exact ⟨i, by rw [dotProduct_neg, hdot]; linarith⟩
  obtain ⟨w', hw', hproper⟩ := hincrease
  have hp' : active A w' ∈ pats := by
    simp only [pats, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w', hw', rfl⟩
  have hle := hmax (active A w') hp'
  have hlt := Finset.card_lt_card hproper
  rw [← hws] at hle
  omega


omit [Fintype ι] in
/-- Select a square invertible matrix of active constraints. -/
theorem exists_active_matrix [Finite ι] (A : Matrix ι (Fin d) ℝ)
    (hspan : Submodule.span ℝ (Set.range A) = ⊤)
    (hex : ∃ w, feasible A w) :
    ∃ (w : Fin d → ℝ) (rows : Fin d → ι), feasible A w ∧
      (∀ j, dotProduct (A (rows j)) w = 1) ∧
      Matrix.det (fun j k ↦ A (rows j) k : Matrix (Fin d) (Fin d) ℝ) ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨w, hw, hactive⟩ := exists_spanning_active A hspan hex
  let v : {i // i ∈ active A w} → (Fin d → ℝ) := fun i ↦ A i
  have hrange : Set.range v = A '' (active A w : Set ι) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hvspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    rw [hrange, hactive]
  obtain ⟨κ, a, hainj, haspan, hali⟩ := exists_linearIndependent' ℝ v
  let : Fintype κ := Fintype.ofInjective a hainj
  let b : Module.Basis κ ℝ (Fin d → ℝ) := Module.Basis.mk hali (by
    rw [haspan, hvspan])
  have hcard : Fintype.card κ = d := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : Fin d ≃ κ := Fintype.equivOfCardEq (by simp [hcard])
  let rows : Fin d → ι := fun j ↦ (a (e j)).val
  refine ⟨w, rows, hw, ?_, ?_⟩
  · intro j
    exact (Finset.mem_filter.mp (a (e j)).property).2
  · apply Matrix.nonsingular_iff_det_ne_zero.mp
    apply Matrix.Nonsingular.of_linearIndependent_row
    exact hali.comp e e.injective

/-- The elementary Leibniz bound is enough for a singly exponential repair. -/
theorem abs_det_le_factorial (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) : |A.det| ≤ (d.factorial : ℝ) := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d),
        |Equiv.Perm.sign σ • ∏ i, A (σ i) i| := abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin d), ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [Units.smul_def, abs_mul, abs_prod, abs_unit_intCast]
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ hA (σ i) i)
    _ = (d.factorial : ℝ) := by simp [Fintype.card_perm]


lemma cramer_of_mulVec (R : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ)
    (hw : R *ᵥ w = fun _ ↦ 1) : R.cramer (fun _ ↦ 1) = R.det • w := by
  rw [← hw, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

lemma cast_cramer (R : Matrix (Fin d) (Fin d) ℤ) (j : Fin d) :
    ((R.cramer (fun _ ↦ 1) j : ℤ) : ℝ) =
      (R.map (fun z : ℤ ↦ (z : ℝ))).cramer (fun _ ↦ 1) j := by
  simp only [Matrix.cramer_apply, Int.cast_det]
  congr 1
  ext i k
  by_cases hkj : k = j
  · simp [Matrix.updateCol, Matrix.map, hkj]
  · simp [Matrix.updateCol, Matrix.map, hkj]

omit [Fintype ι] in
/-- A spanning bounded-integer feature matrix admitting a real separator
admits an integer separator with coefficients bounded by the dimension factorial. -/
theorem exists_bounded_integer_separator [Finite ι] (A : Matrix ι (Fin d) ℤ)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ 1)
    (hspan : Submodule.span ℝ (Set.range (A.map (fun z : ℤ ↦ (z : ℝ)))) = ⊤)
    (hex : ∃ w, feasible (A.map (fun z : ℤ ↦ (z : ℝ))) w) :
    ∃ a : Fin d → ℤ,
      (∀ i, 1 ≤ dotProduct ((A.map (fun z : ℤ ↦ (z : ℝ))) i)
        (fun j ↦ (a j : ℝ))) ∧
      (∀ j, |(a j : ℝ)| ≤ (d.factorial : ℝ)) := by
  classical
  let AR : Matrix ι (Fin d) ℝ := A.map (fun z : ℤ ↦ (z : ℝ))
  obtain ⟨w, rows, hw, hrows, hdet⟩ := exists_active_matrix AR hspan hex
  let RZ : Matrix (Fin d) (Fin d) ℤ := fun i j ↦ A (rows i) j
  let R : Matrix (Fin d) (Fin d) ℝ := RZ.map (fun z : ℤ ↦ (z : ℝ))
  have hRdet : R.det ≠ 0 := hdet
  have hRw : R *ᵥ w = fun _ ↦ 1 := by
    ext i
    exact hrows i
  have hC := cramer_of_mulVec R w hRw
  have hcastdet : (RZ.det : ℝ) = R.det := Int.cast_det RZ
  have hdetZ : RZ.det ≠ 0 := by
    intro hz
    apply hRdet
    rw [← hcastdet, hz, Int.cast_zero]
  have hd1 : 1 ≤ |R.det| := by
    have hzpos : (0 : ℤ) < |RZ.det| := abs_pos.mpr hdetZ
    have hz1 : (1 : ℤ) ≤ |RZ.det| := by omega
    rw [← hcastdet, ← Int.cast_abs]
    exact_mod_cast hz1
  let a : Fin d → ℤ := if 0 < R.det then RZ.cramer (fun _ ↦ 1)
    else -RZ.cramer (fun _ ↦ 1)
  have ha : (fun j ↦ (a j : ℝ)) = |R.det| • w := by
    ext j
    have hj := congrFun hC j
    simp only [Pi.smul_apply, smul_eq_mul] at hj ⊢
    by_cases hpos : 0 < R.det
    · simp only [a, ite_eq_left hpos, cast_cramer]
      rw [hj, abs_of_pos hpos]
    · have hneg : R.det < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hRdet
      simp only [a, ite_eq_right hpos, Pi.neg_apply, Int.cast_neg, cast_cramer]
      rw [hj, abs_of_neg hneg]
      ring
  refine ⟨a, ?_, ?_⟩
  · intro i
    rw [ha, dotProduct_smul, smul_eq_mul]
    calc
      1 ≤ |R.det| := hd1
      _ ≤ |R.det| * dotProduct (AR i) w := by
        nlinarith [hw i, abs_nonneg R.det]
  · intro j
    have hbound : |R.cramer (fun _ ↦ 1) j| ≤ (d.factorial : ℝ) := by
      rw [Matrix.cramer_apply]
      apply abs_det_le_factorial
      intro i k
      by_cases hkj : k = j
      · simp [Matrix.updateCol, hkj]
      · simpa [Matrix.updateCol, hkj, R, RZ, Matrix.map] using hA (rows i) k
    by_cases hpos : 0 < R.det
    · simpa only [a, ite_eq_left hpos, cast_cramer] using hbound
    · simpa only [a, ite_eq_right hpos, Pi.neg_apply, Int.cast_neg, abs_neg,
        cast_cramer] using hbound


/-- The integer affine feature vector of a Boolean input. -/
def cubeFeature (n : ℕ) (x : Fin n → Bool) : Fin (n + 1) → ℤ :=
  Fin.cases 1 (fun i ↦ if x i then 1 else 0)

lemma cubeFeature_zero (n : ℕ) :
    (fun j ↦ (cubeFeature n (fun _ ↦ false) j : ℝ)) = Pi.single 0 1 := by
  ext j
  refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp [cubeFeature]

lemma cubeFeature_single (n : ℕ) (i : Fin n) :
    (fun j ↦ (cubeFeature n (fun k ↦ decide (k = i)) j : ℝ)) =
      Pi.single 0 1 + Pi.single i.succ 1 := by
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [cubeFeature]
  · by_cases hki : k = i <;> simp [cubeFeature, hki, Fin.succ_inj]

lemma cubeFeature_span (n : ℕ) :
    Submodule.span ℝ (Set.range (fun x : Fin n → Bool ↦
      fun j ↦ (cubeFeature n x j : ℝ))) = ⊤ := by
  let p : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ
    (Set.range (fun x : Fin n → Bool ↦ fun j ↦ (cubeFeature n x j : ℝ)))
  have hzero : Pi.single 0 (1 : ℝ) ∈ p := by
    rw [← cubeFeature_zero n]
    exact Submodule.subset_span ⟨fun _ ↦ false, rfl⟩
  have hsingle : ∀ i : Fin n, Pi.single i.succ (1 : ℝ) ∈ p := by
    intro i
    have hsum : Pi.single 0 (1 : ℝ) + Pi.single i.succ 1 ∈ p := by
      rw [← cubeFeature_single n i]
      exact Submodule.subset_span ⟨fun k ↦ decide (k = i), rfl⟩
    simpa using p.sub_mem hsum hzero
  have hb : ∀ j : Fin (n + 1), Pi.single j (1 : ℝ) ∈ p := by
    intro j
    exact Fin.cases hzero hsingle j
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin (n + 1))).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change (Pi.basisFun ℝ (Fin (n + 1))) j ∈ p
  simpa only [Pi.basisFun_apply] using hb j

/-- Signed cube rows retain the full affine feature span. -/
lemma signed_cubeFeature_span (n : ℕ) (f : (Fin n → Bool) → Bool) :
    Submodule.span ℝ (Set.range (fun x : Fin n → Bool ↦
      fun j ↦ (((if f x then (1 : ℤ) else -1) * cubeFeature n x j : ℤ) : ℝ))) = ⊤ := by
  let p : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ
    (Set.range (fun x : Fin n → Bool ↦ fun j ↦
      (((if f x then (1 : ℤ) else -1) * cubeFeature n x j : ℤ) : ℝ)))
  apply top_unique
  rw [← cubeFeature_span n]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  have hm : (fun j ↦ (((if f x then (1 : ℤ) else -1) * cubeFeature n x j : ℤ) : ℝ)) ∈ p :=
    Submodule.subset_span ⟨x, rfl⟩
  change (fun j ↦ (cubeFeature n x j : ℝ)) ∈ p
  cases hfx : f x
  · simp only [hfx, Bool.false_eq_true, ite_false, neg_one_mul, Int.cast_neg] at hm
    convert p.neg_mem hm using 1
    ext j
    simp
  · simpa only [hfx, ite_true, one_mul] using hm

lemma cubeFeature_dot (n : ℕ) (x : Fin n → Bool) (a : Fin (n + 1) → ℝ) :
    dotProduct (fun j ↦ (cubeFeature n x j : ℝ)) a =
      affineValue (a 0) (fun i ↦ a i.succ) x := by
  simp only [dotProduct, Fin.sum_univ_succ, cubeFeature, Fin.cases_zero,
    Fin.cases_succ, Int.cast_one, one_mul, affineValue]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp [boolToReal]


lemma signed_cubeFeature_dot (n : ℕ) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (a : Fin (n + 1) → ℝ) :
    dotProduct (fun j ↦ (((if f x then (1 : ℤ) else -1) *
      cubeFeature n x j : ℤ) : ℝ)) a =
      signedLabel f x * affineValue (a 0) (fun i ↦ a i.succ) x := by
  rw [← cubeFeature_dot]
  cases hfx : f x
  · simp only [hfx, Bool.false_eq_true, ite_false, neg_one_mul, Int.cast_neg,
      signedLabel]
    exact neg_dotProduct _ _
  · simp [signedLabel, hfx]

/-- Every linear threshold table has a bounded integer affine separator. -/
theorem exists_bounded_integer_affine (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : isLTF f) :
    ∃ a : Fin (n + 1) → ℤ,
      (∀ x, 1 ≤ signedLabel f x * affineValue (a 0)
        (fun i ↦ (a i.succ : ℝ)) x) ∧
      (∀ j, |(a j : ℝ)| ≤ ((n + 1).factorial : ℝ)) := by
  classical
  obtain ⟨P, hPdeg, hPsign⟩ := exists_strictSignRep_of_ThresholdDegLE
    ((ThresholdDegLE_one_iff_isLTF f).mpr hf)
  let w : Fin (n + 1) → ℝ := Fin.cases (P.coeff 0)
    (fun i ↦ P.coeff (Finsupp.single i 1))
  let A : Matrix (Fin n → Bool) (Fin (n + 1)) ℤ := fun x j ↦
    (if f x then (1 : ℤ) else -1) * cubeFeature n x j
  let AR : Matrix (Fin n → Bool) (Fin (n + 1)) ℝ := A.map (fun z : ℤ ↦ (z : ℝ))
  have heval : ∀ x, dotProduct (AR x) w =
      signedLabel f x * MvPolynomial.eval (cubePoint x) P := by
    intro x
    rw [show AR x = (fun j ↦ (((if f x then (1 : ℤ) else -1) *
      cubeFeature n x j : ℤ) : ℝ)) from rfl, signed_cubeFeature_dot]
    congr 1
    simpa [w, affineValue] using (eval_cubePoint_affine P hPdeg x).symm
  have hpos : ∀ x, 0 < dotProduct (AR x) w := by
    intro x
    rw [heval]
    cases hfx : f x
    · have hp := (hPsign x).2 hfx
      simp [signedLabel, hfx]
      linarith
    · simpa [signedLabel, hfx] using (hPsign x).1 hfx
  let margin : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun x : Fin n → Bool ↦ dotProduct (AR x) w)
  have hmpos : 0 < margin := by
    simp only [margin, Finset.lt_inf'_iff, Finset.mem_univ, true_implies]
    exact hpos
  have hmargin : ∀ x, margin ≤ dotProduct (AR x) w := fun x ↦
    Finset.inf'_le _ (Finset.mem_univ x)
  have hfeasible : ∃ u, feasible AR u := by
    refine ⟨margin⁻¹ • w, fun x ↦ ?_⟩
    rw [dotProduct_smul, smul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_left (hmargin x) (inv_pos.mpr hmpos).le
    simpa [hmpos.ne'] using hmul
  have hA : ∀ x j, |(A x j : ℝ)| ≤ 1 := by
    intro x j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · cases hfx : f x <;> simp [A, cubeFeature, hfx]
    · cases hfx : f x <;> cases hxi : x i <;> simp [A, cubeFeature, hfx, hxi]
  obtain ⟨a, ha, habound⟩ := exists_bounded_integer_separator A hA
    (signed_cubeFeature_span n f) hfeasible
  refine ⟨a, fun x ↦ ?_, habound⟩
  have hx := ha x
  change 1 ≤ dotProduct (fun j ↦ (((if f x then (1 : ℤ) else -1) *
    cubeFeature n x j : ℤ) : ℝ)) (fun j ↦ (a j : ℝ)) at hx
  rw [signed_cubeFeature_dot] at hx
  exact hx


/-- An explicit positive margin depending only on input dimension. -/
def oneHeadRepairMargin (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ 2 * ((n + 1).factorial : ℝ))

lemma oneHeadRepairMargin_pos (n : ℕ) : 0 < oneHeadRepairMargin n := by
  unfold oneHeadRepairMargin
  have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  positivity

/-- The repair uses one genuine positive-denominator head, zero bias, and
exactly the full-cube head-amplitude relative margin. -/
theorem hasRelativeMargin_of_isLTF (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : isLTF f) : RelativeMarginQuantifiers.HasRelativeMargin n 1 f
      (oneHeadRepairMargin n) := by
  classical
  obtain ⟨a, ha, habound⟩ := exists_bounded_integer_affine n f hf
  let d : ℝ := n + 1
  let M : ℝ := (n + 1).factorial
  have hd : 0 < d := by dsimp [d]; positivity
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast Nat.factorial_pos (n + 1)
  let atom : FracAtom n := FracAtom.ofPositiveAffineRatio (a 0)
    (fun i ↦ (a i.succ : ℝ)) 1 (fun _ ↦ 1) one_pos (fun _ ↦ one_pos)
  have hden : ∀ x : Fin n → Bool,
      1 ≤ affineValue 1 (fun _ ↦ 1) x ∧ affineValue 1 (fun _ ↦ 1) x ≤ d := by
    intro x
    have hl : ∀ i, 0 ≤ boolToReal (x i) := by intro i; cases x i <;> norm_num [boolToReal]
    have hu : ∀ i, boolToReal (x i) ≤ 1 := by intro i; cases x i <;> norm_num [boolToReal]
    constructor
    · simpa [affineValue] using add_le_add_left (Finset.sum_nonneg fun i _ ↦ hl i) 1
    · have hs : (∑ i, boolToReal (x i)) ≤ (n : ℝ) := by
        simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hu i)
      simpa [affineValue, d, add_comm] using add_le_add_left hs 1
  have hnum : ∀ x : Fin n → Bool,
      |affineValue (a 0) (fun i ↦ (a i.succ : ℝ)) x| ≤ d * M := by
    intro x
    have hterm : ∀ i, |(a i.succ : ℝ) * boolToReal (x i)| ≤ M := by
      intro i
      cases hxi : x i
      · simp [boolToReal, hM.le]
      · simpa [boolToReal, hxi, M] using habound i.succ
    calc
      _ ≤ |(a 0 : ℝ)| + |∑ i, (a i.succ : ℝ) * boolToReal (x i)| := abs_add_le _ _
      _ ≤ M + ∑ i, |(a i.succ : ℝ) * boolToReal (x i)| :=
        add_le_add (habound 0) (abs_sum_le_sum_abs _ _)
      _ ≤ M + ∑ _i : Fin n, M := add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ hterm i)
      _ = d * M := by simp [d]; ring
  have hatom : ∀ x, |atom.eval x| ≤ d * M := by
    intro x
    have hD : 0 < affineValue 1 (fun _ ↦ 1) x := lt_of_lt_of_le one_pos (hden x).1
    rw [show atom.eval x = affineValue (a 0) (fun i ↦ (a i.succ : ℝ)) x /
      affineValue 1 (fun _ ↦ 1) x from FracAtom.ofPositiveAffineRatio_eval ..]
    rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    nlinarith [hnum x, (hden x).1, mul_pos hd hM]
  have hsigned : ∀ x, 1 / d ≤ signedLabel f x * atom.eval x := by
    intro x
    have hD : 0 < affineValue 1 (fun _ ↦ 1) x := lt_of_lt_of_le one_pos (hden x).1
    rw [show atom.eval x = affineValue (a 0) (fun i ↦ (a i.succ : ℝ)) x /
      affineValue 1 (fun _ ↦ 1) x from FracAtom.ofPositiveAffineRatio_eval ..]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hd hD).mpr
    nlinarith [ha x, (hden x).2]
  let phi : Fin 1 → FracAtom n := fun _ ↦ atom
  have hscore : ∀ x, RelativeMarginQuantifiers.score phi 0 x = atom.eval x := by
    intro x
    simp [RelativeMarginQuantifiers.score, phi]
  have hstrict : RelativeMarginQuantifiers.StrictlyRepresents f phi 0 := by
    intro x
    rw [hscore]
    exact (div_pos one_pos hd).trans_le (hsigned x)
  have hamp : RelativeMarginQuantifiers.amplitude phi 0 ≤ d * M := by
    simp only [RelativeMarginQuantifiers.amplitude, phi, abs_zero, zero_add,
      Fin.sum_univ_one]
    exact Finset.sup'_le _ _ (fun x _ ↦ hatom x)
  refine ⟨phi, 0, hstrict, ?_⟩
  apply (RelativeMarginQuantifiers.le_relativeMargin_iff hstrict).mpr
  intro x
  calc
    oneHeadRepairMargin n * RelativeMarginQuantifiers.amplitude phi 0 ≤
        oneHeadRepairMargin n * (d * M) :=
      mul_le_mul_of_nonneg_left hamp (oneHeadRepairMargin_pos n).le
    _ = 1 / d := by
      dsimp [oneHeadRepairMargin, d, M]
      field_simp
    _ ≤ signedLabel f x * RelativeMarginQuantifiers.score phi 0 x := by
      rw [hscore]
      exact hsigned x

/-- Same-width quantitative repair for the original unrestricted one-head model. -/
theorem one_head_repair (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n 1 f) :
    RelativeMarginQuantifiers.HasRelativeMargin n 1 f (oneHeadRepairMargin n) :=
  hasRelativeMargin_of_isLTF n f (isLTF_of_computable_one f hf)

/-- The same repair when the original minimum head complexity is at most one. -/
theorem repair_of_HStar_le_one (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : HStar n f ≤ 1) :
    RelativeMarginQuantifiers.HasRelativeMargin n 1 f (oneHeadRepairMargin n) :=
  one_head_repair n f (computableWithHeadsN_mono hf (HStar_computable f))

#print axioms exists_bounded_integer_separator
#print axioms exists_bounded_integer_affine
#print axioms hasRelativeMargin_of_isLTF
#print axioms one_head_repair
#print axioms repair_of_HStar_le_one

end HeadComplexity.IntegerSeparatorMarginRepair
