import HeadComplexity.Research.LinearCylinderCompiler
import HeadComplexity.Research.CauchyMomentInterpolation
import HeadComplexity.Research.UniformMarginCompiler
import HeadComplexity.Research.LowDegreeMarginRepair

set_option linter.style.header false

/-!
Quantitative amplitude control for the linear mixed-cylinder compiler.
The residue bound is explicit and uses integer-separated positive poles.
All approximation and norm estimates concern the full Boolean cube.
-/

noncomputable section

namespace HeadComplexity.LinearCylinderMargin

open Finset Polynomial LinearCylinderCompiler CoherentFaceGating
open RelativeMarginQuantifiers UniformMarginCompiler
open scoped BigOperators

def pole (p : ℕ) (h : Fin (p + 1)) : ℝ := h.val + 1
def scale (p : ℕ) : ℝ :=
  (∏ h : Fin (p + 1), ((p : ℝ) + pole p h)) /
    ∏ j : Fin p, ((p : ℝ) - j.val)
def indicatorPolynomial (p : ℕ) : Polynomial ℝ :=
  C (scale p) * ∏ j : Fin p, (X - C (j.val : ℝ))
def coefficientBound (p : ℕ) : ℝ := (2 * (p : ℝ) + 2) ^ (2 * p + 1)
def massBound (p : ℕ) : ℝ := ((p : ℝ) + 1) * coefficientBound p
def residue (p : ℕ) (h : Fin (p + 1)) : ℝ :=
  CauchyMomentInterpolation.residue (pole p) (indicatorPolynomial p) h

theorem pole_pos (p : ℕ) (h : Fin (p + 1)) : 0 < pole p h := by
  dsimp [pole]
  positivity

theorem pole_one_le (p : ℕ) (h : Fin (p + 1)) : 1 ≤ pole p h := by
  dsimp [pole]
  have h := Nat.cast_nonneg (α := ℝ) h.val
  linarith

theorem pole_injective (p : ℕ) : Function.Injective (pole p) := by
  intro i j hij
  apply Fin.ext
  dsimp [pole] at hij
  exact_mod_cast (add_right_cancel hij : (i.val : ℝ) = j.val)

theorem base_product_one_le (p : ℕ) :
    1 ≤ ∏ j : Fin p, ((p : ℝ) - j.val) := by
  apply one_le_prod₀
  intro j _
  have hj : (j.val : ℝ) + 1 ≤ p := by exact_mod_cast j.isLt
  linarith

theorem scale_nonneg (p : ℕ) : 0 ≤ scale p := by
  unfold scale
  apply div_nonneg
  · exact prod_nonneg fun h _ ↦ by have hp := pole_pos p h; positivity
  · exact le_trans zero_le_one (base_product_one_le p)

theorem scale_le (p : ℕ) : scale p ≤ (2 * (p : ℝ) + 2) ^ (p + 1) := by
  unfold scale
  have hb := base_product_one_le p
  have hnum : 0 ≤ ∏ h : Fin (p + 1), ((p : ℝ) + pole p h) :=
    prod_nonneg fun h _ ↦ by have hp := pole_pos p h; positivity
  calc
    _ ≤ (∏ h : Fin (p + 1), ((p : ℝ) + pole p h)) / 1 :=
      div_le_div_of_nonneg_left hnum zero_lt_one hb
    _ = ∏ h : Fin (p + 1), ((p : ℝ) + pole p h) := div_one _
    _ ≤ ∏ _h : Fin (p + 1), (2 * (p : ℝ) + 2) := by
      apply prod_le_prod₀
      · intro h _; have hp := pole_pos p h; positivity
      · intro h _
        have hh : (h.val : ℝ) ≤ p := by exact_mod_cast Nat.le_of_lt_succ h.isLt
        dsimp [pole]
        linarith
    _ = _ := by simp

theorem indicatorPolynomial_natDegree_le (p : ℕ) :
    (indicatorPolynomial p).natDegree ≤ p := by
  unfold indicatorPolynomial
  apply (natDegree_C_mul_le _ _).trans
  calc
    _ ≤ ∑ j : Fin p, (X - C (j.val : ℝ)).natDegree := natDegree_prod_le _ _
    _ = p := by
      simp only [natDegree_X_sub_C, sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]

theorem indicatorPolynomial_eval_top (p : ℕ) :
    (indicatorPolynomial p).eval (p : ℝ) =
      ∏ h : Fin (p + 1), ((p : ℝ) + pole p h) := by
  have hb : (∏ j : Fin p, ((p : ℝ) - j.val)) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (base_product_one_le p))
  simp only [indicatorPolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact div_mul_cancel₀ _ hb

theorem indicatorPolynomial_eval_lt (p : ℕ) (k : Fin p) :
    (indicatorPolynomial p).eval (k.val : ℝ) = 0 := by
  simp only [indicatorPolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have hz : (∏ j : Fin p, ((k.val : ℝ) - j.val)) = 0 :=
    prod_eq_zero (mem_univ k) (sub_self _)
  rw [hz, mul_zero]

theorem indicatorPolynomial_eval_pole_bound (p : ℕ) (h : Fin (p + 1)) :
    |(indicatorPolynomial p).eval (-pole p h)| ≤ coefficientBound p := by
  simp only [indicatorPolynomial, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
    abs_mul, abs_prod, abs_of_nonneg (scale_nonneg p)]
  have hprod :
      (∏ j : Fin p, |-pole p h - (j.val : ℝ)|) ≤ (2 * (p : ℝ) + 2) ^ p := by
    calc
      _ ≤ ∏ _j : Fin p, (2 * (p : ℝ) + 2) := by
        apply prod_le_prod₀
        · intro j _; exact abs_nonneg _
        · intro j _
          have hh : (h.val : ℝ) ≤ p := by exact_mod_cast Nat.le_of_lt_succ h.isLt
          have hj : (j.val : ℝ) < p := by exact_mod_cast j.isLt
          have hneg : -pole p h - (j.val : ℝ) ≤ 0 := by
            have hpos := pole_pos p h
            have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
            linarith
          rw [abs_of_nonpos hneg]
          dsimp [pole]
          linarith
      _ = _ := by simp
  calc
    _ ≤ (2 * (p : ℝ) + 2) ^ (p + 1) * (2 * (p : ℝ) + 2) ^ p :=
      mul_le_mul (scale_le p) hprod (prod_nonneg fun j _ ↦ abs_nonneg _)
        (by positivity)
    _ = coefficientBound p := by
      rw [← pow_add]
      unfold coefficientBound
      congr 1
      omega

theorem pole_difference_one_le (p : ℕ) {i j : Fin (p + 1)} (hij : i ≠ j) :
    1 ≤ |(-pole p i) - (-pole p j)| := by
  have hv : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
    rw [abs_of_nonneg (by dsimp [pole]; linarith)]
    dsimp [pole]
    linarith
  · have h : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hgt
    rw [abs_of_nonpos (by dsimp [pole]; linarith)]
    dsimp [pole]
    linarith

theorem residue_abs_le (p : ℕ) (h : Fin (p + 1)) :
    |residue p h| ≤ coefficientBound p := by
  have hn : |Lagrange.nodalWeight univ (fun j ↦ -pole p j) h| ≤ 1 := by
    unfold Lagrange.nodalWeight
    rw [abs_prod]
    calc
      _ ≤ ∏ _j ∈ univ.erase h, (1 : ℝ) := by
        apply prod_le_prod₀
        · intro j _; exact abs_nonneg _
        · intro j hj
          rw [abs_inv]
          exact inv_le_one_of_one_le₀
            (pole_difference_one_le p (Ne.symm (mem_erase.mp hj).1))
      _ = 1 := by simp
  unfold residue CauchyMomentInterpolation.residue
  rw [abs_mul]
  calc
    _ ≤ 1 * coefficientBound p :=
      mul_le_mul hn (indicatorPolynomial_eval_pole_bound p h) (abs_nonneg _)
        (by norm_num)
    _ = _ := one_mul _

theorem reciprocal_profile (p : ℕ) (k : Fin (p + 1)) :
    (∑ h : Fin (p + 1), residue p h / ((k.val : ℝ) + pole p h)) =
      if k.val = p then 1 else 0 := by
  have hdeg : (indicatorPolynomial p).degree < (p + 1 : ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast
      (lt_of_le_of_lt (indicatorPolynomial_natDegree_le p) (Nat.lt_succ_self p)))
  rw [show (∑ h, residue p h / ((k.val : ℝ) + pole p h)) =
      (indicatorPolynomial p).eval (k.val : ℝ) / ∏ h, ((k.val : ℝ) + pole p h) by
    exact CauchyMomentInterpolation.sum_residue_div (pole p) (pole_injective p)
      (indicatorPolynomial p) hdeg k.val
      (fun h ↦ ne_of_gt (by have hp := pole_pos p h; positivity))]
  by_cases hk : k.val = p
  · rw [ite_eq_left hk, hk, indicatorPolynomial_eval_top]
    exact div_self (ne_of_gt (prod_pos fun h _ ↦ by have hp := pole_pos p h; positivity))
  · rw [ite_eq_right hk]
    have hkp : k.val < p := by omega
    rw [indicatorPolynomial_eval_lt p ⟨k.val, hkp⟩, zero_div]


variable {n : ℕ}

private theorem affineValue_scale (a r : ℝ) (u : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (r * a) (fun i ↦ r * u i) x = r * affineValue a u x := by
  unfold affineValue
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

/-- Exact decomposition into bounded functions, each uniformly approximable by
one original admissible head. The bound on the affine factor is on the entire
cube, not just on its cylinder. -/
theorem bounded_decomposition_positive (C : CubeCylinder n)
    (a M : ℝ) (u : Fin n → ℝ) (hM : 0 ≤ M)
    (hA : ∀ x, |affineValue a u x| ≤ M) :
    ∃ g : Fin (C.positive.card + 1) → (Fin n → Bool) → ℝ,
      (∀ h, UniformlyOneAtomApproximable (g h)) ∧
      (∀ h x, |g h x| ≤ coefficientBound C.positive.card * M) ∧
      (∀ x, ∑ h, g h x = C.eval x * affineValue a u x) := by
  classical
  let p := C.positive.card
  let g : Fin (p + 1) → (Fin n → Bool) → ℝ := fun h x ↦
    squarefreeMonomial C.negative (flipBits x) *
      (residue p h * affineValue a u x /
        ((selectedWeight C.positive x : ℝ) + pole p h))
  refine ⟨g, ?_, ?_, ?_⟩
  · intro h
    have hd : ∀ x, affineValue (pole p h)
        (fun i ↦ if i ∈ C.positive then 1 else 0) x =
        (selectedWeight C.positive x : ℝ) + pole p h := by
      intro x
      unfold affineValue
      rw [selectedWeight_eq_sum]
      simp only [ite_mul, one_mul, zero_mul]
      rw [← sum_filter]
      simp [add_comm]
    have ha := uniformlyOneAtomApproximable_negativeFace_ratio
      C.negative (residue p h * a) (pole p h) (fun i ↦ residue p h * u i)
      (fun i ↦ if i ∈ C.positive then 1 else 0) (pole_pos p h)
      (fun i ↦ by split_ifs <;> norm_num)
    simpa only [g, affineValue_scale, hd] using ha
  · intro h x
    have hd : 1 ≤ (selectedWeight C.positive x : ℝ) + pole p h := by
      have hw : 0 ≤ (selectedWeight C.positive x : ℝ) := Nat.cast_nonneg _
      linarith [pole_one_le p h]
    have hn : 0 ≤ coefficientBound p * M := by unfold coefficientBound; positivity
    dsimp [g]
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
    calc
      _ ≤ 1 * (coefficientBound p * M / 1) := by
        apply mul_le_mul (LowDegreeMarginRepair.abs_monomial_le_one _ _)
        · exact div_le_div₀ hn
            (mul_le_mul (residue_abs_le p h) (hA x) (abs_nonneg _) (by
              unfold coefficientBound; positivity)) zero_lt_one hd
        · positivity
        · norm_num
      _ = _ := by ring
  · intro x
    have hp := reciprocal_profile p
      ⟨selectedWeight C.positive x, Nat.lt_succ_of_le (selectedWeight_le _ _)⟩
    have heq : (∑ h, g h x) = squarefreeMonomial C.negative (flipBits x) *
        affineValue a u x *
          (if selectedWeight C.positive x = p then 1 else 0) := by
      rw [← hp]
      dsimp [g]
      rw [mul_sum]
      apply sum_congr rfl
      intro h _
      ring
    rw [heq]
    change _ * _ * (if selectedWeight C.positive x = C.positive.card then 1 else 0) = _
    rw [← positiveMonomial_eq_weight_test]
    rw [CubeCylinder.squarefreeMonomial_flipBits]
    unfold CubeCylinder.eval squarefreeMonomial CubeCylinder.negativeSquarefreeMonomial
    ring

/-- The complementary orientation retains the same full-cube amplitude bound. -/
theorem bounded_decomposition_negative (C : CubeCylinder n)
    (a M : ℝ) (u : Fin n → ℝ) (hM : 0 ≤ M)
    (hA : ∀ x, |affineValue a u x| ≤ M) :
    ∃ g : Fin (C.negative.card + 1) → (Fin n → Bool) → ℝ,
      (∀ h, UniformlyOneAtomApproximable (g h)) ∧
      (∀ h x, |g h x| ≤ coefficientBound C.negative.card * M) ∧
      (∀ x, ∑ h, g h x = C.eval x * affineValue a u x) := by
  classical
  let D : CubeCylinder n := ⟨C.negative, C.positive, C.disjoint.symm⟩
  have hD : ∀ x, D.eval (flipBits x) = C.eval x := by
    intro x
    have hbit : ∀ i, boolToReal (flipBits x i) = 1 - boolToReal (x i) := by
      intro i
      cases hx : x i <;> simp [flipBits, boolToReal, hx]
    change (∏ i ∈ C.negative, boolToReal (flipBits x i)) *
      (∏ i ∈ C.positive, (1 - boolToReal (flipBits x i))) =
      (∏ i ∈ C.positive, boolToReal (x i)) *
      (∏ i ∈ C.negative, (1 - boolToReal (x i)))
    simp_rw [hbit, sub_sub_cancel]
    ring
  have hA' : ∀ x, |affineValue (a + ∑ i, u i) (fun i ↦ -u i) x| ≤ M := by
    intro x
    have hflip := AnchoredAtomicDecomposition.affineValue_flipBits a u (flipBits x)
    have h := hA (flipBits x)
    rw [← hflip] at h
    simpa using h
  obtain ⟨g, hg, hbound, hsum⟩ := bounded_decomposition_positive D
    (a + ∑ i, u i) M (fun i ↦ -u i) hM hA'
  refine ⟨fun h x ↦ g h (flipBits x), ?_, ?_, ?_⟩
  · intro h ε hε
    obtain ⟨φ, hφ⟩ := hg h ε hε
    refine ⟨φ.flip, ?_⟩
    intro x
    simpa only [FracAtom.flip_eval] using hφ (flipBits x)
  · intro h x
    exact hbound h (flipBits x)
  · intro x
    simpa only [hD, AnchoredAtomicDecomposition.affineValue_flipBits] using
      hsum (flipBits x)

theorem bounded_decomposition_min (C : CubeCylinder n)
    (a M : ℝ) (u : Fin n → ℝ) (hM : 0 ≤ M)
    (hA : ∀ x, |affineValue a u x| ≤ M) :
    ∃ g : Fin (min C.positive.card C.negative.card + 1) → (Fin n → Bool) → ℝ,
      (∀ h, UniformlyOneAtomApproximable (g h)) ∧
      (∀ h x, |g h x| ≤ coefficientBound (min C.positive.card C.negative.card) * M) ∧
      (∀ x, ∑ h, g h x = C.eval x * affineValue a u x) := by
  by_cases h : C.positive.card ≤ C.negative.card
  · rw [min_eq_left h]
    exact bounded_decomposition_positive C a M u hM hA
  · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact bounded_decomposition_negative C a M u hM hA


/-- An explicit quantitative compiler for signed affine-cylinder scores. The
source score can have arbitrary signed cancellation. The unit signed gap and
all affine amplitude bounds are on the whole cube. -/
theorem hasRelativeMargin_of_cylinder_affine_sum
    {J : Type*} [Fintype J] (C : J → CubeCylinder n)
    (a M : J → ℝ) (u : J → Fin n → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hA : ∀ j x, |affineValue (a j) (u j) x| ≤ M j)
    (bias : ℝ) (f : (Fin n → Bool) → Bool)
    (hmargin : ∀ x, 1 ≤ signedLabel f x *
      (bias + ∑ j, (C j).eval x * affineValue (a j) (u j) x)) :
    HasRelativeMargin n
      (∑ j, (min (C j).positive.card (C j).negative.card + 1)) f
      (1 / (2 * (|bias| + ∑ j,
        massBound (min (C j).positive.card (C j).negative.card) * M j) + 1)) := by
  classical
  let p : J → ℕ := fun j ↦ min (C j).positive.card (C j).negative.card
  let I := (j : J) × Fin (p j + 1)
  let H := ∑ j, (p j + 1)
  have hcard : Fintype.card I = H := by
    simp [I, H]
  let e : Fin H ≃ I :=
    (finCongr hcard.symm).trans (Fintype.equivFin I).symm
  choose g hg hbound hsum using fun j ↦ bounded_decomposition_min
    (C j) (a j) (M j) (u j) (hM j) (hA j)
  let v : Fin H → (Fin n → Bool) → ℝ := fun h ↦ g (e h).1 (e h).2
  let B : Fin H → ℝ := fun h ↦ coefficientBound (p (e h).1) * M (e h).1
  have hv : ∀ h, UniformlyOneAtomApproximable (v h) := fun h ↦ hg _ _
  have hB : ∀ h, 0 ≤ B h := by
    intro h
    dsimp [B]
    apply mul_nonneg _ (hM _)
    unfold coefficientBound
    positivity
  have hvbound : ∀ h x, |v h x| ≤ B h := fun h x ↦ hbound _ _ x
  have hvsum : ∀ x, (∑ h, v h x) =
      ∑ j, (C j).eval x * affineValue (a j) (u j) x := by
    intro x
    dsimp [v]
    rw [e.sum_comp (fun i : I ↦ g i.1 i.2 x)]
    rw [Fintype.sum_sigma]
    exact sum_congr rfl fun j _ ↦ hsum j x
  have hm : ∀ x, 1 ≤ signedLabel f x * (bias + ∑ h, v h x) := by
    intro x
    rw [hvsum]
    exact hmargin x
  have hmass : (∑ h, B h) = ∑ j, massBound (p j) * M j := by
    dsimp [B]
    rw [e.sum_comp (fun i : I ↦ coefficientBound (p i.1) * M i.1)]
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro j _
    simp [massBound]
    ring
  have hout := hasRelativeMargin_of_uniformlyOneAtomApproximable
    v hv B hB hvbound bias f hm
  rw [hmass] at hout
  exact hout

end HeadComplexity.LinearCylinderMargin
