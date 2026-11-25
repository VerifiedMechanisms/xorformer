import HeadComplexity.Research.AnchoredAtomicDecomposition

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.PositiveReciprocalExpansion
open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def face (s : Finset I) (x : I → Bool) : ℝ :=
  if ∀ i ∈ s, x i = false then 1 else 0

def HasExpansion (f : (I → Bool) → ℝ) : Prop :=
  ∃ c : Finset I → ℝ, (∀ s, 0 ≤ c s) ∧ ∀ x, f x = ∑ s, c s * face s x

theorem face_empty (x : I → Bool) : face ∅ x = 1 := by simp [face]

theorem face_union (s t : Finset I) (x : I → Bool) :
    face (s ∪ t) x = face s x * face t x := by
  simp only [face, mem_union, or_imp, forall_and]
  split_ifs <;> norm_num at * <;> aesop

theorem face_eq_prod (s : Finset I) (x : I → Bool) :
    face s x = ∏ i ∈ s, (if x i then (0 : ℝ) else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [face]
  | @insert i s hi ih =>
    have hh := face_union ({i} : Finset I) s x
    rw [singleton_union] at hh
    rw [hh, ih, prod_insert hi]
    congr 1
    cases hxi : x i <;> simp [face, hxi]

theorem face_eq_squarefreeMonomial_flip {n : ℕ} (s : Finset (Fin n))
    (x : Fin n → Bool) : face s x = squarefreeMonomial s (flipBits x) := by
  rw [face_eq_prod]
  unfold squarefreeMonomial
  apply prod_congr rfl
  intro i hi
  cases hxi : x i <;> simp [flipBits, boolToReal, hxi]

theorem uniformlyOneAtomApproximable_face_affine {n : ℕ}
    (s : Finset (Fin n)) (a : ℝ) (u : Fin n → ℝ) :
    UniformlyOneAtomApproximable (fun x => face s x * affineValue a u x) := by
  simpa only [face_eq_squarefreeMonomial_flip] using
    AnchoredAtomicDecomposition.uniformlyOneAtomApproximable_negativeFace_affine s a u

theorem constant (a : ℝ) (ha : 0 ≤ a) : HasExpansion (fun _ : I → Bool => a) := by
  classical
  refine ⟨fun s => if s = ∅ then a else 0, fun s => by dsimp; split_ifs <;> positivity, ?_⟩
  intro x
  simp [face_empty]

theorem generator (s : Finset I) : HasExpansion (face s) := by
  classical
  refine ⟨fun t => if t = s then 1 else 0, fun t => by dsimp; split_ifs <;> positivity, ?_⟩
  intro x
  simp

theorem add {f g : (I → Bool) → ℝ} (hf : HasExpansion f) (hg : HasExpansion g) :
    HasExpansion (fun x => f x + g x) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun s => a s + b s, fun s => add_nonneg (ha s) (hb s), ?_⟩
  intro x
  simp_rw [add_mul, sum_add_distrib, ← hfa, ← hgb]

theorem mul {f g : (I → Bool) → ℝ} (hf : HasExpansion f) (hg : HasExpansion g) :
    HasExpansion (fun x => f x * g x) := by
  classical
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  let c : Finset I → ℝ := fun s => ∑ u : Finset I, ∑ v : Finset I,
    if u ∪ v = s then a u * b v else 0
  refine ⟨c, ?_, ?_⟩
  · intro s
    exact sum_nonneg fun u _ => sum_nonneg fun v _ => by
      split_ifs
      · exact mul_nonneg (ha u) (hb v)
      · exact le_refl 0
  · intro x
    dsimp only
    rw [hfa, hgb, Fintype.sum_mul_sum]
    dsimp [c]
    simp_rw [sum_mul]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro u _
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro v _
    simp only [ite_mul, zero_mul]
    simp only [sum_ite_eq, mem_univ, ite_true, face_union]
    ring

theorem prod {J : Type*} (s : Finset J) (f : J → (I → Bool) → ℝ)
    (hf : ∀ j, HasExpansion (f j)) : HasExpansion (fun x => ∏ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (constant (I := I) 1 (by norm_num))
  | @insert j s hj ih =>
    simpa only [prod_insert hj] using mul (hf j) ih

/-- An exact nonnegative anchored-face expansion of a reciprocal with
nonnegative slopes. Strictly positive original slopes are included. -/
theorem reciprocal (s : Finset I) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (c : ℝ) (hc : 0 < c) :
    HasExpansion (fun x : I → Bool => 1 / (c + ∑ i ∈ s, w i * (if x i then 1 else 0))) := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simpa using (constant (I := I) (1 / c) (by positivity))
  | @insert i s hi ih =>
    have hcw : 0 < c + w i := add_pos_of_pos_of_nonneg hc (hw i)
    have hf := ih c hc
    have hg := ih (c + w i) hcw
    have hp := mul (mul (mul (constant (I := I) (w i) (hw i)) (generator {i})) hf) hg
    have hh := add hg hp
    convert hh using 1
    funext x
    have hsum : 0 ≤ ∑ j ∈ s, w j * (if x j then 1 else 0) := by
      apply sum_nonneg
      intro j hj
      exact mul_nonneg (hw j) (by split_ifs <;> positivity)
    have h0 : c + ∑ j ∈ s, w j * (if x j then 1 else 0) ≠ 0 := by positivity
    have h1 : c + w i + ∑ j ∈ s, w j * (if x j then 1 else 0) ≠ 0 := by positivity
    rw [sum_insert hi]
    have hface : face {i} x = if x i then 0 else 1 := by
      cases hxi : x i <;> simp [face, hxi]
    rw [hface]
    cases hxi : x i <;>
      simp only [hxi, Bool.false_eq_true, not_false_eq_true, ite_false, ite_true,
        mul_zero, mul_one, zero_mul, zero_add, add_zero]
    · field_simp [h0, h1]
      ring
    · rw [← add_assoc]

theorem face_zero (s : Finset I) : face s (fun _ => false) = 1 := by
  simp [face]

theorem face_singleton_input (s : Finset I) (i : I) :
    face s (fun j => if j = i then true else false) = if i ∉ s then 1 else 0 := by
  classical
  by_cases hi : i ∈ s
  · have hh : ¬∀ j ∈ s, (if j = i then true else false) = false := by
      intro h
      simpa using h i hi
    simp [face, hh, hi]
  · have hh : ∀ j ∈ s, (if j = i then true else false) = false := by
      intro j hj
      have hji : j ≠ i := by intro h; subst j; contradiction
      simp [hji]
    simp [face, hh, hi]

/-- The positive coefficients satisfy the two endpoint identities used in
the full-cube mass estimate, without any condition-number assumption. -/
theorem reciprocal_with_endpoint_identities (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (c : ℝ) (hc : 0 < c) :
    ∃ κ : Finset I → ℝ, (∀ s, 0 ≤ κ s) ∧
      (∀ x : I → Bool, 1 / (c + ∑ i, w i * (if x i then 1 else 0)) =
        ∑ s, κ s * face s x) ∧
      (∑ s, κ s = 1 / c) ∧
      (∀ i, ∑ s, (if i ∉ s then κ s else 0) = 1 / (c + w i)) := by
  classical
  obtain ⟨κ, hκ, he⟩ := reciprocal (univ : Finset I) w hw c hc
  refine ⟨κ, hκ, he, ?_, ?_⟩
  · simpa only [Bool.false_eq_true, ite_false, mul_zero, sum_const_zero,
      add_zero, face_zero, mul_one] using (he (fun _ => false)).symm
  · intro i
    have h := (he (fun j => if j = i then true else false)).symm
    simp only [face_singleton_input] at h
    simpa [mul_ite, ite_not] using h

/-- The complete positive reciprocal expansion and its weighted mass bound
are available together for the original finite Boolean cube. -/
theorem reciprocal_with_mass_bound {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (c : ℝ) (hc : 0 < c) :
    ∃ κ : Finset (Fin n) → ℝ, (∀ s, 0 ≤ κ s) ∧
      (∀ x : Fin n → Bool, 1 / (c + ∑ i, w i * (if x i then 1 else 0)) =
        ∑ s, κ s * face s x) ∧
      (∑ s, κ s * (c + ∑ i, if i ∉ s then w i else 0)) ≤ (n : ℝ) + 1 := by
  obtain ⟨κ, hκ, he, hzero, hsingle⟩ := reciprocal_with_endpoint_identities w hw c hc
  exact ⟨κ, hκ, he,
    AnchoredAtomicDecomposition.face_coefficient_mass_le c w κ hc hw hzero hsingle⟩

/-- An arbitrary finite product of normalized constant-numerator coherent
reciprocals is exactly a probability mixture of anchored faces. -/
theorem normalized_product_probability_expansion {J : Type*} [Fintype J]
    (w : J → I → ℝ) (hw : ∀ j i, 0 ≤ w j i)
    (c : J → ℝ) (hc : ∀ j, 0 < c j) :
    ∃ κ : Finset I → ℝ, (∀ s, 0 ≤ κ s) ∧ (∑ s, κ s = 1) ∧
      ∀ x : I → Bool,
        (∏ j, c j / (c j + ∑ i, w j i * (if x i then 1 else 0))) =
          ∑ s, κ s * face s x := by
  classical
  have hf (j : J) : HasExpansion (fun x : I → Bool =>
      c j / (c j + ∑ i, w j i * (if x i then 1 else 0))) := by
    simpa only [mul_one_div] using mul (constant (I := I) (c j) (hc j).le)
      (reciprocal univ (w j) (hw j) (c j) (hc j))
  obtain ⟨κ, hκ, he⟩ := prod univ _ hf
  refine ⟨κ, hκ, ?_, he⟩
  have hz := he (fun _ => false)
  dsimp only at hz
  have hleft : (∏ j, c j / (c j + ∑ i, w j i *
      (if (false : Bool) then 1 else 0))) = 1 := by
    apply prod_eq_one
    intro j hj
    simp [(hc j).ne']
  rw [hleft] at hz
  simpa only [face_zero, mul_one] using hz.symm

/-- Exact anchored-face decomposition with the full-cube norm budget.
For affine `A`, each displayed block has the genuine one-head approximation
already proved in `AnchoredAtomicDecomposition`. -/
theorem ratio_with_full_cube_mass {n : ℕ} (A : (Fin n → Bool) → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ℝ) (hc : 0 < c) :
    ∃ κ : Finset (Fin n) → ℝ, (∀ s, 0 ≤ κ s) ∧
      (∀ x, A x / (c + ∑ i, w i * (if x i then 1 else 0)) =
        ∑ s, κ s * face s x * A x) ∧
      (∑ s, ‖fun x => κ s * face s x * A x‖) ≤
        ((n : ℝ) + 1) * ‖fun x => A x / (c + ∑ i, w i * (if x i then 1 else 0))‖ := by
  classical
  obtain ⟨κ, hκ, he, hmass⟩ := reciprocal_with_mass_bound w hw c hc
  let B : (Fin n → Bool) → ℝ := fun x => c + ∑ i, w i * (if x i then 1 else 0)
  let D : Finset (Fin n) → ℝ := fun s => c + ∑ i, if i ∉ s then w i else 0
  let M : ℝ := ‖fun x => A x / B x‖
  have hM : 0 ≤ M := norm_nonneg _
  have hB (x : Fin n → Bool) : 0 < B x := by
    apply add_pos_of_pos_of_nonneg hc
    exact sum_nonneg fun i _ => mul_nonneg (hw i) (by split_ifs <;> positivity)
  have hD (s : Finset (Fin n)) : 0 < D s := by
    apply add_pos_of_pos_of_nonneg hc
    exact sum_nonneg fun i _ => by
      split_ifs <;> first | exact hw i | exact le_rfl
  have hA (x : Fin n → Bool) : |A x| ≤ M * B x := by
    have hh := norm_le_pi_norm (fun x => A x / B x) x
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hB x)] at hh
    exact (div_le_iff₀ (hB x)).mp hh
  have hblock (s : Finset (Fin n)) :
      ‖fun x => κ s * face s x * A x‖ ≤ κ s * D s * M := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (hκ s) (hD s).le) hM)).mpr
    intro x
    by_cases hz : ∀ i ∈ s, x i = false
    · have hBD : B x ≤ D s := by
        dsimp [B, D]
        apply add_le_add le_rfl
        apply sum_le_sum
        intro i hi
        by_cases his : i ∈ s
        · simp [his, hz i his]
        · simp only [his, not_false_eq_true, ite_true]
          cases hxi : x i <;> simp [hw i]
      have hh : |A x| ≤ D s * M := by nlinarith [hA x, mul_nonneg hM (sub_nonneg.mpr hBD)]
      simpa only [Real.norm_eq_abs, face, if_pos hz, mul_one, abs_mul,
        abs_of_nonneg (hκ s), mul_assoc] using mul_le_mul_of_nonneg_left hh (hκ s)
    · simp only [face, if_neg hz, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (hκ s) (hD s).le) hM
  refine ⟨κ, hκ, ?_, ?_⟩
  · intro x
    calc
      _ = A x * (1 / (c + ∑ i, w i * (if x i then 1 else 0))) := by ring
      _ = _ := by rw [he, mul_sum]; apply sum_congr rfl; intro s hs; ring
  · calc
      _ ≤ ∑ s, κ s * D s * M := sum_le_sum fun s _ => hblock s
      _ = (∑ s, κ s * D s) * M := (sum_mul ..).symm
      _ ≤ ((n : ℝ) + 1) * M := mul_le_mul_of_nonneg_right hmass hM

end HeadComplexity.PositiveReciprocalExpansion
