module

public import HeadComplexity.Algebra.Polynomial.Lagrange
public import HeadComplexity.Attention.AffineFraction

/-!
# Scores that depend on a weighted sum

The nodal quotient of a bounded-degree polynomial at a positive weighted sum
is a head score. Interpolating on the finite image of the sum gives exact scores
that factor through it, including every score for the binary weighting.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace HeadComplexity

variable {n H : ℕ}

/-- The sum of the weights of the true input coordinates. -/
def weightedSum (w : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, w i * Bool.cubePoint ℝ x i

/-- The weighted sum of the true bits is nonnegative when all weights are nonnegative. -/
theorem weightedSum_nonneg {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (x : Fin n → Bool) :
    0 ≤ weightedSum w x :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (Nat.cast_nonneg _)

/-- With all weights equal to one, the weighted sum is the Hamming weight. -/
@[simp] theorem weightedSum_one (x : Fin n → Bool) :
    weightedSum (fun _ ↦ 1) x = (Bool.hammingWeight x : ℝ) := by
  simpa [weightedSum] using Bool.sum_cubePoint (R := ℝ) x

private def negativePole (i : Fin H) : ℝ := -((i.val : ℝ) + 1)

/-- Different pole indices give distinct negative poles. -/
private theorem negativePole_injective : Function.Injective (negativePole (H := H)) := by
  intro i j h
  simpa [negativePole, Fin.ext_iff] using h

/-- Every chosen pole is strictly negative. -/
private theorem negativePole_neg (i : Fin H) : negativePole i < 0 :=
  neg_lt_zero.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)

/-- Subtracting a negative pole from the weighted sum gives a positive denominator on the cube. -/
private theorem weightedSum_sub_pos {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) {a : ℝ}
    (ha : a < 0) (x : Fin n → Bool) : 0 < weightedSum w x - a :=
  sub_pos.mpr (ha.trans_le (weightedSum_nonneg (fun i ↦ (hw i).le) x))

/-- A nodal polynomial with negative poles is positive at every nonnegative weighted sum on the
cube. -/
private theorem eval_nodal_weightedSum_pos {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {a : Fin H → ℝ} (ha : ∀ i, a i < 0) (x : Fin n → Bool) :
    0 < (Lagrange.nodal Finset.univ a).eval (weightedSum w x) := by
  rw [Lagrange.eval_nodal]
  exact Finset.prod_pos fun i _ ↦ weightedSum_sub_pos hw (ha i) x

/-- A polynomial divided by the nodal polynomial of `H` distinct negative poles
gives an exact `H`-head score when evaluated at a positive weighted sum. -/
theorem hasHeadScore_eval_div_nodal_weightedSum (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {a : Fin H → ℝ} (ha : Function.Injective a) (ha_neg : ∀ i, a i < 0)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ H) :
    HasHeadScore (fun x ↦ p.eval (weightedSum w x) /
      (Lagrange.nodal Finset.univ a).eval (weightedSum w x)) H := by
  obtain ⟨c, b, hb⟩ := p.exists_eval_div_nodal_eq_const_add_sum_div
    (s := Finset.univ) ha.injOn (by simpa using hp)
  let r (i : Fin H) : Attention.AffineFraction n :=
    { numerator := (AffineMap.constCoeffEquiv ℝ (Fin n)).symm (b i, 0)
      denominator := (AffineMap.constCoeffEquiv ℝ (Fin n)).symm (-a i, w) }
  have hnum (i : Fin H) (x : Fin n → Bool) : (r i).numerator (Bool.cubePoint ℝ x) = b i := by
    simp [r, AffineMap.constCoeffEquiv_symm_apply]
  have hden (i : Fin H) (x : Fin n → Bool) :
      (r i).denominator (Bool.cubePoint ℝ x) = weightedSum w x - a i := by
    simp [r, AffineMap.constCoeffEquiv_symm_apply, weightedSum, dotProduct, sub_eq_neg_add]
  refine hasHeadScore_iff_exists_affineFractions.mpr ⟨c, r, fun i ↦ ?_, fun x ↦ ?_⟩
  · exact ⟨fun x ↦ by rw [hden]; exact weightedSum_sub_pos hw (ha_neg i) x,
      Or.inl (by simpa [r] using hw)⟩
  · simpa only [Attention.AffineFraction.eval, hnum, hden] using
      hb (weightedSum w x) (fun i _ ↦ (sub_pos.mp (weightedSum_sub_pos hw (ha_neg i) x)).ne')

/-- A polynomial of degree at most `H` in a positive weighted sum gives a Boolean
classification with `H` heads. -/
theorem computableWithHeads_of_sign_eval_weightedSum (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {p : Polynomial ℝ} (hp : p.natDegree ≤ H) {f : (Fin n → Bool) → Bool}
    (hf : Function.SignRepresents (fun x ↦ p.eval (weightedSum w x)) f) :
    ComputableWithHeads f H := by
  refine (hasHeadScore_eval_div_nodal_weightedSum w hw negativePole_injective negativePole_neg p hp)
    |>.computableWithHeads fun x ↦ ?_
  exact (div_pos_iff_of_pos_right (eval_nodal_weightedSum_pos hw negativePole_neg x)).trans (hf x)

/-- Every score that factors through a positive weighted sum is realizable with
one fewer head than the number of distinct values of the sum. -/
theorem hasHeadScore_of_factorsThrough_weightedSum (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {s : (Fin n → Bool) → ℝ} (hs : s.FactorsThrough (weightedSum w)) :
    HasHeadScore s ((Finset.univ.image (weightedSum w)).card - 1) := by
  let S := Finset.univ.image (weightedSum w)
  let a : Fin (S.card - 1) → ℝ := negativePole
  let Q := Lagrange.nodal Finset.univ a
  let g := Function.extend (weightedSum w) s 0
  let p := Lagrange.interpolate S id (fun z ↦ g z * Q.eval z)
  suffices (fun x ↦ p.eval (weightedSum w x) / Q.eval (weightedSum w x)) = s by
    rw [← this]
    exact hasHeadScore_eval_div_nodal_weightedSum w hw negativePole_injective negativePole_neg p
      (Polynomial.natDegree_le_of_degree_le (Lagrange.degree_interpolate_le _ (Set.injOn_id _)))
  funext x
  apply (div_eq_iff (eval_nodal_weightedSum_pos (a := a) hw negativePole_neg x).ne').2
  simpa only [id_eq, g, hs.extend_apply] using
    Lagrange.eval_interpolate_at_node (s := S) (v := id) (fun z ↦ g z * Q.eval z) (Set.injOn_id _)
      (Finset.mem_image_of_mem (weightedSum w) (Finset.mem_univ x))

/-- A Boolean function that factors through a positive weighted sum takes at most
one fewer head than the number of distinct values of the sum. -/
theorem computableWithHeads_of_factorsThrough_weightedSum (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {f : (Fin n → Bool) → Bool} (hf : f.FactorsThrough (weightedSum w)) :
    ComputableWithHeads f ((Finset.univ.image (weightedSum w)).card - 1) := by
  let s (x : Fin n → Bool) : ℝ := if f x then 1 else -1
  refine (hasHeadScore_of_factorsThrough_weightedSum (s := s) w hw ?_).computableWithHeads ?_
  · exact fun _ _ h ↦ congrArg (fun b : Bool ↦ if b then (1 : ℝ) else -1) (hf h)
  · intro x
    cases hx : f x <;> simp [s, hx]

/-- Binary weights distinguish every Boolean assignment. -/
theorem weightedSum_two_pow_injective :
    Function.Injective (weightedSum (fun i : Fin n ↦ (2 : ℝ) ^ i.val)) := by
  have hcode (x : Fin n → Bool) : weightedSum (fun i ↦ (2 : ℝ) ^ i.val) x =
      ((finFunctionFinEquiv (fun i ↦ finTwoEquiv.symm (x i)) : ℕ) : ℝ) := by
    rw [finFunctionFinEquiv_apply, Nat.cast_sum, weightedSum]
    exact Finset.sum_congr rfl fun i _ ↦ by cases h : x i <;> simp [h, finTwoEquiv]
  intro x y h
  rw [hcode, hcode] at h
  funext i
  exact finTwoEquiv.symm.injective
    (congrFun (finFunctionFinEquiv.injective (Fin.ext (Nat.cast_injective h))) i)

/-- Every Boolean function on `n` bits is computable with `2^n - 1` heads. -/
theorem computableWithHeads_universal (f : (Fin n → Bool) → Bool) :
    ComputableWithHeads f (2 ^ n - 1) := by
  let w : Fin n → ℝ := fun i ↦ (2 : ℝ) ^ i.val
  simpa [w, Finset.card_image_of_injective _ weightedSum_two_pow_injective] using
    computableWithHeads_of_factorsThrough_weightedSum w (fun _ ↦ pow_pos zero_lt_two _)
      (weightedSum_two_pow_injective.factorsThrough f)

end HeadComplexity
