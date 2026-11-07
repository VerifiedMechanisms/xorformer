module

public import HeadComplexity.Algebra.MvPolynomial.Affine
public import HeadComplexity.Attention.AffineFraction
public import HeadComplexity.BooleanFunction.ThresholdDegree.Basic

/-!
# Clearing denominators of attention scores

An attention score with `H` heads becomes a polynomial of degree at most `H` after
multiplication by a positive factor on the Boolean cube. For two heads the cleared
polynomial is a sum of two products of affine polynomials.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

/-- Clearing the nonzero denominators of a sum of fractions gives a sum in which each
numerator is multiplied by the product of all the other denominators. -/
theorem sum_mul_prod_erase_eq_sum_div_mul_prod {ι K : Type*} [DecidableEq ι] [Field K]
    (s : Finset ι) (N D : ι → K) (hD : ∀ i ∈ s, D i ≠ 0) :
    ∑ i ∈ s, N i * ∏ j ∈ s.erase i, D j = (∑ i ∈ s, N i / D i) * ∏ j ∈ s, D j := by
  rw [sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [← mul_prod_erase s D hi, ← mul_assoc, div_mul_cancel₀ _ (hD i hi)]

end Finset

namespace HeadComplexity

open MvPolynomial

/-- A product of polynomials of degree at most one has degree at most the number of factors. -/
private theorem totalDegree_prod_le_card {ι σ R : Type*} [CommSemiring R]
    (s : Finset ι) (D : ι → MvPolynomial σ R) (hD : ∀ i ∈ s, (D i).totalDegree ≤ 1) :
    (∏ i ∈ s, D i).totalDegree ≤ s.card := by
  calc
    _ ≤ ∑ i ∈ s, (D i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum hD
    _ = s.card := by simp

private noncomputable def clearedPolynomial {ι σ K : Type*} [DecidableEq ι] [CommSemiring K]
    (s : Finset ι) (N D : ι → MvPolynomial σ K) (c : K) : MvPolynomial σ K :=
  C c * (∏ i ∈ s, D i) + ∑ i ∈ s, N i * ∏ j ∈ s.erase i, D j

/-- At a point where every denominator is nonzero, the cleared polynomial is the original
rational expression multiplied by the denominator product. -/
private theorem eval_clearedPolynomial {ι σ K : Type*} [DecidableEq ι] [Field K]
    (s : Finset ι) (N D : ι → MvPolynomial σ K) (c : K) (x : σ → K)
    (hD : ∀ i ∈ s, eval x (D i) ≠ 0) :
    eval x (clearedPolynomial s N D c) =
      (c + ∑ i ∈ s, eval x (N i) / eval x (D i)) * ∏ i ∈ s, eval x (D i) := by
  simp only [clearedPolynomial, map_add, map_mul, map_prod, map_sum, eval_C, add_mul]
  rw [Finset.sum_mul_prod_erase_eq_sum_div_mul_prod _ _ _ hD]

/-- With affine numerator and denominator polynomials, the cleared polynomial has degree at most
the number of fractions. -/
private theorem totalDegree_clearedPolynomial_le_card {ι σ R : Type*}
    [DecidableEq ι] [CommSemiring R] (s : Finset ι) (N D : ι → MvPolynomial σ R) (c : R)
    (hN : ∀ i ∈ s, (N i).totalDegree ≤ 1) (hD : ∀ i ∈ s, (D i).totalDegree ≤ 1) :
    (clearedPolynomial s N D c).totalDegree ≤ s.card := by
  unfold clearedPolynomial
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by simpa using totalDegree_prod_le_card s D hD)
  · refine totalDegree_finsetSum_le fun i hi ↦ (totalDegree_mul _ _).trans ?_
    calc
      _ ≤ 1 + (s.erase i).card :=
        Nat.add_le_add (hN i hi) (totalDegree_prod_le_card _ D fun j hj ↦
          hD j (Finset.mem_of_mem_erase hj))
      _ = s.card := by simpa [Nat.add_comm] using Finset.card_erase_add_one hi

variable {n H : ℕ} {s : (Fin n → Bool) → ℝ} {f : (Fin n → Bool) → Bool}

/-- A realized head score is a constant plus one quotient of affine polynomials per head, with
denominators positive on the Boolean cube. -/
private theorem HasHeadScore.exists_affinePolynomialFractions (hs : HasHeadScore s H) :
    ∃ (c : ℝ) (N D : Fin H → MvPolynomial (Fin n) ℝ),
      (∀ i, (N i).totalDegree ≤ 1) ∧ (∀ i, (D i).totalDegree ≤ 1) ∧
      (∀ i x, 0 < eval (Bool.cubePoint ℝ x) (D i)) ∧
      ∀ x, s x = c + ∑ i, eval (Bool.cubePoint ℝ x) (N i) / eval (Bool.cubePoint ℝ x) (D i) := by
  obtain ⟨c, r, hr, heval⟩ := hasHeadScore_iff_exists_affineFractions.mp hs
  refine ⟨c, fun i ↦ (r i).numerator.toMvPolynomial, fun i ↦ (r i).denominator.toMvPolynomial,
    fun i ↦ (r i).numerator.totalDegree_toMvPolynomial_le_one,
    fun i ↦ (r i).denominator.totalDegree_toMvPolynomial_le_one, ?_, ?_⟩
  · intro i x
    simpa only [AffineMap.eval_toMvPolynomial] using (hr i).denominator_pos x
  · intro x
    simpa only [AffineMap.eval_toMvPolynomial, Attention.AffineFraction.eval] using heval x

/-- Multiplying an `H`-head score by a positive factor on the cube gives the evaluation of a
polynomial of degree at most `H`. -/
theorem HasHeadScore.exists_mul_pos_eq_eval (hs : HasHeadScore s H) :
    ∃ (p : MvPolynomial (Fin n) ℝ) (d : (Fin n → Bool) → ℝ),
      p.totalDegree ≤ H ∧ (∀ x, 0 < d x) ∧
      ∀ x, eval (Bool.cubePoint ℝ x) p = s x * d x := by
  obtain ⟨c, N, D, hN, hD, hpos, heval⟩ := hs.exists_affinePolynomialFractions
  refine ⟨clearedPolynomial Finset.univ N D c, fun x ↦ ∏ i, eval (Bool.cubePoint ℝ x) (D i),
    ?_, fun x ↦ Finset.prod_pos fun i _ ↦ hpos i x, ?_⟩
  · simpa using totalDegree_clearedPolynomial_le_card Finset.univ N D c
      (fun i _ ↦ hN i) (fun i _ ↦ hD i)
  · intro x
    rw [eval_clearedPolynomial _ _ _ _ _ (fun i _ ↦ (hpos i x).ne'), heval x]

/-- A Boolean function computed with a given number of heads has threshold degree at most that
number. -/
theorem ComputableWithHeads.thresholdDegreeLE (hf : ComputableWithHeads f H) :
    ThresholdDegreeLE f H := by
  obtain ⟨s, hs, hsign⟩ := hf
  obtain ⟨p, d, hp, hd, heval⟩ := hs.exists_mul_pos_eq_eval
  exact ⟨p, hp, fun x ↦ by simpa only [heval x] using hsign.mul_pos_right hd x⟩

/-- With two fractions, the cleared expression is a sum of two products after absorbing the
constant into the first numerator. -/
private theorem clearedPolynomial_two {σ : Type*} (N D : Fin 2 → MvPolynomial σ ℝ) (c : ℝ) :
    clearedPolynomial Finset.univ N D c = (C c * D 0 + N 0) * D 1 + N 1 * D 0 := by
  rw [clearedPolynomial, Fin.prod_univ_two, Fin.sum_univ_two, Finset.univ_fin2]
  simp [Finset.erase_insert_of_ne Fin.zero_ne_one, add_mul, mul_assoc, add_assoc]

/-- A two-head classifier is sign represented by a sum of two products of affine polynomials. -/
theorem ComputableWithHeads.exists_signRepresents_twoAffineProducts
    (hf : ComputableWithHeads f 2) :
    ∃ L₁ R₁ L₂ R₂ : MvPolynomial (Fin n) ℝ,
      L₁.totalDegree ≤ 1 ∧ R₁.totalDegree ≤ 1 ∧ L₂.totalDegree ≤ 1 ∧ R₂.totalDegree ≤ 1 ∧
      Function.SignRepresents (fun x ↦ eval (Bool.cubePoint ℝ x) (L₁ * R₁ + L₂ * R₂)) f := by
  obtain ⟨s, hs, hsign⟩ := hf
  obtain ⟨c, N, D, hN, hD, hpos, heval⟩ := hs.exists_affinePolynomialFractions
  refine ⟨C c * D 0 + N 0, D 1, N 1, D 0, ?_, hD 1, hN 1, hD 0, ?_⟩
  · exact (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by simpa using hD 0))
      (hN 0))
  · intro x
    change 0 < eval (Bool.cubePoint ℝ x) _ ↔ _
    rw [← clearedPolynomial_two, eval_clearedPolynomial _ _ _ _ _ (fun i _ ↦ (hpos i x).ne'),
      ← heval x]
    exact hsign.mul_pos_right (fun y ↦ Finset.prod_pos fun i _ ↦ hpos i y) x

end HeadComplexity
