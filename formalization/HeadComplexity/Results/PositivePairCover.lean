import HeadComplexity.Atoms.FiniteFlipIsolation
import HeadComplexity.Atoms.PoleIsolation
import HeadComplexity.Atoms.PositiveRationalTransfer
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option linter.style.header false

/-! An auxiliary full-rank reciprocal-cube matrix from a cover by selected
two-flip targets. This is not a theorem about worst-case attention-head count. -/
namespace HeadComplexity.PositivePairCover

open Polynomial Finset
open scoped BigOperators symmDiff

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

noncomputable def epsilon (I : Type*) [Fintype I] : ℝ :=
  1 / (4 * Fintype.card (Finset I))

omit [DecidableEq I] in
theorem epsilon_bounds : 0 < epsilon I ∧ epsilon I ≤ 1 / 2 := by
  have hN : (1 : ℝ) ≤ Fintype.card (Finset I) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Finset I))
  have hden : (0 : ℝ) < 4 * Fintype.card (Finset I) := by linarith
  constructor
  · exact div_pos (by norm_num) hden
  · exact (div_le_iff₀ hden).mpr (by linarith)

noncomputable def denominator (center : V → Finset I) (v : V) (x : Finset I) : ℝ[X] :=
  C (1 + (x.card : ℝ)) + X * C (epsilon I + 2 - ((x ∆ center v).card : ℝ) -
    (1 + (x.card : ℝ)))

omit [Fintype V] [DecidableEq V] in
theorem denominator_at_one (center : V → Finset I) (v : V) (x : Finset I) :
    (denominator center v x).eval 1 =
      epsilon I + (FiniteFlipIsolation.offset (center v) x : ℝ) := by
  simp [denominator, FiniteFlipIsolation.offset]
  ring

omit [Fintype V] [DecidableEq V] in
theorem denominator_at_one_ne_zero (center : V → Finset I) (v : V) (x : Finset I) :
    (denominator center v x).eval 1 ≠ 0 := by
  rw [denominator_at_one]
  have he := epsilon_bounds (I := I)
  by_cases ha : FiniteFlipIsolation.offset (center v) x = 0
  · simpa [ha] using he.1.ne'
  · have hsep := PoleIsolation.shifted_int_abs _ ha (epsilon I) he.1.le he.2
    intro hz
    rw [hz, abs_zero] at hsep
    norm_num at hsep

omit [Fintype V] [DecidableEq V] in
theorem denominator_positive (center : V → Finset I) (t : ℝ) (ht : 0 < t)
    (hsmall : t * ((Fintype.card I : ℝ) + 3) < 1) (v : V) (x : Finset I) :
    0 < (denominator center v x).eval t := by
  have hn : (0 : ℝ) ≤ Fintype.card I := by positivity
  have ht1 : t < 1 := by nlinarith [mul_nonneg ht.le hn]
  have hd : ((x ∆ center v).card : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Finset.card_le_univ (x ∆ center v)
  have hbase : 0 ≤ (1 - t) * (x.card : ℝ) := by positivity
  have hcore := PolynomialPositiveGrid.homotopy_constant_positive
    (Fintype.card I) (Fintype.card I) le_rfl (epsilon I) t
      (epsilon_bounds (I := I)).1 ht hsmall
  have hdist := mul_le_mul_of_nonneg_left hd ht.le
  simp only [denominator, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  nlinarith

noncomputable def numerator (center : V → Finset I) (owner : Finset I → V)
    (pair : Finset I → Finset I) (x y : Finset I) : ℝ :=
  FiniteFlipIsolation.numerator (center (owner y)) (pair y) x

omit [Fintype V] [DecidableEq V] in
theorem pole_matrix_nonsingular (center : V → Finset I) (owner : Finset I → V)
    (pair : Finset I → Finset I) (hpair : ∀ y, (pair y).card = 2)
    (htarget : ∀ y, y ∆ center (owner y) = pair y) :
    (PositiveRationalTransfer.rationalMatrix owner (numerator center owner pair)
      (denominator center) 1).det ≠ 0 := by
  let a : Finset I → Finset I → ℤ :=
    fun x y ↦ FiniteFlipIsolation.offset (center (owner y)) x
  have ha : ∀ x, a x x = 0 := fun x ↦
    (FiniteFlipIsolation.target_values _ _ _ (hpair x) (htarget x)).1
  have hdiag : ∀ x, numerator center owner pair x x = 1 := fun x ↦
    (FiniteFlipIsolation.target_values _ _ _ (hpair x) (htarget x)).2
  have hE : ∀ x y, |numerator center owner pair x y| ≤ 1 := fun x y ↦
    FiniteFlipIsolation.numerator_abs_le _ _ _
  have hisolate : ∀ x y, x ≠ y → a x y = 0 → numerator center owner pair x y = 0 := by
    intro x y hxy hzero
    exact FiniteFlipIsolation.off_target_vanishes _ _ _ _ (hpair y) (htarget y)
      hxy hzero
  have hdet := PoleIsolation.explicit_kernel_det_ne_zero a
    (numerator center owner pair) ha hdiag hE hisolate
  change (PoleIsolation.kernel a (numerator center owner pair) (epsilon I)).det ≠ 0
    at hdet
  have hmatrix : PoleIsolation.kernel a (numerator center owner pair) (epsilon I) =
      (epsilon I) ^ 3 • PositiveRationalTransfer.rationalMatrix owner
        (numerator center owner pair) (denominator center) 1 := by
    ext x y
    simp only [PoleIsolation.kernel, Matrix.smul_apply, smul_eq_mul,
      PositiveRationalTransfer.rationalMatrix, denominator_at_one]
    dsimp [a]
    ring
  rw [hmatrix, Matrix.det_smul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2

/-- A complete finite-matrix conclusion from the combinatorial pair cover.
No head realization or asymptotic head lower bound is included. -/
theorem exists_positive_pair_matrix (center : V → Finset I) (owner : Finset I → V)
    (pair : Finset I → Finset I) (hpair : ∀ y, (pair y).card = 2)
    (htarget : ∀ y, y ∆ center (owner y) = pair y) :
    ∃ t : ℝ, 0 < t ∧ t * ((Fintype.card I : ℝ) + 3) < 1 ∧
      (∀ v x, 0 < (denominator center v x).eval t) ∧
      (PositiveRationalTransfer.rationalMatrix owner (numerator center owner pair)
        (denominator center) t).det ≠ 0 := by
  obtain ⟨j, ht, hsmall, hpositive, hdet⟩ :=
    PositiveRationalTransfer.exists_positive_nonsingular owner (numerator center owner pair)
      (denominator center) 1 (denominator_at_one_ne_zero center)
      (pole_matrix_nonsingular center owner pair hpair htarget)
      ((Fintype.card I : ℝ) + 3) (by positivity) (denominator_positive center)
  exact ⟨_, ht, hsmall, hpositive, hdet⟩

theorem card_symmDiff_affine (v x : Finset I) :
    ((x ∆ v).card : ℝ) = (v.card : ℝ) +
      ∑ i : I, (if i ∈ v then (-1 : ℝ) else 1) * (if i ∈ x then (1 : ℝ) else 0) := by
  have hsym : ((x ∆ v).card : ℝ) = ∑ i : I, if i ∈ x ∆ v then (1 : ℝ) else 0 := by simp
  have hv : (v.card : ℝ) = ∑ i : I, if i ∈ v then (1 : ℝ) else 0 := by simp
  rw [hsym, hv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ x <;> by_cases hv : i ∈ v <;> simp [Finset.mem_symmDiff, hi, hv]

omit [Fintype V] [DecidableEq V] in
theorem denominator_affine (center : V → Finset I) (t : ℝ) (v : V) (x : Finset I) :
    (denominator center v x).eval t =
      1 + t * (epsilon I + 1 - ((center v).card : ℝ)) +
        ∑ i : I, (if i ∈ center v then (1 : ℝ) else 1 - 2 * t) *
          (if i ∈ x then (1 : ℝ) else 0) := by
  have hx : (x.card : ℝ) = ∑ i : I, if i ∈ x then (1 : ℝ) else 0 := by simp
  simp only [denominator, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, card_symmDiff_affine]
  calc
    _ = 1 + t * (epsilon I + 1 - ((center v).card : ℝ)) +
        ((1 - t) * (x.card : ℝ) - t * ∑ i : I,
          (if i ∈ center v then (-1 : ℝ) else 1) * (if i ∈ x then (1 : ℝ) else 0)) := by ring
    _ = 1 + t * (epsilon I + 1 - ((center v).card : ℝ)) +
        ∑ i : I, ((1 - t) * (if i ∈ x then (1 : ℝ) else 0) -
          t * ((if i ∈ center v then (-1 : ℝ) else 1) *
            (if i ∈ x then (1 : ℝ) else 0))) := by
      rw [hx, Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hv : i ∈ center v <;> by_cases hi : i ∈ x <;> simp [hv, hi]
      ring

/-- The forms in the nonsingular matrix have positive constant and slope
coefficients, not merely positive values on the selected vertices. -/
theorem exists_positive_affine_pair_matrix (center : V → Finset I)
    (owner : Finset I → V) (pair : Finset I → Finset I)
    (hpair : ∀ y, (pair y).card = 2)
    (htarget : ∀ y, y ∆ center (owner y) = pair y) :
    ∃ b₀ : V → ℝ, ∃ b : V → I → ℝ,
      (∀ v, 0 < b₀ v) ∧ (∀ v i, 0 < b v i) ∧
      (Matrix.of (fun x y : Finset I ↦ numerator center owner pair x y /
        (b₀ (owner y) + ∑ i : I, b (owner y) i *
          (if i ∈ x then (1 : ℝ) else 0)) ^ 3)).det ≠ 0 := by
  obtain ⟨t, ht, hsmall, _, hdet⟩ :=
    exists_positive_pair_matrix center owner pair hpair htarget
  let b₀ : V → ℝ := fun v ↦ 1 + t * (epsilon I + 1 - ((center v).card : ℝ))
  let b : V → I → ℝ := fun v i ↦ if i ∈ center v then 1 else 1 - 2 * t
  refine ⟨b₀, b, ?_, ?_, ?_⟩
  · intro v
    exact PolynomialPositiveGrid.homotopy_constant_positive (Fintype.card I)
      (center v).card (Finset.card_le_univ _) (epsilon I) t
      (epsilon_bounds (I := I)).1 ht hsmall
  · intro v i
    dsimp [b]
    split_ifs
    · norm_num
    · exact PolynomialPositiveGrid.homotopy_slope_positive (Fintype.card I) t ht hsmall
  · convert hdet using 1
    congr 1
    ext x y
    simp only [Matrix.of_apply, PositiveRationalTransfer.rationalMatrix,
      denominator_affine, b₀, b]

end HeadComplexity.PositivePairCover
