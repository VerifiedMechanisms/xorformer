import HeadComplexity.Atoms.RoPEReorientation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# A six-direction obstruction for three pure rotary heads

The maximum-principle argument is adapted from `PositiveDirectionRankThree`
in VerifiedMechanisms/xorformer-runs, commit
1899d884da3affbf21a8528bcb74b409c9783876. The pure-head cross-factor
obstruction below is new. All statements quantify over arbitrary real data.
-/

namespace HeadComplexity.PureRoPEThreeHeadCross

noncomputable section

open Finset Matrix
open scoped BigOperators

section MaximumPrinciple

variable {n : ℕ} [NeZero n]

theorem maximum_principle (M : Matrix (Fin n) (Fin n) ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j)
    (v : Fin n → ℝ) (hv : ∀ i, (M.mulVec v) i ≤ 0) : ∀ i, v i ≤ 0 := by
  classical
  obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Fin n)).exists_max_image v
    Finset.univ_nonempty
  have hmax : v i ≤ 0 := by
    by_contra hn
    have hp : 0 < v i := lt_of_not_ge hn
    have hr : 0 ≤ ∑ j, M i j * (v j - v i) := by
      apply Finset.sum_nonneg
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · exact mul_nonneg_of_nonpos_of_nonpos (hoff i j (Ne.symm hji))
          (sub_nonpos.mpr (hi j (Finset.mem_univ j)))
    have he : (M.mulVec v) i = (∑ j, M i j) * v i +
        ∑ j, M i j * (v j - v i) := by
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul]
      ring
    have hh := mul_pos (hrow i) hp
    linarith [hv i]
  intro j
  exact (hi j (Finset.mem_univ j)).trans hmax

theorem mulVec_injective (M : Matrix (Fin n) (Fin n) ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) :
    Function.Injective M.mulVec := by
  intro u v he
  have hsub : M.mulVec (u - v) = 0 := by rw [Matrix.mulVec_sub, he]; simp
  have hsub' : M.mulVec (v - u) = 0 := by rw [Matrix.mulVec_sub, he]; simp
  have h1 := maximum_principle M hoff hrow (u - v) (fun i ↦ by simp [hsub])
  have h2 := maximum_principle M hoff hrow (v - u) (fun i ↦ by simp [hsub'])
  funext i
  have := h1 i
  have := h2 i
  simp only [Pi.sub_apply] at *
  linarith

theorem positive_solution (M : Matrix (Fin n) (Fin n) ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j)
    (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ u : Fin n → ℝ, (∀ i, 0 < u i) ∧ M.mulVec u = v := by
  have hinj : Function.Injective M.mulVecLin := mulVec_injective M hoff hrow
  have hsur : Function.Surjective M.mulVecLin := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨u, hu⟩ := hsur v
  change M.mulVec u = v at hu
  have hnon : ∀ i, 0 ≤ u i := by
    have h := maximum_principle M hoff hrow (-u) (fun i ↦ by
      rw [Matrix.mulVec_neg, hu]
      exact neg_nonpos.mpr (hv i).le)
    intro i
    simpa using h i
  refine ⟨u, fun i ↦ ?_, hu⟩
  by_contra hn
  have hz : u i = 0 := le_antisymm (le_of_not_gt hn) (hnon i)
  have hm : (M.mulVec u) i ≤ 0 := by
    change (∑ j, M i j * u j) ≤ 0
    apply Finset.sum_nonpos
    intro j _
    by_cases hji : j = i
    · simp [hji, hz]
    · exact mul_nonpos_of_nonpos_of_nonneg (hoff i j (Ne.symm hji)) (hnon j)
  rw [hu] at hm
  exact (not_lt_of_ge hm) (hv i)

end MaximumPrinciple

/-- The linear coefficient map of the six pure-head directions. -/
def transform (k l : Fin 3 → ℝ) (a b : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![k 0 * (b 1 + b 2), k 1 * (b 0 + b 2), k 2 * (b 0 + b 1),
    k 1 * a 1 + k 2 * a 2 + (l 0 + l 1) * b 1 + (l 0 + l 2) * b 2,
    k 0 * a 0 + k 2 * a 2 + (l 0 + l 1) * b 0 + (l 1 + l 2) * b 2,
    k 0 * a 0 + k 1 * a 1 + (l 0 + l 2) * b 0 + (l 1 + l 2) * b 1]

theorem transform_injective (k l : Fin 3 → ℝ) (hk : ∀ i, k i ≠ 0)
    (a b a' b' : Fin 3 → ℝ) (h : transform k l a b = transform k l a' b') :
    a = a' ∧ b = b' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  dsimp [transform] at h0 h1 h2
  have hb0 := (mul_left_cancel₀ (hk 0) h0)
  have hb1 := (mul_left_cancel₀ (hk 1) h1)
  have hb2 := (mul_left_cancel₀ (hk 2) h2)
  have hb : b = b' := by
    funext i
    fin_cases i <;> dsimp at * <;> linarith
  subst b'
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  dsimp [transform] at h3 h4 h5
  have ha0 : k 0 * a 0 = k 0 * a' 0 := by linarith
  have ha1 : k 1 * a 1 = k 1 * a' 1 := by linarith
  have ha2 : k 2 * a 2 = k 2 * a' 2 := by linarith
  refine ⟨?_, rfl⟩
  funext i
  fin_cases i
  · exact mul_left_cancel₀ (hk 0) ha0
  · exact mul_left_cancel₀ (hk 1) ha1
  · exact mul_left_cancel₀ (hk 2) ha2

def unit (j : Fin 3) : Fin 6 → ℝ := fun i ↦ if i = j.castAdd 3 then 1 else 0

def inverseA (k l : Fin 3 → ℝ) (j : Fin 3) (i : Fin 3) : ℝ :=
  if i = j then l i / (k i) ^ 2 else -(l i + l j) / (2 * k i * k j)

def inverseB (k : Fin 3 → ℝ) (j : Fin 3) (i : Fin 3) : ℝ :=
  (if i = j then -1 else 1) / (2 * k j)

theorem transform_inverse (k l : Fin 3 → ℝ) (hk : ∀ i, k i ≠ 0) (j : Fin 3) :
    transform k l (inverseA k l j) (inverseB k j) = unit j := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [transform, inverseA, inverseB, unit] <;>
    field_simp [h0, h1, h2] <;> (try simp) <;> ring

/-- Three real numbers cannot have all three pairwise products negative. -/
theorem no_three_negative_products (k : Fin 3 → ℝ)
    (h01 : k 0 * k 1 < 0) (h02 : k 0 * k 2 < 0) (h12 : k 1 * k 2 < 0) : False := by
  rcases mul_neg_iff.mp h01 with h | h
  · have h2 : k 2 < 0 := (mul_neg_iff.mp h02).resolve_right (by intro t; linarith)
      |>.2
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos h.2.le h2.le)) h12
  · have h2 : 0 < k 2 := (mul_neg_iff.mp h02).resolve_left (by intro t; linarith)
      |>.2
    exact (not_lt_of_ge (mul_nonneg h.2.le h2.le)) h12

/-- The upper-left block of the inverse pure-head coefficient matrix cannot
be entrywise positive. -/
theorem inverseA_not_positive (k l : Fin 3 → ℝ) (_hk : ∀ i, k i ≠ 0)
    (hp : ∀ i j, 0 < inverseA k l j i) : False := by
  have hl (i : Fin 3) : 0 < l i := by
    have h := hp i i
    simp only [inverseA] at h
    exact (div_pos_iff.mp h).resolve_right (by
      intro hn
      exact (not_lt_of_ge (sq_nonneg (k i))) hn.2) |>.1
  have hpair (i j : Fin 3) (hij : i ≠ j) : k i * k j < 0 := by
    have h := hp i j
    simp only [inverseA, if_neg hij] at h
    have hn : -(l i + l j) < 0 := neg_neg_of_pos (add_pos (hl i) (hl j))
    have hd := ((div_pos_iff.mp h).resolve_left (by intro hp'; linarith)).2
    nlinarith
  exact no_three_negative_products k (hpair 0 1 (by decide))
    (hpair 0 2 (by decide)) (hpair 1 2 (by decide))

def columns (S B : Fin 3 → Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i ↦ ![S 0 i, S 1 i, S 2 i, B 0 i, B 1 i, B 2 i]

/-- The mixed coefficient matrix of the evenized pure three-head numerator. -/
def cross (k l : Fin 3 → ℝ) (S B T D : Fin 3 → Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j ↦ dotProduct (columns T D j)
    (transform k l (fun h ↦ S h i) (fun h ↦ B h i))

theorem factorization (k l : Fin 3 → ℝ) (S B T D : Fin 3 → Fin 6 → ℝ)
    (u : Fin 6 → ℝ) :
    (columns T D).mulVec
      (transform k l (fun h ↦ ∑ i, S h i * u i) (fun h ↦ ∑ i, B h i * u i)) =
        (cross k l S B T D).transpose.mulVec u := by
  funext j
  simp [columns, transform, cross, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem columns_unit (T D : Fin 3 → Fin 6 → ℝ) (j : Fin 3) :
    (columns T D).mulVec (unit j) = T j := by
  funext i
  fin_cases j <;> simp [columns, unit, Matrix.mulVec, dotProduct]

/-- A six-by-six cross matrix from three pure heads cannot have nonpositive
off-diagonal entries and strictly positive column sums. This does not assume
nonzero token differences: invertibility forces that condition internally. -/
theorem obstruction (k l : Fin 3 → ℝ) (S B T D : Fin 3 → Fin 6 → ℝ)
    (hS : ∀ h i, 0 < S h i) (hT : ∀ h i, 0 < T h i)
    (hoff : ∀ i j, i ≠ j → cross k l S B T D i j ≤ 0)
    (hsum : ∀ j, 0 < ∑ i, cross k l S B T D i j) : False := by
  let M := (cross k l S B T D).transpose
  have hmoff : ∀ i j, i ≠ j → M i j ≤ 0 := fun i j hij ↦ hoff j i (Ne.symm hij)
  have hinj : Function.Injective M.mulVecLin := mulVec_injective M hmoff hsum
  have hsur : Function.Surjective M.mulVecLin := LinearMap.injective_iff_surjective.mp hinj
  have hYsur : Function.Surjective (columns T D).mulVecLin := by
    intro v
    obtain ⟨u, hu⟩ := hsur v
    refine ⟨transform k l (fun h ↦ ∑ i, S h i * u i) (fun h ↦ ∑ i, B h i * u i), ?_⟩
    change (columns T D).mulVec _ = v
    rw [factorization]
    exact hu
  have hYinj : Function.Injective (columns T D).mulVecLin :=
    LinearMap.injective_iff_surjective.mpr hYsur
  have hsol (j : Fin 3) := positive_solution M hmoff hsum (T j) (hT j)
  choose u hu hMu using hsol
  let a (j h : Fin 3) := ∑ i, S h i * u j i
  let b (j h : Fin 3) := ∑ i, B h i * u j i
  have hcoeff (j : Fin 3) : transform k l (a j) (b j) = unit j := by
    apply hYinj
    change (columns T D).mulVec _ = (columns T D).mulVec _
    rw [columns_unit]
    simpa only [a, b, factorization] using hMu j
  have hk (j : Fin 3) : k j ≠ 0 := by
    intro hz
    have h := congrFun (hcoeff j) (j.castAdd 3)
    fin_cases j <;> dsimp at hz <;> simp [transform, unit, hz] at h
  have ha (j : Fin 3) : a j = inverseA k l j :=
    (transform_injective k l hk _ _ _ _ ((hcoeff j).trans (transform_inverse k l hk j).symm)).1
  apply inverseA_not_positive k l hk
  intro i j
  rw [← ha j]
  exact Finset.sum_pos (fun r _ ↦ mul_pos (hS i r) (hu j r)) Finset.univ_nonempty

/-- The even part of the cleared normalized three-head score. -/
theorem evenization (T : ℝ) (b u : Fin 3 → ℝ) :
    ((T * (1 + b 0) * (1 + b 1) * (1 + b 2) +
      u 0 * (1 + b 1) * (1 + b 2) + u 1 * (1 + b 0) * (1 + b 2) +
      u 2 * (1 + b 0) * (1 + b 1)) +
    (T * (1 - b 0) * (1 - b 1) * (1 - b 2) -
      u 0 * (1 - b 1) * (1 - b 2) - u 1 * (1 - b 0) * (1 - b 2) -
      u 2 * (1 - b 0) * (1 - b 1))) / 2 =
    T + (u 0 + T / 2 * b 0) * (b 1 + b 2) +
      (u 1 + T / 2 * b 1) * (b 0 + b 2) +
      (u 2 + T / 2 * b 2) * (b 0 + b 1) := by
  ring

end
end HeadComplexity.PureRoPEThreeHeadCross
