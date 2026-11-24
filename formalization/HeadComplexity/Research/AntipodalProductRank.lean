import HeadComplexity.Polynomial.SignRank
import Mathlib.Tactic

set_option linter.style.header false

/-!
Antipodal-complete sign matrices have full row sign rank. A sum of K
affine-times-product atoms across any bipartition has matrix rank at most
2K+1 when a free bias is included. These are comparison-class facts, not
an unrestricted lower bound for affine-ratio heads.
-/

noncomputable section

namespace HeadComplexity.AntipodalProductRank

open Finset
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def AntipodalComplete (f : ι → κ → Bool) : Prop :=
  ∀ s : ι → Bool, ∃ j, (∀ i, f i j = s i) ∨ (∀ i, f i j = !(s i))

lemma aligned_sum_pos (a b : ι → ℝ) (ha : ∃ i, a i ≠ 0)
    (hb : ∀ i, if 0 ≤ a i then 0 < b i else b i < 0) :
    0 < ∑ i, a i * b i := by
  classical
  have hn : ∀ i, 0 ≤ a i * b i := by
    intro i
    by_cases h : 0 ≤ a i
    · exact mul_nonneg h (le_of_lt (by simpa [h] using hb i))
    · exact le_of_lt (mul_pos_of_neg_of_neg (lt_of_not_ge h)
        (by simpa [h] using hb i))
  obtain ⟨i, hi⟩ := ha
  have hp : 0 < a i * b i := by
    by_cases h : 0 ≤ a i
    · exact mul_pos (lt_of_le_of_ne h (Ne.symm hi))
        (by simpa [h] using hb i)
    · exact mul_pos_of_neg_of_neg (lt_of_not_ge h)
        (by simpa [h] using hb i)
  exact lt_of_lt_of_le hp (single_le_sum (fun j _ => hn j) (mem_univ i))

theorem rank_eq_card_of_antipodal {f : ι → κ → Bool}
    (hf : AntipodalComplete f) {M : Matrix ι κ ℝ}
    (hM : StrictSignMatrix M f) : M.rank = Fintype.card ι := by
  classical
  apply LinearIndependent.rank_matrix
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hi
  let s : ι → Bool := fun j => decide (0 ≤ a j)
  obtain ⟨j, hj | hj⟩ := hf s
  · have hb : ∀ k, if 0 ≤ a k then 0 < M k j else M k j < 0 := by
      intro k
      simpa [hj k, s] using hM k j
    have hp := aligned_sum_pos a (fun k => M k j) ⟨i, hi⟩ hb
    have hz := congrFun ha j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row] at hz
    exact (ne_of_gt hp) hz
  · have hb : ∀ k, if 0 ≤ a k then 0 < -M k j else -M k j < 0 := by
      intro k
      have hh := hM k j
      rw [hj k] at hh
      by_cases hk : 0 ≤ a k
      · simp [s, hk] at hh ⊢
        exact hh
      · simp [s, hk] at hh ⊢
        exact hh
    have hp := aligned_sum_pos a (fun k => -M k j) ⟨i, hi⟩ hb
    have hz := congrFun ha j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row] at hz
    have hz' : (∑ k, a k * -M k j) = 0 := by
      simp_rw [mul_neg, sum_neg_distrib, hz, neg_zero]
    exact (ne_of_gt hp) hz'

theorem signRank_eq_card_of_antipodal {f : ι → κ → Bool}
    (hf : AntipodalComplete f) : signRank f = Fintype.card ι := by
  obtain ⟨M, hM, hr⟩ := exists_strictSignMatrix_rank_eq f
  rw [← hr]
  exact rank_eq_card_of_antipodal hf hM

def productMatrix (a u : ι → ℝ) (b v : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => (a i + b j) * u i * v j

theorem productMatrix_rank_le_two (a u : ι → ℝ) (b v : κ → ℝ) :
    (productMatrix a u b v).rank ≤ 2 := by
  have he : productMatrix a u b v =
      Matrix.vecMulVec (fun i => a i*u i) v +
      Matrix.vecMulVec u (fun j => b j*v j) := by
    ext i j
    simp only [productMatrix, Matrix.add_apply, Matrix.vecMulVec_apply]
    ring
  rw [he]
  exact (HeadComplexity.Matrix.rank_add_le _ _).trans
    (Nat.add_le_add (Matrix.rank_vecMulVec_le _ _) (Matrix.rank_vecMulVec_le _ _))

def productScoreMatrix {H : ℕ} (c : ℝ) (a u : Fin H → ι → ℝ)
    (b v : Fin H → κ → ℝ) : Matrix ι κ ℝ :=
  Matrix.vecMulVec (fun _ : ι => c) (fun _ : κ => 1) +
    ∑ h, productMatrix (a h) (u h) (b h) (v h)

theorem productScoreMatrix_rank_le {H : ℕ} (c : ℝ)
    (a u : Fin H → ι → ℝ) (b v : Fin H → κ → ℝ) :
    (productScoreMatrix c a u b v).rank ≤ 2*H+1 := by
  have hc' := Matrix.rank_vecMulVec_le (fun _ : ι => c) (fun _ : κ => (1 : ℝ))
  have hs : (∑ h, productMatrix (a h) (u h) (b h) (v h)).rank ≤ 2*H := by
    refine (HeadComplexity.Matrix.rank_sum_le _).trans ?_
    calc
      (∑ h, (productMatrix (a h) (u h) (b h) (v h)).rank) ≤ ∑ _ : Fin H, 2 :=
        sum_le_sum fun h _ => productMatrix_rank_le_two _ _ _ _
      _ = 2*H := by simp [Nat.mul_comm]
  unfold productScoreMatrix
  exact (HeadComplexity.Matrix.rank_add_le _ _).trans (by omega)

theorem product_width_of_antipodal {H : ℕ} {f : ι → κ → Bool}
    (hf : AntipodalComplete f) (c : ℝ)
    (a u : Fin H → ι → ℝ) (b v : Fin H → κ → ℝ)
    (hrep : StrictSignMatrix (productScoreMatrix c a u b v) f) :
    Fintype.card ι ≤ 2*H+1 := by
  rw [← rank_eq_card_of_antipodal hf hrep]
  exact productScoreMatrix_rank_le c a u b v

#print axioms rank_eq_card_of_antipodal
#print axioms product_width_of_antipodal

end HeadComplexity.AntipodalProductRank
