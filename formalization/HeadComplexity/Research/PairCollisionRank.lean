import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# A rank constraint on two-head Boolean cancellation

The cleared quadratic of two affine-ratio heads has rank at most four.  If it
vanishes on every Boolean subset, this bounds the coordinates on which both a
numerator coefficient and the denominator difference are nonzero.
-/

noncomputable section
namespace HeadComplexity.PairCollisionRank
open scoped BigOperators

variable {n : ℕ}

def quadraticMatrix (a c b d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => a i * d j + d i * a j + c i * b j + b i * c j

lemma quadraticMatrix_rank_le (a c b d : Fin n → ℝ) :
    (quadraticMatrix a c b d).rank ≤ 4 := by
  let L : Matrix (Fin n) (Fin 4) ℝ := fun i => ![a i, d i, c i, b i]
  let R : Matrix (Fin 4) (Fin n) ℝ := ![d, a, b, c]
  have hf : quadraticMatrix a c b d = L * R := by
    ext i j
    change a i * d j + d i * a j + c i * b j + b i * c j =
      ∑ k : Fin 4, L i k * R k j
    simp [Fin.sum_univ_succ, L, R]
    ring
  rw [hf]
  exact (Matrix.rank_mul_le_left L R).trans (by
    simpa using Matrix.rank_le_card_width L)

/-- The one-coordinate and two-coordinate equations imply a diagonal
quadratic matrix. -/
lemma quadraticMatrix_eq_diagonal (a c b d : Fin n → ℝ)
    (hpair : ∀ i j, i ≠ j →
      a i * d j + a j * d i + c i * b j + c j * b i = 0) :
    quadraticMatrix a c b d =
      Matrix.diagonal (fun i => 2 * (a i * d i + c i * b i)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [quadraticMatrix]
    ring
  · simp only [Matrix.diagonal_apply_ne _ hij, quadraticMatrix]
    nlinarith [hpair i j hij]

lemma diagonal_ne_zero_iff (a c b d : Fin n → ℝ)
    (hsingle : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0)
    (hb : ∀ i, 0 < b i) (i : Fin n) :
    2 * (a i * d i + c i * b i) ≠ 0 ↔ a i ≠ 0 ∧ b i ≠ d i := by
  constructor
  · intro h
    constructor
    · intro ha
      have hs := hsingle i
      rw [ha, zero_mul, zero_add] at hs
      have hc : c i = 0 := (mul_eq_zero.mp hs).resolve_right (by linarith [hb i])
      simp [ha, hc] at h
    · intro hbd
      have hs := hsingle i
      rw [← hbd] at hs
      have hp : (a i + c i) * (1 + b i) = 0 := by nlinarith
      have hc : a i + c i = 0 :=
        (mul_eq_zero.mp hp).resolve_right (by linarith [hb i])
      apply h
      rw [← hbd]
      nlinarith
  · rintro ⟨ha, hbd⟩ hz
    have hc : c i = -a i := by linarith [hsingle i]
    have he : a i * (d i - b i) = 0 := by rw [hc] at hz; nlinarith
    exact hbd (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ha)).symm

/-- Positivity improves the rank bound to three: the cube center is a
stationary point of every quadratic vanishing on the cube. -/
lemma quadraticMatrix_rank_le_three (a c b d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i)
    (hsingle : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0)
    (hpair : ∀ i j, i ≠ j →
      a i * d j + a j * d i + c i * b j + c j * b i = 0) :
    (quadraticMatrix a c b d).rank ≤ 3 := by
  let A := ∑ i, a i
  let B := 2 + ∑ i, b i
  let C := ∑ i, c i
  let D := 2 + ∑ i, d i
  have hD : 0 < D := by
    dsimp [D]
    have hs : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ => (hd i).le)
    linarith
  have hrel : ∀ i, D * a i + A * d i + B * c i + C * b i = 0 := by
    intro i
    have hs : (∑ j, quadraticMatrix a c b d i j) =
        quadraticMatrix a c b d i i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        dsimp [quadraticMatrix]
        nlinarith [hpair i j hji.symm]
      · simp
    simp only [quadraticMatrix, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    dsimp [A, B, C, D]
    nlinarith [hsingle i]
  let L : Matrix (Fin n) (Fin 3) ℝ := fun i => ![d i, c i, b i]
  let R : Matrix (Fin 3) (Fin n) ℝ :=
    ![fun j => a j - A / D * d j,
      fun j => b j - B / D * d j,
      fun j => c j - C / D * d j]
  have hf : quadraticMatrix a c b d = L * R := by
    ext i j
    change a i * d j + d i * a j + c i * b j + b i * c j =
      ∑ k : Fin 3, L i k * R k j
    simp only [Fin.sum_univ_succ, L, R, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    field_simp [ne_of_gt hD]
    have hr := congrArg (fun z : ℝ => z * d j) (hrel i)
    nlinarith [hr]
  rw [hf]
  exact (Matrix.rank_mul_le_left L R).trans (by
    simpa using Matrix.rank_le_card_width L)

/-- With positive second-denominator slopes, only three coordinates can
simultaneously be active and have differing slopes. -/
theorem card_active_different_le_three (a c b d : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i)
    (hsingle : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0)
    (hpair : ∀ i j, i ≠ j →
      a i * d j + a j * d i + c i * b j + c j * b i = 0) :
    Fintype.card {i : Fin n // a i ≠ 0 ∧ b i ≠ d i} ≤ 3 := by
  have hr := quadraticMatrix_rank_le_three a c b d hd hsingle hpair
  rw [quadraticMatrix_eq_diagonal a c b d hpair, Matrix.rank_diagonal] at hr
  simpa only [diagonal_ne_zero_iff a c b d hsingle hb] using hr

/-- At most four coordinates can have both a nonzero normalized numerator
coefficient and a different denominator slope. -/
theorem card_active_different_le_four (a c b d : Fin n → ℝ)
    (hb : ∀ i, 0 < b i)
    (hsingle : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0)
    (hpair : ∀ i j, i ≠ j →
      a i * d j + a j * d i + c i * b j + c j * b i = 0) :
    Fintype.card {i : Fin n // a i ≠ 0 ∧ b i ≠ d i} ≤ 4 := by
  have hr := quadraticMatrix_rank_le a c b d
  rw [quadraticMatrix_eq_diagonal a c b d hpair, Matrix.rank_diagonal] at hr
  simpa only [diagonal_ne_zero_iff a c b d hsingle hb] using hr

/-- The coefficient hypotheses above follow from a genuine identity on all
Boolean subsets, without a polynomial identity away from the cube. -/
theorem card_active_different_le_four_of_cube_identity (a c b d : Fin n → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcube : ∀ s : Finset (Fin n),
      (∑ i ∈ s, a i) * (1 + ∑ i ∈ s, d i) +
      (∑ i ∈ s, c i) * (1 + ∑ i ∈ s, b i) = 0) :
    Fintype.card {i : Fin n // a i ≠ 0 ∧ b i ≠ d i} ≤ 4 := by
  have hs : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0 := by
    intro i
    simpa using hcube {i}
  apply card_active_different_le_four a c b d hb hs
  intro i j hij
  have hp := hcube {i, j}
  simp only [Finset.sum_insert, Finset.mem_singleton, hij, not_false_eq_true,
    Finset.sum_singleton] at hp
  nlinarith [hs i, hs j]

/-- The coefficient hypotheses above follow from a genuine identity on all
Boolean subsets, without a polynomial identity away from the cube. -/
theorem card_active_different_le_three_of_cube_identity (a c b d : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i)
    (hcube : ∀ s : Finset (Fin n),
      (∑ i ∈ s, a i) * (1 + ∑ i ∈ s, d i) +
      (∑ i ∈ s, c i) * (1 + ∑ i ∈ s, b i) = 0) :
    Fintype.card {i : Fin n // a i ≠ 0 ∧ b i ≠ d i} ≤ 3 := by
  have hs : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0 := by
    intro i
    simpa using hcube {i}
  apply card_active_different_le_three a c b d hb hd hs
  intro i j hij
  have hp := hcube {i, j}
  simp only [Finset.sum_insert, Finset.mem_singleton, hij, not_false_eq_true,
    Finset.sum_singleton] at hp
  nlinarith [hs i, hs j]

/-- In at least four coordinates, a nonzero-everywhere numerator forces an
agreeing denominator coordinate. -/
theorem exists_agreeing_coordinate (a c b d : Fin n → ℝ)
    (hn : 4 ≤ n) (hb : ∀ i, 0 < b i) (hd : ∀ i, 0 < d i)
    (ha : ∀ i, a i ≠ 0)
    (hsingle : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0)
    (hpair : ∀ i j, i ≠ j →
      a i * d j + a j * d i + c i * b j + c j * b i = 0) :
    ∃ i, b i = d i := by
  by_contra h
  push Not at h
  have hr := card_active_different_le_three a c b d hb hd hsingle hpair
  let e : {i : Fin n // a i ≠ 0 ∧ b i ≠ d i} ≃ Fin n :=
    ⟨Subtype.val, fun i => ⟨i, ha i, h i⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e] at hr
  simp only [Fintype.card_fin] at hr
  omega

/-- A complete graph on at least three vertices cannot carry nonzero real
values that satisfy positive weighted opposite-sign equations on every edge. -/
lemma zero_of_positive_pair_equations (a : Fin n → ℝ)
    (p : Fin n → Fin n → ℝ) (hn : 3 ≤ n)
    (hp : ∀ i j, i ≠ j → 0 < p i j)
    (he : ∀ i j, i ≠ j → a i * p i j + a j * p j i = 0) :
    ∀ i, a i = 0 := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have h02 : i0 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i0, i2] at this
  have h12 : i1 ≠ i2 := by intro h; have := congrArg Fin.val h; simp [i1, i2] at this
  have no_pos : ∀ a' : Fin n → ℝ,
      (∀ i j, i ≠ j → a' i * p i j + a' j * p j i = 0) → ¬ 0 < a' i0 := by
    intro a' ha ha0
    have ha1 : a' i1 < 0 := by
      by_contra h
      have h1 := mul_nonneg (le_of_not_gt h) (hp i1 i0 h01.symm).le
      have h0 := mul_pos ha0 (hp i0 i1 h01)
      linarith [ha i0 i1 h01]
    have ha2 : a' i2 < 0 := by
      by_contra h
      have h2 := mul_nonneg (le_of_not_gt h) (hp i2 i0 h02.symm).le
      have h0 := mul_pos ha0 (hp i0 i2 h02)
      linarith [ha i0 i2 h02]
    have h1 := mul_neg_of_neg_of_pos ha1 (hp i1 i2 h12)
    have h2 := mul_neg_of_neg_of_pos ha2 (hp i2 i1 h12.symm)
    linarith [ha i1 i2 h12]
  have ha0 : a i0 = 0 := by
    have hle := le_of_not_gt (no_pos a he)
    have hge := no_pos (fun i => -a i) (by
      intro i j hij
      nlinarith [he i j hij])
    linarith
  intro i
  by_cases hi : i = i0
  · simpa [hi] using ha0
  · have h := he i i0 hi
    rw [ha0, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (ne_of_gt (hp i i0 hi))

/-- Opposite coherent denominator orientations admit no nontrivial normalized
two-head relation in at least three input coordinates. -/
theorem opposite_orientations_independent (a c b d : Fin n → ℝ)
    (hn : 3 ≤ n) (hb : ∀ i, 0 < b i) (hd : ∀ i, d i < 0)
    (hdv : ∀ i, 0 < 1 + d i)
    (hsingle : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0)
    (hpair : ∀ i j, i ≠ j →
      a i * d j + a j * d i + c i * b j + c j * b i = 0) :
    (∀ i, a i = 0) ∧ (∀ i, c i = 0) := by
  let r : Fin n → ℝ := fun i => (1 + d i) / (1 + b i)
  have hr : ∀ i, 0 < r i := fun i => div_pos (hdv i) (by linarith [hb i])
  have hc : ∀ i, c i = -r i * a i := by
    intro i
    dsimp [r]
    field_simp [show 1 + b i ≠ 0 by linarith [hb i]]
    nlinarith [hsingle i]
  let p : Fin n → Fin n → ℝ := fun i j => r i * b j - d j
  have hp : ∀ i j, i ≠ j → 0 < p i j := by
    intro i j _
    dsimp [p]
    have h := mul_pos (hr i) (hb j)
    linarith [hd j]
  have he : ∀ i j, i ≠ j → a i * p i j + a j * p j i = 0 := by
    intro i j hij
    have h := hpair i j hij
    rw [hc i, hc j] at h
    dsimp [p]
    nlinarith
  have ha := zero_of_positive_pair_equations a p hn hp he
  exact ⟨ha, fun i => by rw [hc i, ha i, mul_zero]⟩

/-- Direct full-cube formulation of opposite-orientation independence. -/
theorem opposite_orientations_independent_of_cube_identity (a c b d : Fin n → ℝ)
    (hn : 3 ≤ n) (hb : ∀ i, 0 < b i) (hd : ∀ i, d i < 0)
    (hdv : ∀ i, 0 < 1 + d i)
    (hcube : ∀ s : Finset (Fin n),
      (∑ i ∈ s, a i) * (1 + ∑ i ∈ s, d i) +
      (∑ i ∈ s, c i) * (1 + ∑ i ∈ s, b i) = 0) :
    (∀ i, a i = 0) ∧ (∀ i, c i = 0) := by
  have hs : ∀ i, a i * (1 + d i) + c i * (1 + b i) = 0 := by
    intro i
    simpa using hcube {i}
  apply opposite_orientations_independent a c b d hn hb hd hdv hs
  intro i j hij
  have hp := hcube {i, j}
  simp only [Finset.sum_insert, Finset.mem_singleton, hij, not_false_eq_true,
    Finset.sum_singleton] at hp
  nlinarith [hs i, hs j]

end HeadComplexity.PairCollisionRank
