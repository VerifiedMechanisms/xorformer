import HeadComplexity.Research.IntegerSeparatorMarginRepair
import HeadComplexity.Atoms.UniformApproximation

set_option linter.style.header false

/-!
# Two-head margin repair for products of affine signs

The two affine factors may have arbitrary slope signs. A common strictly
positive affine denominator and a controlled perturbation give two genuine
original heads. Integer refitting of the two threshold factors then gives a
dimension-only relative margin, measured using full-cube head norms.
-/

noncomputable section

namespace HeadComplexity.TwoFactorMarginRepair

open Finset RelativeMarginQuantifiers
open scoped BigOperators

variable {n : ℕ}

theorem abs_affineValue_le (a : ℝ) (u : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hu : ∀ i, |u i| ≤ M)
    (x : Fin n → Bool) :
    |affineValue a u x| ≤ ((n : ℝ) + 1) * M := by
  have ht : ∀ i, |u i * boolToReal (x i)| ≤ M := by
    intro i
    cases x i <;> simp [boolToReal, hM, hu i]
  calc
    _ ≤ |a| + |∑ i, u i * boolToReal (x i)| := abs_add_le _ _
    _ ≤ M + ∑ i, |u i * boolToReal (x i)| :=
      add_le_add ha (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ M + ∑ _i : Fin n, M := add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ ht i)
    _ = ((n : ℝ) + 1) * M := by simp; ring

/-- A bounded unit-margin product has a two-head representation with explicit
relative margin. No sign restriction is placed on either affine factor. -/
theorem hasRelativeMargin_of_bounded_affine_product
    (a c : ℝ) (u v : Fin n → ℝ) (M : ℝ) (hM : 0 < M)
    (ha : |a| ≤ M) (hu : ∀ i, |u i| ≤ M)
    (hc : |c| ≤ M) (hv : ∀ i, |v i| ≤ M)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, 1 ≤ signedLabel f x *
      (affineValue a u x * affineValue c v x)) :
    HasRelativeMargin n 2 f (1 / (12 * ((n : ℝ) + 1) ^ 4 * M ^ 2)) := by
  classical
  let d : ℝ := n + 1
  let U : ℝ := d * M
  let ε : ℝ := 1 / (2 * U)
  have hd : 1 ≤ d := by dsimp [d]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hdpos : 0 < d := by linarith
  have hU : 0 < U := mul_pos hdpos hM
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεU : ε * U = 1 / 2 := by dsimp [ε]; field_simp
  have hMU : M ≤ U := by dsimp [U]; nlinarith
  have hεM : ε * M ≤ 1 / 2 := by nlinarith
  have hnew : ∀ z : ℝ, |z| ≤ M → 0 < 1 + ε * z := by
    intro z hz
    have hz' := mul_le_mul_of_nonneg_left (abs_le.mp hz).1 hε.le
    nlinarith
  let φ₀ : FracAtom n := FracAtom.ofPositiveAffineRatio a u 1 (fun _ ↦ 1)
    one_pos (fun _ ↦ one_pos)
  let φ₁ : FracAtom n := FracAtom.ofPositiveAffineRatio (-a) (fun i ↦ -u i)
    (1 + ε * c) (fun i ↦ 1 + ε * v i) (hnew c hc) (fun i ↦ hnew (v i) (hv i))
  let φ : Fin 2 → FracAtom n := ![φ₀, φ₁]
  let A : (Fin n → Bool) → ℝ := affineValue a u
  let D : (Fin n → Bool) → ℝ := affineValue c v
  let B : (Fin n → Bool) → ℝ := affineValue 1 (fun _ ↦ 1)
  let C : (Fin n → Bool) → ℝ := fun x ↦ B x + ε * D x
  have hA : ∀ x, |A x| ≤ U := fun x ↦ abs_affineValue_le a u M hM.le ha hu x
  have hD : ∀ x, |D x| ≤ U := fun x ↦ abs_affineValue_le c v M hM.le hc hv x
  have hB : ∀ x, 1 ≤ B x ∧ B x ≤ d := by
    intro x
    constructor
    · have hs := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ boolToReal_nonneg (x i)
      simpa [B, affineValue] using hs
    · have hs := Finset.sum_le_sum (s := Finset.univ)
        (fun i (_ : i ∈ Finset.univ) ↦ boolToReal_le_one (x i))
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
      dsimp [B, affineValue, d]
      simpa only [one_mul] using (show 1 + ∑ i, boolToReal (x i) ≤ (n : ℝ) + 1 by linarith)
  have hC : ∀ x, 1 / 2 ≤ C x ∧ C x ≤ 2 * d := by
    intro x
    have hbound := mul_le_mul_of_nonneg_left (abs_le.mp (hD x)).1 hε.le
    have hbound' := mul_le_mul_of_nonneg_left (abs_le.mp (hD x)).2 hε.le
    dsimp [C]
    constructor <;> nlinarith [hB x]
  have hBp : ∀ x, 0 < B x := fun x ↦ lt_of_lt_of_le one_pos (hB x).1
  have hCp : ∀ x, 0 < C x := fun x ↦ lt_of_lt_of_le (by norm_num) (hC x).1
  have hCeval : ∀ x, affineValue (1 + ε * c) (fun i ↦ 1 + ε * v i) x = C x := by
    intro x
    rw [affineValue_add, affineValue_smul]
  have heval₀ : ∀ x, φ₀.eval x = A x / B x := fun x ↦ FracAtom.ofPositiveAffineRatio_eval ..
  have heval₁ : ∀ x, φ₁.eval x = -A x / C x := by
    intro x
    rw [show φ₁.eval x = affineValue (-a) (fun i ↦ -u i) x /
      affineValue (1 + ε * c) (fun i ↦ 1 + ε * v i) x from FracAtom.ofPositiveAffineRatio_eval ..,
      hCeval]
    congr 1
    simp [A, affineValue, ← Finset.sum_neg_distrib, add_comm]
  have hscore : ∀ x, score φ 0 x = ε * (A x * D x) / (B x * C x) := by
    intro x
    simp only [score, zero_add, φ, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, heval₀, heval₁]
    dsimp [C]
    field_simp [(hBp x).ne', (show B x + ε * D x ≠ 0 from (hCp x).ne')]
    ring
  have hnorm₀ : atomSup φ₀ ≤ U := by
    apply Finset.sup'_le
    intro x _
    rw [heval₀, abs_div, abs_of_pos (hBp x)]
    apply (div_le_iff₀ (hBp x)).2
    nlinarith [hA x, (hB x).1]
  have hnorm₁ : atomSup φ₁ ≤ 2 * U := by
    apply Finset.sup'_le
    intro x _
    rw [heval₁, abs_div, abs_neg, abs_of_pos (hCp x)]
    apply (div_le_iff₀ (hCp x)).2
    nlinarith [hA x, (hC x).1]
  have hamp : amplitude φ 0 ≤ 3 * U := by
    simp only [amplitude, abs_zero, zero_add, φ, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  have hsigned : ∀ x, ε / (2 * d ^ 2) ≤ signedLabel f x * score φ 0 x := by
    intro x
    have hprod : B x * C x ≤ 2 * d ^ 2 := by
      nlinarith [mul_le_mul (hB x).2 (hC x).2 (hCp x).le hdpos.le]
    have hnum : 1 ≤ signedLabel f x * (A x * D x) := hf x
    rw [hscore]
    rw [show signedLabel f x * (ε * (A x * D x) / (B x * C x)) =
      ε * (signedLabel f x * (A x * D x)) / (B x * C x) by ring]
    apply (div_le_div_iff₀ (by positivity) (mul_pos (hBp x) (hCp x))).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hnum) (sq_nonneg d)]
  have hs : StrictlyRepresents f φ 0 := fun x ↦
    (div_pos hε (by positivity)).trans_le (hsigned x)
  refine ⟨φ, 0, hs, (le_relativeMargin_iff hs).2 fun x ↦ ?_⟩
  have hγ : 0 ≤ 1 / (12 * ((n : ℝ) + 1) ^ 4 * M ^ 2) := by positivity
  calc
    _ ≤ (1 / (12 * ((n : ℝ) + 1) ^ 4 * M ^ 2)) * (3 * U) :=
      mul_le_mul_of_nonneg_left hamp hγ
    _ = ε / (2 * d ^ 2) := by
      dsimp [ε, U, d]
      field_simp
      ring
    _ ≤ signedLabel f x * score φ 0 x := hsigned x

/-- Explicit dimension-only relative margin for agreement of two arbitrary
linear threshold truth tables. -/
def twoFactorRepairMargin (n : ℕ) : ℝ :=
  1 / (12 * ((n : ℝ) + 1) ^ 4 * ((n + 1).factorial : ℝ) ^ 2)

theorem twoFactorRepairMargin_pos (n : ℕ) : 0 < twoFactorRepairMargin n := by
  have hM : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  unfold twoFactorRepairMargin
  positivity

theorem hasRelativeMargin_of_two_LTFs (f g : (Fin n → Bool) → Bool)
    (hf : isLTF f) (hg : isLTF g) :
    HasRelativeMargin n 2 (fun x ↦ decide (f x = g x)) (twoFactorRepairMargin n) := by
  obtain ⟨a, ha, hab⟩ := IntegerSeparatorMarginRepair.exists_bounded_integer_affine n f hf
  obtain ⟨c, hc, hcb⟩ := IntegerSeparatorMarginRepair.exists_bounded_integer_affine n g hg
  apply hasRelativeMargin_of_bounded_affine_product (a 0) (c 0)
    (fun i ↦ (a i.succ : ℝ)) (fun i ↦ (c i.succ : ℝ))
    ((n + 1).factorial : ℝ) (by exact_mod_cast Nat.factorial_pos (n + 1))
    (hab 0) (fun i ↦ hab i.succ) (hcb 0) (fun i ↦ hcb i.succ)
  intro x
  have hp : 1 ≤ (signedLabel f x * affineValue (a 0) (fun i ↦ (a i.succ : ℝ)) x) *
      (signedLabel g x * affineValue (c 0) (fun i ↦ (c i.succ : ℝ)) x) := by
    nlinarith [ha x, hc x,
      mul_nonneg (sub_nonneg.mpr (ha x)) (sub_nonneg.mpr (hc x))]
  cases hfx : f x <;> cases hgx : g x <;> simp_all [signedLabel]

/-- The positive repair is a representation in the unchanged original model. -/
theorem computableWithHeadsN_of_two_LTFs (f g : (Fin n → Bool) → Bool)
    (hf : isLTF f) (hg : isLTF g) :
    computableWithHeadsN n 2 (fun x ↦ decide (f x = g x)) :=
  computable_of_hasRelativeMargin (hasRelativeMargin_of_two_LTFs f g hf hg)

end HeadComplexity.TwoFactorMarginRepair
