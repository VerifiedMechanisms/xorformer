import HeadComplexity.Atoms.UniformApproximation

set_option linter.style.header false

/-!
# A whole affine block on a positive face costs one atom

The numerator may be any affine function. Large negative denominator slopes
suppress inputs outside the chosen positive face, while small slopes on the
other coordinates preserve the affine function on that face.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- One atom uniformly approximates a positive monomial times an arbitrary
real affine function, including all its coefficients together. -/
theorem exists_fracAtom_approx_monomial_mul_affineValue
    (S : Finset (Fin n)) (c : ℝ) (cs : Fin n → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : FracAtom n, ∀ bits,
      |φ.eval bits - squarefreeMonomial S bits * affineValue c cs bits| < ε := by
  classical
  let C : ℝ := 1 + ∑ bits : Fin n → Bool, |affineValue c cs bits|
  have hC : 0 < C := by
    dsimp [C]
    have := Finset.sum_nonneg (fun bits (_ : bits ∈ Finset.univ) ↦
      abs_nonneg (affineValue c cs bits))
    linarith
  have hbound : ∀ bits, |affineValue c cs bits| < C := by
    intro bits
    have := Finset.single_le_sum
      (fun y (_ : y ∈ Finset.univ) ↦ abs_nonneg (affineValue c cs y))
      (Finset.mem_univ bits)
    dsimp [C]
    linarith
  let R : ℝ := 1 + C / ε
  have hR : 0 < R := by dsimp [R]; positivity
  let δ : ℝ := ε / (C * (n + 1 : ℝ))
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδ : 0 < δ := div_pos hε (mul_pos hC hn)
  let w : Fin n → ℝ := fun i ↦ if i ∈ S then R else δ
  have hw : ∀ i, 0 < w i := fun i ↦ by dsimp [w]; split <;> assumption
  let b₀ : ℝ := 1 + ∑ i, w i
  let b : Fin n → ℝ := fun i ↦ -w i
  have hb₀ : 0 < b₀ := by
    dsimp [b₀]
    have : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ ↦ (hw i).le
    linarith
  have hb : ∀ i, b i < 0 := fun i ↦ by dsimp [b]; exact neg_neg_of_pos (hw i)
  have hbmargin : ∑ i, -b i < b₀ := by
    dsimp [b₀, b]
    simp only [neg_neg]
    linarith
  let φ : FracAtom n := FracAtom.ofNegativeAffineRatio c cs b₀ b hb₀ hb hbmargin
  refine ⟨φ, fun bits ↦ ?_⟩
  let T : ℝ := ∑ i, w i * (1 - boolToReal (bits i))
  let L : ℝ := affineValue c cs bits
  have hsub : ∀ i, 0 ≤ 1 - boolToReal (bits i) := fun i ↦ by
    linarith [boolToReal_le_one (bits i)]
  have hT : 0 ≤ T :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i).le (hsub i)
  have hden : affineValue b₀ b bits = 1 + T := by
    dsimp [b₀, b, T]
    unfold affineValue
    simp_rw [mul_sub]
    simp only [mul_one]
    rw [Finset.sum_sub_distrib]
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib]
    ring
  have hdenpos : 0 < 1 + T := by linarith
  rw [show φ.eval bits = L / affineValue b₀ b bits by
    exact FracAtom.ofNegativeAffineRatio_eval c cs b₀ b hb₀ hb hbmargin bits, hden]
  by_cases hall : ∀ i ∈ S, bits i = true
  · have hmono : squarefreeMonomial S bits = 1 := by
      unfold squarefreeMonomial
      exact Finset.prod_eq_one fun i hi ↦ by simp [boolToReal, hall i hi]
    rw [hmono, one_mul]
    change |L / (1 + T) - L| < ε
    have hterm : ∀ i, w i * (1 - boolToReal (bits i)) ≤ δ := by
      intro i
      by_cases hi : i ∈ S
      · simp [hall i hi, boolToReal, hδ.le]
      · dsimp [w]
        rw [if_neg hi]
        nlinarith [boolToReal_nonneg (bits i)]
    have hTle : T ≤ (n : ℝ) * δ := by
      calc
        T ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ ↦ hterm i
        _ = (n : ℝ) * δ := by simp
    have hTlt : T < δ * (n + 1 : ℝ) := by nlinarith
    have hnum_nonneg : 0 ≤ |L| * T := mul_nonneg (abs_nonneg _) hT
    have hnum_lt : |L| * T < ε := by
      have hfirst : |L| * T ≤ C * T :=
        mul_le_mul_of_nonneg_right (hbound bits).le hT
      have hsecond : C * T < C * (δ * (n + 1 : ℝ)) :=
        mul_lt_mul_of_pos_left hTlt hC
      have heq : C * (δ * (n + 1 : ℝ)) = ε := by
        dsimp [δ]
        field_simp [hC.ne', hn.ne']
      exact hfirst.trans_lt (hsecond.trans_eq heq)
    have herr : |L / (1 + T) - L| = |L| * T / (1 + T) := by
      rw [show L / (1 + T) - L = -(L * T / (1 + T)) by
        field_simp [hdenpos.ne']
        ring]
      rw [abs_neg, abs_div, abs_mul, abs_of_nonneg hT, abs_of_pos hdenpos]
    rw [herr]
    exact (div_le_self hnum_nonneg (by linarith : 1 ≤ 1 + T)).trans_lt hnum_lt
  · push Not at hall
    obtain ⟨i, hi, hifalse⟩ := hall
    have hibool : bits i = false := by
      cases hbit : bits i
      · rfl
      · exact (hifalse hbit).elim
    have hmono : squarefreeMonomial S bits = 0 := by
      unfold squarefreeMonomial
      apply Finset.prod_eq_zero hi
      simp [boolToReal, hibool]
    rw [hmono, zero_mul, sub_zero, abs_div, abs_of_pos hdenpos]
    change |L| / (1 + T) < ε
    have hiterm : w i * (1 - boolToReal (bits i)) = R := by
      simp [w, hi, hibool, boolToReal]
    have hTge : R ≤ T := by
      rw [← hiterm]
      exact Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (hw j).le (hsub j)) (Finset.mem_univ i)
    have hCR : C < ε * R := by
      dsimp [R]
      field_simp [hε.ne']
      linarith
    apply (div_lt_iff₀ hdenpos).mpr
    exact (hbound bits).trans (hCR.trans_le
      (mul_le_mul_of_nonneg_left (by linarith : R ≤ 1 + T) hε.le))

/-- Uniform one-atom interface for a whole affine block on a positive face. -/
theorem uniformlyOneAtomApproximable_monomial_mul_affineValue
    (S : Finset (Fin n)) (c : ℝ) (cs : Fin n → ℝ) :
    UniformlyOneAtomApproximable
      (fun bits ↦ squarefreeMonomial S bits * affineValue c cs bits) :=
  fun ε hε ↦ exists_fracAtom_approx_monomial_mul_affineValue S c cs ε hε

end HeadComplexity
