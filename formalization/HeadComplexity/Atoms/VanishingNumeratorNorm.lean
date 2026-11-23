import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.AffineHead
import HeadComplexity.Results.SymmetricComplexity
import Mathlib.Tactic

set_option linter.style.header false

/-! An exact two-head unit-margin family whose normalized numerator norm
tends to zero. This disproves unconditional attainment of that optimization
problem; it does not prove a worst-case head lower bound. -/

namespace HeadComplexity.VanishingNumeratorNorm

open scoped BigOperators

noncomputable def profile (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  1 + 4*t*k / (1+t*k) - 2*t*k / (t+n-k)

theorem profile_origin (n : ℕ) (t : ℝ) : profile n t 0 = 1 := by
  simp [profile]

theorem profile_below_top {n k : ℕ} {t : ℝ}
    (ht : 0 < t) (hk : k < n) (hb : 4*t*n ≤ 1) : 1 ≤ profile n t k := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have htn : t*k ≤ t*n := mul_le_mul_of_nonneg_left (by linarith) ht.le
  have htk : 0 ≤ t*k := mul_nonneg ht.le hk0
  have hd1 : 0 < 1+t*k := by positivity
  have hd2 : 0 < t+n-k := by linarith
  have hfirst : 2*t*k ≤ 4*t*k / (1+t*k) := by
    apply (le_div_iff₀ hd1).mpr
    have hmul := mul_le_mul_of_nonneg_left
      (show 1+t*k ≤ 2 by nlinarith) (show 0 ≤ 2*t*k by positivity)
    nlinarith
  have hsecond : 2*t*k / (t+n-k) ≤ 2*t*k := by
    apply (div_le_iff₀ hd2).mpr
    have hmul := mul_le_mul_of_nonneg_left
      (show 1 ≤ t+n-k by linarith) (show 0 ≤ 2*t*k by positivity)
    nlinarith
  unfold profile
  linarith

theorem profile_top {n : ℕ} {t : ℝ} (hn : 2 ≤ n)
    (ht : 0 < t) (hb : 4*t*n ≤ 1) : profile n t n ≤ -1 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htn : 0 ≤ t*(n : ℝ) := by positivity
  have hd : 0 < 1+t*n := by positivity
  have hfirst : 4*t*n / (1+t*n) ≤ 4*t*n := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (t*(n : ℝ))]
  have hsecond : 2*t*n / (t+n-n) = 2*n := by
    field_simp [ht.ne']
    ring
  unfold profile
  rw [hsecond]
  linarith

noncomputable def label (n : ℕ) (x : Fin n → Bool) : ℝ :=
  if hammingWeight x = n then -1 else 1

theorem profile_unit_margin {n : ℕ} {t : ℝ} (hn : 2 ≤ n)
    (ht : 0 < t) (hb : 4*t*n ≤ 1) (x : Fin n → Bool) :
    1 ≤ label n x * profile n t (hammingWeight x) := by
  unfold label
  split_ifs with hh
  · rw [hh]
    have h := profile_top hn ht hb
    linarith
  · have hk := hammingWeight_le n x
    simpa using profile_below_top ht (lt_of_le_of_ne hk hh) hb

noncomputable def numerator (n : ℕ) (t : ℝ) : Fin 2 → Fin n → ℝ :=
  ![fun _ ↦ 4*t, fun _ ↦ -2*t/(n+t)]

noncomputable def slope (n : ℕ) (t : ℝ) : Fin 2 → Fin n → ℝ :=
  ![fun _ ↦ t, fun _ ↦ -1/(n+t)]

noncomputable def normSquare (n : ℕ) (u : Fin 2 → Fin n → ℝ) : ℝ :=
  ∑ h, ∑ i, (u h i)^2

noncomputable def totalScore (n : ℕ) (u b : Fin 2 → Fin n → ℝ)
    (x : Fin n → Bool) : ℝ :=
  1 + ∑ h, affineValue 0 (u h) x / affineValue 1 (b h) x

theorem constant_affine (n : ℕ) (c d : ℝ) (x : Fin n → Bool) :
    affineValue c (fun _ ↦ d) x = c + d * hammingWeight x := by
  simp [affineValue, ← Finset.mul_sum, ← hammingWeight_eq_sum]

theorem totalScore_eq_profile {n : ℕ} {t : ℝ} (hn : 2 ≤ n) (ht : 0 < t)
    (x : Fin n → Bool) :
    totalScore n (numerator n t) (slope n t) x = profile n t (hammingWeight x) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnt : (n : ℝ) + t ≠ 0 := by linarith
  have hk : (hammingWeight x : ℝ) ≤ n := by exact_mod_cast hammingWeight_le n x
  have hden : t+(n : ℝ)-hammingWeight x ≠ 0 := by linarith
  simp only [totalScore, Fin.sum_univ_two, numerator, slope, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, constant_affine, zero_add, profile]
  have hfrac : (-2*t/(n+t) * (hammingWeight x : ℝ)) /
      (1 + -1/(n+t) * hammingWeight x) = -2*t*hammingWeight x/(t+n-hammingWeight x) := by
    calc
      _ = (-2*t*hammingWeight x/(n+t)) /
          ((t+n-hammingWeight x)/(n+t)) := by
        congr 1 <;> field_simp [hnt] <;> ring
      _ = _ := div_div_div_cancel_right₀ hnt _ _
  rw [hfrac]
  ring

theorem normSquare_bound {n : ℕ} {t : ℝ} (hn : 2 ≤ n) (ht : 0 < t) :
    normSquare n (numerator n t) ≤ 20*n*t^2 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnt : 1 ≤ (n : ℝ) + t := by linarith
  have hp : 0 < (n : ℝ) + t := by linarith
  have hratio : |(-2*t)/((n : ℝ)+t)| ≤ 2*t := by
    rw [abs_div, abs_of_pos hp, abs_of_neg (by nlinarith : -2*t < 0)]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hsq : (-2*t/((n : ℝ)+t))^2 ≤ 4*t^2 := by
    have ha0 := abs_nonneg (-2*t/((n : ℝ)+t))
    have hh := mul_le_mul hratio hratio ha0 (by positivity : 0 ≤ 2*t)
    nlinarith [sq_abs (-2*t/((n : ℝ)+t))]
  simp only [normSquare, Fin.sum_univ_two, numerator, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (n : ℝ))
  nlinarith

theorem arbitrarily_small_norm (n : ℕ) (hn : 2 ≤ n) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ 4*t*n ≤ 1 ∧ normSquare n (numerator n t) < η ∧
      ∀ x, 1 ≤ label n x * totalScore n (numerator n t) (slope n t) x := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  let t := min (1/(8*(n : ℝ))) (η/(40*n+1))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 := min_le_left (1/(8*(n : ℝ))) (η/(40*n+1))
  have ht2 := min_le_right (1/(8*(n : ℝ))) (η/(40*n+1))
  have hbudget : t * (8*n) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht1
  have hsmall : t * (40*n+1) ≤ η := (le_div_iff₀ (by positivity)).mp ht2
  have htone : t ≤ 1 := by nlinarith
  have htsq : t^2 ≤ t := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htone)]
  have hb : 4*t*n ≤ 1 := by nlinarith
  refine ⟨t, ht, hb, ?_, ?_⟩
  · calc
      _ ≤ 20*n*t^2 := normSquare_bound hn ht
      _ ≤ 20*n*t := mul_le_mul_of_nonneg_left htsq (by positivity)
      _ < η := by nlinarith
  · intro x
    rw [totalScore_eq_profile hn ht]
    exact profile_unit_margin hn ht hb x

noncomputable def firstAtom (n : ℕ) (t : ℝ) (ht : 0 < t) : FracAtom n :=
  FracAtom.ofPositiveAffineRatio 0 (fun _ ↦ 4*t) 1 (fun _ ↦ t)
    (by norm_num) (fun _ ↦ ht)

noncomputable def secondAtom (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) : FracAtom n :=
  FracAtom.ofNegativeAffineRatio 0 (fun _ ↦ -2*t) (n+t) (fun _ ↦ -1)
    (by positivity) (by intro _; norm_num) (by simp; linarith)

noncomputable def atoms (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) : Fin 2 → FracAtom n :=
  ![firstAtom n t ht, secondAtom n hn t ht]

theorem atoms_score (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) (x : Fin n → Bool) :
    1 + ∑ h : Fin 2, (atoms n hn t ht h).eval x = profile n t (hammingWeight x) := by
  simp only [atoms, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    firstAtom, secondAtom, FracAtom.ofPositiveAffineRatio_eval,
    FracAtom.ofNegativeAffineRatio_eval, constant_affine, zero_add, profile]
  ring

theorem family_slopes (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) :
    (∀ i, 0 < slope n t 0 i) ∧ (∀ i, slope n t 1 i < 0) ∧
      (∑ i : Fin n, -slope n t 1 i < 1) := by
  have hnt : 0 < (n : ℝ)+t := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [slope] using ht
  · intro i
    simp only [slope, Matrix.cons_val_one, Matrix.head_cons]
    exact div_neg_of_neg_of_pos (by norm_num) hnt
  · simp only [slope, Matrix.cons_val_one, Matrix.cons_val_zero, neg_div, neg_neg,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one hnt).mpr (by linarith)

theorem normSquare_nonneg (n : ℕ) (u : Fin 2 → Fin n → ℝ) : 0 ≤ normSquare n u := by
  exact Finset.sum_nonneg fun h _ ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg (u h i)

theorem norm_positive_of_unit_margin (n : ℕ) (u b : Fin 2 → Fin n → ℝ)
    (hmargin : ∀ x, 1 ≤ label n x * totalScore n u b x) : 0 < normSquare n u := by
  by_contra hn
  have hzero : normSquare n u = 0 := le_antisymm (le_of_not_gt hn) (normSquare_nonneg n u)
  have hu : ∀ h i, u h i = 0 := by
    intro h i
    have houter := Finset.single_le_sum
      (f := fun h : Fin 2 ↦ ∑ i : Fin n, (u h i)^2)
      (fun h _ ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg (u h i)) (Finset.mem_univ h)
    have hinner := Finset.single_le_sum
      (f := fun i : Fin n ↦ (u h i)^2)
      (fun i _ ↦ sq_nonneg (u h i)) (Finset.mem_univ i)
    change (∑ i, (u h i)^2) ≤ normSquare n u at houter
    rw [hzero] at houter
    nlinarith [sq_nonneg (u h i)]
  have hh := hmargin (fun _ ↦ true)
  simp [label, hammingWeight, totalScore, affineValue, hu] at hh
  linarith

theorem no_numerator_norm_minimum (n : ℕ) (hn : 2 ≤ n)
    (u b : Fin 2 → Fin n → ℝ)
    (hmargin : ∀ x, 1 ≤ label n x * totalScore n u b x) :
    ∃ t : ℝ, 0 < t ∧ normSquare n (numerator n t) < normSquare n u ∧
      (∀ x, 1 ≤ label n x * totalScore n (numerator n t) (slope n t) x) ∧
      (∀ i, 0 < slope n t 0 i) ∧ (∀ i, slope n t 1 i < 0) ∧
      (∑ i : Fin n, -slope n t 1 i < 1) := by
  obtain ⟨t, ht, _, hsmall, hm⟩ := arbitrarily_small_norm n hn (normSquare n u)
    (norm_positive_of_unit_margin n u b hmargin)
  obtain ⟨hp, hneg, hsum⟩ := family_slopes n hn t ht
  exact ⟨t, ht, hsmall, hm, hp, hneg, hsum⟩

#print axioms arbitrarily_small_norm
#print axioms atoms_score
#print axioms no_numerator_norm_minimum

end HeadComplexity.VanishingNumeratorNorm
