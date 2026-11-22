import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.PartialFraction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

set_option linter.style.header false

/-! A projective perturbation compiles strict polynomial predicates in an
arbitrary affine statistic, including mixed-sign weights. This is an auxiliary
upper construction, not the requested worst-case head lower bound. -/
namespace HeadComplexity
open Finset Filter Polynomial
open scoped BigOperators Topology

namespace AffineStatisticPolynomial

private theorem finite_signs_persist {X : Type*} [Finite X]
    (g : ℝ → X → ℝ)
    (hc : ∀ x, ContinuousAt (fun t ↦ g t x) 0)
    (hn : ∀ x, g 0 x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ x, (0 < g t x ↔ 0 < g 0 x) := by
  have hx : ∀ x, ∀ᶠ t in nhds (0 : ℝ), (0 < g t x ↔ 0 < g 0 x) := by
    intro x
    rcases lt_or_gt_of_ne (hn x) with hneg | hpos
    · filter_upwards [hc x (Iio_mem_nhds hneg)] with t ht
      change g t x < 0 at ht
      constructor <;> intro h <;> linarith
    · filter_upwards [hc x (Ioi_mem_nhds hpos)] with t ht
      change 0 < g t x at ht
      exact ⟨fun _ ↦ hpos, fun _ ↦ ht⟩
  have hall := Filter.eventually_all.mpr hx
  change {t : ℝ | ∀ x, (0 < g t x ↔ 0 < g 0 x)} ∈ nhds 0 at hall
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r / 2, by linarith, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  simp only [sub_zero, abs_of_pos (by linarith : 0 < r / 2)]
  linarith

private theorem affine_abs_bound {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (x : Fin n → Bool) :
    |affineValue c a x| ≤ |c| + ∑ i, |a i| := by
  unfold affineValue
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  cases x i <;> simp [boolToReal]

end AffineStatisticPolynomial

/-- Every strict degree-`K` univariate polynomial predicate in any affine
statistic is computable by `K` exact-model heads. The affine weights need not
have coherent signs. The constructed denominators have positive coefficients. -/
theorem computableWithHeadsN_affineStatisticPolynomial {n K : ℕ}
    (c : ℝ) (a : Fin n → ℝ) (P : ℝ[X]) (hdeg : P.natDegree ≤ K)
    (f : (Fin n → Bool) → Bool)
    (hne : ∀ x, P.eval (affineValue c a x) ≠ 0)
    (hsign : ∀ x, (0 < P.eval (affineValue c a x) ↔ f x = true)) :
    computableWithHeadsN n K f := by
  classical
  let D : ℝ → (Fin n → Bool) → ℝ := fun t x ↦ affineValue 1 (fun _ ↦ t) x
  let L := affineValue c a
  let g : ℝ → (Fin n → Bool) → ℝ := fun t x ↦ P.eval (L x / D t x)
  have hD0 (x) : D 0 x = 1 := by simp [D, affineValue]
  have hc (x) : ContinuousAt (fun t ↦ g t x) 0 := by
    apply P.continuous.continuousAt.comp
    apply continuousAt_const.div
    · dsimp [D, affineValue]
      fun_prop
    · rw [hD0]; norm_num
  have hn (x) : g 0 x ≠ 0 := by simpa [g, hD0, L] using hne x
  obtain ⟨δ, hδ, hδsign⟩ := AffineStatisticPolynomial.finite_signs_persist g hc hn
  have hD (x) : 0 < D δ x := affineValue_pos 1 (fun _ ↦ δ) (by norm_num) (fun _ ↦ hδ) x
  have hDone (x) : 1 ≤ D δ x := by
    dsimp [D, affineValue]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦
      mul_nonneg hδ.le (by cases x i <;> simp [boolToReal]))
  let M : ℝ := |c| + ∑ i, |a i|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcM : |c| ≤ M := le_add_of_nonneg_right (by positivity)
  have haM (i) : |a i| ≤ M := by
    have hi : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (a j)) (Finset.mem_univ i)
    dsimp [M]
    linarith [abs_nonneg c]
  let B : ℝ := M + M / δ + 1
  have hBM : M < B := by
    dsimp [B]
    have := div_nonneg hM hδ.le
    linarith
  have hBMδ : M < B * δ := by
    have hid : B * δ = M * δ + M + δ := by dsimp [B]; field_simp
    rw [hid]
    nlinarith [mul_nonneg hM hδ.le]
  obtain ⟨av, bv, τ, hav, hpf⟩ := exists_partialFraction_sign_atoms P B hdeg
  have hb0 (h) : 0 < c + av h := by
    have := hav h
    linarith [neg_abs_le c]
  have hb (h) (i) : 0 < a i + av h * δ := by
    have hh : B * δ < av h * δ := mul_lt_mul_of_pos_right (hav h) hδ
    linarith [neg_abs_le (a i), haM i]
  apply computableWithHeadsN_of_positiveAffineRatios bv
    (fun h _ ↦ bv h * δ) (fun h ↦ c + av h)
    (fun h i ↦ a i + av h * δ) hb0 hb (-τ)
  intro x
  have hLbound : -M ≤ L x := by
    have hh := AffineStatisticPolynomial.affine_abs_bound c a x
    exact (abs_le.mp hh).1
  have ht : -B ≤ L x / D δ x := by
    apply le_trans (neg_le_neg hBM.le)
    apply (le_div_iff₀ (hD x)).mpr
    nlinarith [hDone x]
  have hnum (h) : affineValue (bv h) (fun _ ↦ bv h * δ) x = bv h * D δ x := by
    simpa [D] using affineValue_smul (bv h) 1 (fun _ ↦ δ) x
  have hden (h) : affineValue (c + av h) (fun i ↦ a i + av h * δ) x =
      L x + av h * D δ x := by
    simpa [L, D] using affineValue_linearCombination 0 1 (av h) c 1 a (fun _ ↦ δ) x
  have hratio (h) : affineValue (bv h) (fun _ ↦ bv h * δ) x /
      affineValue (c + av h) (fun i ↦ a i + av h * δ) x =
      bv h / (L x / D δ x + av h) := by
    rw [hnum, hden]
    field_simp [(hD x).ne']
  simp_rw [hratio]
  have hgs : (0 < P.eval (L x / D δ x) ↔ f x = true) := by
    have hh : (0 < P.eval (L x / D δ x) ↔ 0 < P.eval (L x)) := by
      simpa [g, hD0] using hδsign x
    exact hh.trans (hsign x)
  have hp := (hpf (L x / D δ x) ht).trans hgs
  constructor
  · intro h
    exact hp.mp (by linarith)
  · intro h
    have hh := hp.mpr h
    linarith

end HeadComplexity
