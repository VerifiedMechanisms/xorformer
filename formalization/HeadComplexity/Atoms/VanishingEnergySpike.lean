import HeadComplexity.Atoms.HeadEllipticEnergy
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false
noncomputable section

/-! Finite algebra for a sign-preserving spike with vanishing normalized
denominator energy. The accompanying writeup supplies the differentiation
and the full finite-head assembly. No head-count lower bound is asserted. -/
namespace HeadComplexity.VanishingEnergySpike
open scoped BigOperators
open Finset HeadEllipticEnergy

theorem energy_scale {ι : Type*} [Fintype ι] (b v : ι → ℝ) (r : ℝ) :
    energy b (fun i ↦ r * v i) = r^2 * energy b v := by
  unfold energy
  simp_rw [mul_pow]
  have h₁ : (∑ i, b i * (r^2 * (v i)^2)) = r^2 * ∑ i, b i * (v i)^2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have h₂ : (∑ i, b i * (r * v i)) = r * ∑ i, b i * v i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [h₁, h₂]
  ring

theorem energy_cauchy {ι X : Type*} [Fintype ι] [Fintype X]
    (b : ι → ℝ) (S : X → ℝ) (g : X → ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    energy b (fun i ↦ ∑ x, S x * g x i) ≤
      (∑ x, (S x)^2) * ∑ x, energy b (g x) := by
  have hc i := sum_mul_sq_le_sq_mul_sq univ S (fun x ↦ g x i)
  have hd := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) ↦
    mul_le_mul_of_nonneg_left (hc i) (hb i))
  have hz := sum_mul_sq_le_sq_mul_sq univ S (fun x ↦ ∑ i, b i * g x i)
  have hmean : (∑ i, b i * ∑ x, S x * g x i) =
      ∑ x, S x * ∑ i, b i * g x i := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro i _
    ring
  have hdiag : (∑ i, b i * ((∑ x, (S x)^2) * ∑ x, (g x i)^2)) =
      (∑ x, (S x)^2) * ∑ x, ∑ i, b i * (g x i)^2 := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro i _
    ring
  rw [hdiag] at hd
  simp only [energy, hmean, sum_add_distrib, mul_add]
  exact add_le_add hd hz

def angularEnergy {ι X : Type*} [Fintype ι] [Fintype X]
    (b : ι → ℝ) (S : X → ℝ) (g : X → ι → ℝ) : ℝ :=
  (((∑ x, (S x)^2) * ∑ x, energy b (g x)) -
    energy b (fun i ↦ ∑ x, S x * g x i)) / (∑ x, (S x)^2)^2

theorem angularEnergy_bounds {ι X : Type*} [Fintype ι] [Fintype X]
    (b : ι → ℝ) (S : X → ℝ) (g : X → ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hG : 1 ≤ ∑ x, (S x)^2) :
    0 ≤ angularEnergy b S g ∧ angularEnergy b S g ≤ ∑ x, energy b (g x) := by
  have hGpos : 0 < ∑ x, (S x)^2 := by linarith
  have hraw : 0 ≤ ∑ x, energy b (g x) :=
    sum_nonneg fun x _ ↦ energy_nonneg b (g x) hb
  constructor
  · exact div_nonneg (sub_nonneg.mpr (energy_cauchy b S g hb)) (sq_nonneg _)
  · unfold angularEnergy
    apply (div_le_iff₀ (sq_pos_of_pos hGpos)).mpr
    have hm := energy_nonneg b (fun i ↦ ∑ x, S x * g x i) hb
    have hg : (∑ x, (S x)^2) ≤ (∑ x, (S x)^2)^2 := by nlinarith
    have he := mul_le_mul_of_nonneg_right hg hraw
    nlinarith

theorem spike_energy {ι : Type*} [Fintype ι] (x : ι → ℝ) (t s : ℝ)
    (hx : ∀ i, (x i)^2 = x i) (ht : 0 < t) (hs : s^2 = 1)
    (hk : 0 ≤ ∑ i, x i) :
    energy (fun _ ↦ 1/t) (fun i ↦ -s*t^2*x i/(t+∑ j, x j)^2) =
      t^2 * (∑ i, x i) / (t+∑ i, x i)^3 := by
  have htk : t + ∑ i, x i ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hk)
  have hrewrite : (fun i ↦ -s*t^2*x i/(t+∑ j, x j)^2) =
      (fun i ↦ (-s*t^2/(t+∑ j, x j)^2) * x i) := by
    funext i
    ring
  rw [hrewrite, energy_scale]
  have he : energy (fun _ : ι ↦ 1/t) x =
      (∑ i, x i)/t + ((∑ i, x i)/t)^2 := by
    unfold energy
    simp_rw [hx, one_div_mul_eq_div, ← sum_div]
  rw [he]
  field_simp
  nlinarith [hs]

theorem spike_energy_bound (t k : ℝ) (ht : 0 < t) (hk : 1 ≤ k) :
    t^2*k/(t+k)^3 ≤ t^2 := by
  have hp : 0 < t+k := by linarith
  have hsq : k ≤ k^2 := by nlinarith
  have hcube : k ≤ k^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg k)]
  have htk : k ≤ (t+k)^3 := by nlinarith [sq_nonneg t, mul_pos ht (sq_pos_of_pos (by linarith : 0 < k))]
  apply (div_le_iff₀ (pow_pos hp 3)).mpr
  exact mul_le_mul_of_nonneg_left htk (sq_nonneg t)

theorem preserve_sign (y S a ε m t : ℝ) (hy : y^2 = 1)
    (hm : 0 < m) (hS : m ≤ y*S) (hε : 0 < ε)
    (ha : |a| ≤ t) (ht : t ≤ ε*m/2) :
    0 < y*(a+ε*S) := by
  have habs : |y| = 1 := by nlinarith [sq_abs y, abs_nonneg y]
  have hlower : -t ≤ y*a := by
    have hab : |y*a| ≤ t := by simpa [abs_mul, habs] using ha
    exact (abs_le.mp hab).1
  have hs := mul_le_mul_of_nonneg_left hS hε.le
  have hp := mul_pos hε hm
  nlinarith

theorem origin_norm_bound {X : Type*} [Fintype X] (S : X → ℝ) (o : X)
    (h : 1 ≤ (S o)^2) : 1 ≤ ∑ x, (S x)^2 := by
  exact h.trans (single_le_sum (fun x _ ↦ sq_nonneg (S x)) (mem_univ o))

theorem small_scale (K N m η : ℝ) (hK : 0 ≤ K) (hN : 0 < N)
    (hm : 0 < m) (hη : 0 < η) :
    ∃ ε t : ℝ, 0 < ε ∧ 0 < t ∧ t ≤ ε*m/2 ∧
      N*t^2+ε^2*K < η := by
  let q := η / (K+N)
  have hq : 0 < q := div_pos hη (by linarith)
  let ε := min q 1 / 2
  have hε : 0 < ε := by dsimp [ε]; exact div_pos (lt_min hq zero_lt_one) (by norm_num)
  have heq : ε ≤ q/2 := by dsimp [ε]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he1 : ε ≤ 1/2 := by dsimp [ε]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have he : ε^2 < η/(K+N) := by
    change ε^2 < q
    nlinarith
  let t := ε*m/(2*(1+m))
  have ht : 0 < t := by dsimp [t]; positivity
  have htm : t ≤ ε*m/2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2*(1+m))).mpr
    nlinarith [mul_pos hε hm]
  have hte : t ≤ ε := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2*(1+m))).mpr
    nlinarith [mul_pos hε hm]
  refine ⟨ε, t, hε, ht, htm, ?_⟩
  have he' := (lt_div_iff₀ (show 0 < K+N by linarith)).mp he
  have ht2 : t^2 ≤ ε^2 := by nlinarith
  have := mul_le_mul_of_nonneg_left ht2 hN.le
  nlinarith

def spikeAtom {n : ℕ} (s t : ℝ) (ht : 0 < t) : FracAtom n :=
  FracAtom.ofPositiveAffineRatio (s*t) (fun _ ↦ 0) t (fun _ ↦ 1) ht (by intro i; norm_num)

theorem spikeAtom_eval {n : ℕ} (s t : ℝ) (ht : 0 < t) (x : Fin n → Bool) :
    (spikeAtom s t ht).eval x = s*t/(t+∑ i, boolToReal (x i)) := by
  simp [spikeAtom, FracAtom.ofPositiveAffineRatio_eval, affineValue]

end HeadComplexity.VanishingEnergySpike
