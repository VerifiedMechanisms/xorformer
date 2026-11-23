import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

/-! Algebraic identities for the denominator-parameter elliptic operator.
The analytic differentiation and its relation to normalized head tables are
spelled out in the accompanying writeup. This file proves no sign count. -/
namespace HeadComplexity.HeadEllipticEnergy
open scoped BigOperators
open Finset

def energy {ι : Type*} [Fintype ι] (b v : ι → ℝ) : ℝ :=
  (∑ i, b i * (v i)^2) + (∑ i, b i * v i)^2

theorem energy_nonneg {ι : Type*} [Fintype ι] (b v : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) : 0 ≤ energy b v := by
  exact add_nonneg (sum_nonneg fun i _ ↦ mul_nonneg (hb i) (sq_nonneg _)) (sq_nonneg _)

theorem boolean_spherical_identity {ι : Type*} [Fintype ι] (b x : ι → ℝ)
    (hx : ∀ i, (x i)^2 = x i) (hD : 1 + ∑ i, b i*x i ≠ 0) :
    energy b (fun i ↦ x i / (1 + ∑ j, b j*x j)) =
      (∑ i, b i*x i) / (1 + ∑ j, b j*x j) := by
  unfold energy
  simp_rw [div_pow, hx, ← mul_div_assoc]
  rw [← sum_div, ← sum_div]
  field_simp

theorem scalar_variance_identity {X : Type*} [Fintype X] (p z : X → ℝ)
    (hp : ∑ x, p x = 1) :
    (∑ x, p x * (z x - ∑ y, p y*z y)^2) =
      (∑ x, p x*(z x)^2) - (∑ x, p x*z x)^2 := by
  let m := ∑ x, p x*z x
  have hterm : ∀ x, p x*(z x-m)^2 =
      p x*(z x)^2 - 2*m*(p x*z x) + m^2*p x := by intro x; ring
  change (∑ x, p x*(z x-m)^2) = _
  simp_rw [hterm]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hp]
  change (∑ x, p x*(z x)^2) - 2*m*m + m^2*1 = _
  dsimp [m]
  ring

theorem weighted_energy_variance {ι X : Type*} [Fintype ι] [Fintype X]
    (b : ι → ℝ) (p : X → ℝ) (v : X → ι → ℝ) (hp : ∑ x, p x = 1) :
    (∑ x, p x * energy b (fun i ↦ v x i - ∑ y, p y*v y i)) =
      (∑ x, p x * energy b (v x)) - energy b (fun i ↦ ∑ x, p x*v x i) := by
  let m : ι → ℝ := fun i ↦ ∑ x, p x*v x i
  have hmean : (∑ x, p x * ∑ i, b i*v x i) = ∑ i, b i*m i := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp_rw [← mul_assoc, mul_comm (p _) (b i), mul_assoc]
    rw [← mul_sum]
  have hv i := scalar_variance_identity p (fun x ↦ v x i) hp
  have hz := scalar_variance_identity p (fun x ↦ ∑ i, b i*v x i) hp
  rw [hmean] at hz
  have hdiff x : (∑ i, b i*(v x i-m i)) =
      (∑ i, b i*v x i) - ∑ i, b i*m i := by simp [mul_sub, sum_sub_distrib]
  change (∑ x, p x * energy b (fun i ↦ v x i-m i)) = _
  simp only [energy, mul_add, sum_add_distrib, hdiff]
  rw [hz]
  have hdiag : (∑ x, p x * ∑ i, b i*(v x i-m i)^2) =
      (∑ x, p x * ∑ i, b i*(v x i)^2) - ∑ i, b i*(m i)^2 := by
    simp_rw [mul_sum]
    rw [sum_comm, sum_comm (f := fun x i ↦ p x * (b i * (v x i)^2))]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp_rw [← mul_assoc, mul_comm (p _) (b i), mul_assoc]
    rw [← mul_sum, ← mul_sum, ← mul_sub]
    exact congrArg (fun z ↦ b i*z) (hv i)
  rw [hdiag]
  dsimp [m]
  ring

theorem completed_spherical_variance {ι : Type*} [Fintype ι] (b m : ι → ℝ)
    (hB : 1 + ∑ i, b i ≠ 0) :
    (∑ i, b i*m i) - energy b m =
      (∑ i, b i) / (4*(1+∑ i, b i)) -
        energy b (fun i ↦ m i - 1/(2*(1+∑ j, b j))) := by
  let c : ℝ := 1/(2*(1+∑ j, b j))
  have hs : (∑ i, b i*(m i-c)) = (∑ i, b i*m i)-c*(∑ i, b i) := by
    simp_rw [mul_sub, mul_comm (b _) c]
    rw [sum_sub_distrib, ← mul_sum]
  have hsq : (∑ i, b i*(m i-c)^2) =
      (∑ i, b i*(m i)^2)-2*c*(∑ i, b i*m i)+c^2*(∑ i, b i) := by
    have ht : ∀ i, b i*(m i-c)^2 = b i*(m i)^2 - 2*c*(b i*m i) + c^2*b i := by
      intro i; ring
    simp_rw [ht]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  change (∑ i, b i*m i) - energy b m = _ - energy b (fun i ↦ m i-c)
  simp only [energy, hs, hsq]
  dsimp [c]
  field_simp
  ring

theorem spherical_variance_upper {ι : Type*} [Fintype ι] (b m : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) :
    (∑ i, b i*m i) - energy b m ≤ (∑ i, b i)/(4*(1+∑ i, b i)) := by
  have hB : 1 + ∑ i, b i ≠ 0 := by
    have : 0 ≤ ∑ i, b i := sum_nonneg fun i _ ↦ hb i
    linarith
  rw [completed_spherical_variance b m hB]
  exact sub_le_self _ (energy_nonneg b _ hb)

theorem radius_lt_quarter (B : ℝ) (hB : 0 ≤ B) : B/(4*(1+B)) < 1/4 := by
  have hp : 0 < 4*(1+B) := by linarith
  apply (div_lt_iff₀ hp).mpr
  linarith

theorem spherical_variance_bounds {ι X : Type*} [Fintype ι] [Fintype X]
    (b : ι → ℝ) (p : X → ℝ) (v : X → ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hv : ∀ x, energy b (v x) = ∑ i, b i*v x i) :
    let m : ι → ℝ := fun i ↦ ∑ x, p x*v x i
    0 ≤ (∑ i, b i*m i) - energy b m ∧
      (∑ i, b i*m i) - energy b m ≤ (∑ i, b i)/(4*(1+∑ i, b i)) := by
  dsimp only
  constructor
  · have hmean : (∑ x, p x * energy b (v x)) =
        ∑ i, b i * ∑ x, p x*v x i := by
      simp_rw [hv, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro x _
      ring
    rw [← hmean, ← weighted_energy_variance b p v hp1]
    exact sum_nonneg fun x _ ↦ mul_nonneg (hp x) (energy_nonneg b _ hb)
  · exact spherical_variance_upper b _ hb

theorem elliptic_scalar_identity (A s : ℝ) (hD : 1 + s ≠ 0) :
    2*A*(s+s^2)/(1+s)^3 - 2*A*s/(1+s)^2 = 0 := by
  field_simp
  ring

end HeadComplexity.HeadEllipticEnergy
