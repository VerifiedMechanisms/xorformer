import HeadComplexity.Research.WeightedNormalizedCounting

set_option linter.style.header false

/-!
Elementary finite mass estimates used by the written Cayley--Bacharach
configuration argument. The geometric Hilbert-function window inequality is an
explicit hypothesis here; this file does not formalize that geometric theorem
or assert that Boolean projection moments are ordinary moments.
-/

noncomputable section
namespace HeadComplexity.CayleyBacharachWindowMass
open Finset
open scoped BigOperators

/-- Disjoint windows, each of mass at least `m`, force total mass at least `K*m`. -/
theorem disjoint_windows_lower (a : ℕ → ℝ) (L K : ℕ) (m : ℝ)
    (hwindow : ∀ j < K, m ≤ ∑ i ∈ range L, a (j * L + i)) :
    (K : ℝ) * m ≤ ∑ i ∈ range (K * L), a i := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hprev := ih (fun j hj ↦ hwindow j (Nat.lt_succ_of_lt hj))
    have hlast := hwindow K (Nat.lt_succ_self K)
    rw [Nat.succ_mul, sum_range_add]
    push_cast
    nlinarith

/-- A prefix of a nonnegative sequence has no more mass than a longer prefix. -/
theorem prefix_mass_mono (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {U T : ℕ} (hUT : U ≤ T) :
    (∑ i ∈ range U, a i) ≤ ∑ i ∈ range T, a i := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono hUT)
  exact fun i _ _ ↦ ha i

/-- The exact integer number of disjoint windows yields the compression bound. -/
theorem window_mass_mul_floor_le (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (T L : ℕ) (m : ℝ)
    (hwindow : ∀ j, j + L ≤ T → m ≤ ∑ i ∈ range L, a (j + i)) :
    ((T / L : ℕ) : ℝ) * m ≤ ∑ i ∈ range T, a i := by
  have hblock : ∀ j < T / L, m ≤ ∑ i ∈ range L, a (j * L + i) := by
    intro j hj
    apply hwindow
    calc
      j * L + L = (j + 1) * L := by ring
      _ ≤ (T / L) * L := Nat.mul_le_mul_right L (by omega)
      _ ≤ T := Nat.div_mul_le_self T L
  exact (disjoint_windows_lower a L (T / L) m hblock).trans
    (prefix_mass_mono a ha (Nat.div_mul_le_self T L))

/-- Division form of the exact window bound. -/
theorem window_mass_le_div_floor (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (T L : ℕ) (hL : 0 < L) (hLT : L ≤ T) (m : ℝ)
    (hwindow : ∀ j, j + L ≤ T → m ≤ ∑ i ∈ range L, a (j + i)) :
    m ≤ (∑ i ∈ range T, a i) / ((T / L : ℕ) : ℝ) := by
  have hk : 0 < T / L := Nat.div_pos hLT hL
  have hkR : (0 : ℝ) < (T / L : ℕ) := by exact_mod_cast hk
  apply (le_div_iff₀ hkR).mpr
  simpa [mul_comm] using window_mass_mul_floor_le a ha T L m hwindow

/-- The integer floor costs at most a factor of two when one window fits. -/
theorem half_ratio_le_floor (T L : ℕ) (hL : 0 < L) (hLT : L ≤ T) :
    (T : ℝ) ≤ 2 * ((T / L : ℕ) : ℝ) * L := by
  have hk : 1 ≤ T / L := Nat.div_pos hLT hL
  have hrem : T % L < L := Nat.mod_lt T hL
  have hdiv : T / L * L + T % L = T := by simpa [mul_comm] using Nat.div_add_mod T L
  have hLmul : L ≤ T / L * L := by
    simpa using Nat.mul_le_mul_right L hk
  have hNat : T ≤ 2 * (T / L * L) := by omega
  have hReal : (T : ℝ) ≤ 2 * ((T / L : ℕ) : ℝ) * L := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
      (show (T : ℝ) ≤ ((2 * (T / L * L) : ℕ) : ℝ) by exact_mod_cast hNat)
  exact hReal

/-- A convenient real bound for subsequent asymptotic dimension estimates. -/
theorem window_mass_le_twice_ratio (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (T L : ℕ) (hL : 0 < L) (hLT : L ≤ T) (m : ℝ) (hm : 0 ≤ m)
    (hwindow : ∀ j, j + L ≤ T → m ≤ ∑ i ∈ range L, a (j + i)) :
    m ≤ 2 * L * (∑ i ∈ range T, a i) / T := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le hL hLT)
  have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hfloor := window_mass_mul_floor_le a ha T L m hwindow
  have hratio := half_ratio_le_floor T L hL hLT
  have hmul := mul_le_mul_of_nonneg_right hratio hm
  have hbound := mul_le_mul_of_nonneg_left hfloor (by positivity : (0 : ℝ) ≤ 2 * L)
  apply (le_div_iff₀ hT).mpr
  nlinarith

end HeadComplexity.CayleyBacharachWindowMass
