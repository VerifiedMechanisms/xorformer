import HeadComplexity.Research.NonnegativeHeadCone
import HeadComplexity.Research.UnitGapBasisGeometry
import HeadComplexity.Research.OriginalMarginCapacity

set_option linter.style.header false
set_option linter.style.longLine false

noncomputable section
namespace HeadComplexity.SelectedNegativeControl
open Finset
open scoped BigOperators

/-- Any selected set of downward neighbors suffices. The omitted coordinates
remain fixed, and no maximizing-vertex premise is required. -/
theorem affine_corner_subset_ratio_le {I : Type*} [Fintype I]
    (s : Finset I) (a₀ b₀ : ℝ) (a beta : I → ℝ)
    (hb₀ : 0 < b₀) (hbeta : ∀ i, 0 ≤ beta i)
    (ha : ∀ t : Finset I, 0 ≤ a₀ + ∑ i ∈ t, a i)
    (hs : 2 ≤ s.card) :
    (a₀ + ∑ i, a i) / (b₀ + ∑ i, beta i) ≤
      (∑ i ∈ s, ((a₀ + ∑ j, a j) - a i) / ((b₀ + ∑ j, beta j) - beta i)) /
        ((s.card : ℝ) - 1) := by
  classical
  let A := a₀ + ∑ i, a i
  let B := b₀ + ∑ i, beta i
  have hB : 0 < B := add_pos_of_pos_of_nonneg hb₀ (sum_nonneg fun i _ => hbeta i)
  have hcomp : a₀ + ∑ i ∈ univ \ s, a i = A - ∑ i ∈ s, a i := by
    have hh := sum_sdiff (subset_univ s) (f := a)
    dsimp [A]
    linarith
  have ha0 : 0 ≤ A - ∑ i ∈ s, a i := by rw [← hcomp]; exact ha _
  have ha1 (i : I) : 0 ≤ A - a i := by
    have hh := sum_erase_add univ a (mem_univ i)
    have hp := ha (univ.erase i)
    dsimp [A]
    linarith
  have hb1 (i : I) : 0 < B - beta i ∧ B - beta i ≤ B := by
    have hh := sum_erase_add univ beta (mem_univ i)
    have hp : 0 ≤ ∑ j ∈ univ.erase i, beta j := sum_nonneg fun j _ => hbeta j
    have hi := hbeta i
    dsimp [B]
    constructor <;> linarith
  have hr : 0 < (s.card : ℝ) - 1 := by
    have hsR : (2 : ℝ) ≤ s.card := by exact_mod_cast hs
    linarith
  have hh : (∑ i ∈ s, (A - a i)) / B ≤
      ∑ i ∈ s, (A - a i) / (B - beta i) := by
    rw [sum_div]
    exact sum_le_sum fun i _ => div_le_div_of_nonneg_left (ha1 i) (hb1 i).1 (hb1 i).2
  have hid : (∑ i ∈ s, (A - a i)) / B =
      (A / B) * ((s.card : ℝ) - 1) + (A - ∑ i ∈ s, a i) / B := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [hid] at hh
  have hnonneg := div_nonneg ha0 hB.le
  change A / B ≤ (∑ i ∈ s, (A - a i) / (B - beta i)) / ((s.card : ℝ) - 1)
  apply (le_div_iff₀ hr).mpr
  linarith

theorem affineValue_update_false {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (x : Fin n → Bool) (i : Fin n) (hi : x i = true) :
    affineValue c a (Function.update x i false) = affineValue c a x - a i := by
  have ht : ∀ j, a j * boolToReal (Function.update x i false j) =
      a j * boolToReal (x j) - if j = i then a i else 0 := by
    intro j
    by_cases hji : j = i
    · subst j; simp [hi, boolToReal]
    · simp [hji]
  simp only [affineValue, ht, sum_sub_distrib]
  simp
  ring

theorem two_neighbor_ratio_le (A B A₁ A₂ A₁₂ B₁ B₂ : ℝ)
    (hB : 0 < B) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₁₂ : 0 ≤ A₁₂)
    (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (h₁ : B₁ ≤ B) (h₂ : B₂ ≤ B)
    (hA : A₁ + A₂ = A + A₁₂) : A / B ≤ A₁ / B₁ + A₂ / B₂ := by
  calc
    A / B ≤ (A₁ + A₂) / B := div_le_div_of_nonneg_right (by linarith) hB.le
    _ = A₁ / B + A₂ / B := add_div _ _ _
    _ ≤ A₁ / B₁ + A₂ / B₂ := add_le_add
      (div_le_div_of_nonneg_left hA₁ hB₁ h₁)
      (div_le_div_of_nonneg_left hA₂ hB₂ h₂)

theorem affine_two_down_ratio_le {n : ℕ} (a₀ b₀ : ℝ) (a b : Fin n → ℝ)
    (hA : ∀ x, 0 ≤ affineValue a₀ a x) (hB : ∀ x, 0 < affineValue b₀ b x)
    (hb : ∀ i, 0 ≤ b i) (x : Fin n → Bool) (i j : Fin n)
    (hij : i ≠ j) (hi : x i = true) (hj : x j = true) :
    affineValue a₀ a x / affineValue b₀ b x ≤
      affineValue a₀ a (Function.update x i false) / affineValue b₀ b (Function.update x i false) +
      affineValue a₀ a (Function.update x j false) / affineValue b₀ b (Function.update x j false) := by
  have hj' : Function.update x i false j = true := by simp [hij.symm, hj]
  apply two_neighbor_ratio_le _ _ _ _
    (affineValue a₀ a (Function.update (Function.update x i false) j false)) _ _
    (hB x) (hA _) (hA _) (hA _) (hB _) (hB _)
  · rw [affineValue_update_false _ _ _ _ hi]; exact sub_le_self _ (hb i)
  · rw [affineValue_update_false _ _ _ _ hj]; exact sub_le_self _ (hb j)
  · rw [affineValue_update_false _ _ _ _ hj', affineValue_update_false _ _ _ _ hi,
      affineValue_update_false _ _ _ _ hj]
    ring

theorem affine_two_up_ratio_le {n : ℕ} (a₀ b₀ : ℝ) (a b : Fin n → ℝ)
    (hA : ∀ x, 0 ≤ affineValue a₀ a x) (hB : ∀ x, 0 < affineValue b₀ b x)
    (hb : ∀ i, b i ≤ 0) (x : Fin n → Bool) (i j : Fin n)
    (hij : i ≠ j) (hi : x i = false) (hj : x j = false) :
    affineValue a₀ a x / affineValue b₀ b x ≤
      affineValue a₀ a (Function.update x i true) / affineValue b₀ b (Function.update x i true) +
      affineValue a₀ a (Function.update x j true) / affineValue b₀ b (Function.update x j true) := by
  have hj' : Function.update x i true j = false := by simp [hij.symm, hj]
  apply two_neighbor_ratio_le _ _ _ _
    (affineValue a₀ a (Function.update (Function.update x i true) j true)) _ _
    (hB x) (hA _) (hA _) (hA _) (hB _) (hB _)
  · rw [UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hi]; exact add_le_of_nonpos_right (hb i)
  · rw [UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hj]; exact add_le_of_nonpos_right (hb j)
  · rw [UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hj',
      UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hi,
      UnitGapBasisGeometry.affineValue_update_true _ _ _ _ hj]
    ring

/-- Four fixed observations control every nonnegative original head. The
selected observations depend on the vertex, not on the head parameters. -/
theorem original_four_neighbors_le {n : ℕ} (φ : FracAtom n)
    (hφ : ∀ x, 0 ≤ φ.eval x) (x : Fin n → Bool) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hi : x i = true) (hj : x j = true) (hk : x k = false) (hl : x l = false) :
    φ.eval x ≤ φ.eval (Function.update x i false) + φ.eval (Function.update x j false) +
      φ.eval (Function.update x k true) + φ.eval (Function.update x l true) := by
  let A := OriginalMarginCapacity.numeratorCoefficients φ
  let B := OriginalMarginCapacity.denominatorCoefficients φ
  let a := fun i => A (some i)
  let b := fun i => B (some i)
  have hAc (y : Fin n → Bool) : affineValue (A none) a y =
      CoefficientOrderChart.affineValue A y := by
    simp only [affineValue, CoefficientOrderChart.affineValue, a, mul_comm]
  have hBc (y : Fin n → Bool) : affineValue (B none) b y =
      CoefficientOrderChart.affineValue B y := by
    simp only [affineValue, CoefficientOrderChart.affineValue, b, mul_comm]
  have he (y : Fin n → Bool) : affineValue (A none) a y / affineValue (B none) b y = φ.eval y := by
    rw [hAc, hBc]
    exact OriginalMarginCapacity.affineRatio_eq_eval φ y
  have hB (y : Fin n → Bool) : 0 < affineValue (B none) b y := by
    rw [hBc, OriginalMarginCapacity.affineValue_denominatorCoefficients]
    exact φ.denom_pos y
  have hA (y : Fin n → Bool) : 0 ≤ affineValue (A none) a y := by
    have hp := hφ y
    rw [← he y] at hp
    have hh := mul_nonneg hp (hB y).le
    rwa [div_mul_cancel₀ _ (hB y).ne'] at hh
  by_cases halpha : 1 ≤ φ.α
  · have hb (r : Fin n) : 0 ≤ b r := by
      exact mul_nonneg (φ.hρ r).le (sub_nonneg.mpr halpha)
    have hh := affine_two_down_ratio_le (A none) (B none) a b hA hB hb x i j hij hi hj
    simp only [he] at hh
    linarith [hφ (Function.update x k true), hφ (Function.update x l true)]
  · have hb (r : Fin n) : b r ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (φ.hρ r).le (sub_nonpos.mpr (le_of_not_ge halpha))
    have hh := affine_two_up_ratio_le (A none) (B none) a b hA hB hb x k l hkl hk hl
    simp only [he] at hh
    linarith [hφ (Function.update x i false), hφ (Function.update x j false)]

/-- The same four observations work simultaneously for an arbitrary family
of nonnegative original heads, regardless of their orientations. -/
theorem sum_four_neighbors_le {n H : ℕ} (φ : Fin H → FracAtom n)
    (hφ : ∀ h x, 0 ≤ (φ h).eval x) (x : Fin n → Bool) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hi : x i = true) (hj : x j = true) (hk : x k = false) (hl : x l = false) :
    (∑ h, (φ h).eval x) ≤
      (∑ h, (φ h).eval (Function.update x i false)) +
      (∑ h, (φ h).eval (Function.update x j false)) +
      (∑ h, (φ h).eval (Function.update x k true)) +
      (∑ h, (φ h).eval (Function.update x l true)) := by
  simpa only [sum_add_distrib] using
    (sum_le_sum fun h (_ : h ∈ (univ : Finset (Fin H))) =>
      original_four_neighbors_le (φ h) (hφ h) x i j k l hij hkl hi hj hk hl)

/-- Uniform negative observations control the total positive score on every
vertex having two negative observations in each direction. This is a value
bound only; it does not give a quantitative strict-label gap. -/
theorem total_le_four_of_observations {n H : ℕ} (φ : Fin H → FracAtom n)
    (hφ : ∀ h x, 0 ≤ (φ h).eval x) (Z : Set (Fin n → Bool)) (L : ℝ)
    (hZ : ∀ y ∈ Z, (∑ h, (φ h).eval y) ≤ L)
    (x : Fin n → Bool) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hi : x i = true) (hj : x j = true) (hk : x k = false) (hl : x l = false)
    (hZi : Function.update x i false ∈ Z) (hZj : Function.update x j false ∈ Z)
    (hZk : Function.update x k true ∈ Z) (hZl : Function.update x l true ∈ Z) :
    (∑ h, (φ h).eval x) ≤ 4 * L := by
  have hh := sum_four_neighbors_le φ hφ x i j k l hij hkl hi hj hk hl
  linarith [hZ _ hZi, hZ _ hZj, hZ _ hZk, hZ _ hZl]

end HeadComplexity.SelectedNegativeControl
