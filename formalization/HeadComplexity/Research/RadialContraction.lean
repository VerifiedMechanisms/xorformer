import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-! Finite radial contraction can lose labels even with reselected affine
numerators. This is an auxiliary obstruction, not a worst-case lower bound. -/
namespace HeadComplexity.RadialContraction
abbrev Cube := Fin 4 → Bool
noncomputable def firstDirection : Fin 4 → ℝ := ![6, 7, 2, 5]
noncomputable def secondDirection : Fin 4 → ℝ := ![2, 2, 1, 1]
noncomputable def d₁ (t : ℝ) (x : Cube) : ℝ :=
  affineValue 1 (fun i ↦ t * firstDirection i) x
noncomputable def d₂ (t : ℝ) (x : Cube) : ℝ :=
  affineValue 1 (fun i ↦ t * secondDirection i) x
noncomputable def score (t c a₀ : ℝ) (a : Fin 4 → ℝ)
    (b₀ : ℝ) (b : Fin 4 → ℝ) (x : Cube) : ℝ :=
  c + affineValue a₀ a x / d₁ t x + affineValue b₀ b x / d₂ t x
noncomputable def cleared (t c a₀ : ℝ) (a : Fin 4 → ℝ)
    (b₀ : ℝ) (b : Fin 4 → ℝ) (x : Cube) : ℝ :=
  c * d₁ t x * d₂ t x + affineValue a₀ a x * d₂ t x +
    affineValue b₀ b x * d₁ t x

def target (x : Cube) : Bool :=
  (x 0 && x 1 && !x 2 && !x 3) ||
  (x 0 && !x 1 && x 2 && !x 3) ||
  (!x 1 && x 2 && x 3) || (x 0 && x 1 && x 2 && x 3)
def sample : Fin 9 → Cube :=
  ![![true,false,false,false], ![false,true,false,false],
    ![true,true,false,false], ![true,false,true,false],
    ![true,true,true,false], ![true,false,false,true],
    ![true,true,false,true], ![false,false,true,true],
    ![true,true,true,true]]
noncomputable def label : Fin 9 → ℝ := ![-1,-1,1,1,-1,-1,-1,1,1]
noncomputable def weight (t : ℝ) : Fin 9 → ℝ :=
  ![-130*t^3 + 343*t^2 + 215*t + 48,
    -(2*t+5)*(5*t-1)*(7*t+4), -12*(t-2)*(10*t^2+11*t+7),
    -50*t^3+157*t^2+269*t+44, -46*t^3+139*t^2+239*t+144,
    -10*t^3-199*t^2+25*t+16, -10*t^3+169*t^2+65*t+84,
    -(2*t+5)*(5*t-1)*(7*t+4), 5*(2*t^3+23*t^2+19*t+16)]

theorem denominator_pos {t : ℝ} (ht : 0 < t) (x : Cube) :
    0 < d₁ t x ∧ 0 < d₂ t x := by
  constructor
  · apply affineValue_pos 1 _ (by norm_num) _ x
    intro i
    fin_cases i <;> norm_num [firstDirection] <;> positivity
  · apply affineValue_pos 1 _ (by norm_num) _ x
    intro i
    fin_cases i <;> norm_num [secondDirection] <;> positivity

theorem weight_pos {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 10)
    (i : Fin 9) : 0 < weight t i := by
  have hs : 0 ≤ t^2 := sq_nonneg t
  have hq : t^2 ≤ 1 / 100 := by nlinarith
  have hc : 0 ≤ t^3 := by positivity
  have hc' : t^3 ≤ 1 / 1000 := by
    have hm := mul_le_mul_of_nonneg_left hq (le_of_lt ht)
    nlinarith
  fin_cases i <;> norm_num [weight] <;> nlinarith

theorem annihilation (t c a₀ : ℝ) (a : Fin 4 → ℝ)
    (b₀ : ℝ) (b : Fin 4 → ℝ) :
    ∑ i : Fin 9, weight t i * label i * cleared t c a₀ a b₀ b (sample i) = 0 := by
  norm_num [Fin.sum_univ_succ, weight, label, cleared, d₁, d₂,
    affineValue, firstDirection, secondDirection, sample, boolToReal]
  ring

theorem cleared_eq {t : ℝ} (ht : 0 < t) (c a₀ : ℝ) (a : Fin 4 → ℝ)
    (b₀ : ℝ) (b : Fin 4 → ℝ) (x : Cube) :
    cleared t c a₀ a b₀ b x = score t c a₀ a b₀ b x * (d₁ t x * d₂ t x) := by
  obtain ⟨h₁,h₂⟩ := denominator_pos ht x
  unfold cleared score
  field_simp

theorem not_small_scale_represents_target {t : ℝ} (ht : 0 < t)
    (ht' : t ≤ 1 / 10) (c a₀ : ℝ) (a : Fin 4 → ℝ)
    (b₀ : ℝ) (b : Fin 4 → ℝ) :
    ¬ (∀ x : Cube, 0 < score t c a₀ a b₀ b x ↔ target x = true) := by
  intro h
  have hn (i : Fin 9) : 0 ≤ label i * cleared t c a₀ a b₀ b (sample i) := by
    rw [cleared_eq ht]
    have hd := mul_pos (denominator_pos ht (sample i)).1
      (denominator_pos ht (sample i)).2
    have hh := h (sample i)
    fin_cases i <;> norm_num [label, target, sample] at hh hd ⊢
    all_goals first
      | exact le_of_lt (mul_pos hh hd)
      | nlinarith [mul_nonpos_of_nonpos_of_nonneg hh (le_of_lt hd)]
  have hp : 0 < label 2 * cleared t c a₀ a b₀ b (sample 2) := by
    rw [cleared_eq ht]
    have hh : 0 < score t c a₀ a b₀ b (sample 2) :=
      (h (sample 2)).mpr (by norm_num [target, sample])
    norm_num [label]
    exact mul_pos hh (mul_pos (denominator_pos ht (sample 2)).1
      (denominator_pos ht (sample 2)).2)
  have hsum : 0 < ∑ i : Fin 9, weight t i * label i *
      cleared t c a₀ a b₀ b (sample i) := by
    apply Finset.sum_pos'
    · intro i _
      simpa only [mul_assoc] using mul_nonneg (le_of_lt (weight_pos ht ht' i)) (hn i)
    · exact ⟨2, Finset.mem_univ _, by
        simpa only [mul_assoc] using mul_pos (weight_pos ht ht' 2) hp⟩
  rw [annihilation] at hsum
  exact (lt_irrefl 0) hsum

noncomputable def numeratorConstants : Fin 2 → ℝ := ![0,0]
noncomputable def numeratorSlopes : Fin 2 → Fin 4 → ℝ :=
  ![![0,-1008,0,1350], ![42,398,22,-464]]
noncomputable def denominatorSlopes : Fin 2 → Fin 4 → ℝ :=
  ![firstDirection,secondDirection]

theorem target_computableWith_two_heads : computableWithHeadsN 4 2 target := by
  apply computableWithHeadsN_of_positiveAffineRatios
    numeratorConstants numeratorSlopes (fun _ ↦ 1) denominatorSlopes
    (fun _ ↦ by norm_num) (by
      intro h i
      fin_cases h <;> fin_cases i <;>
        norm_num [denominatorSlopes, firstDirection, secondDirection]) (-15)
  intro x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [Fin.sum_univ_succ, affineValue, numeratorConstants, numeratorSlopes,
      denominatorSlopes, firstDirection, secondDirection, target, boolToReal,
      h0, h1, h2, h3]

#print axioms target_computableWith_two_heads
#print axioms not_small_scale_represents_target
end HeadComplexity.RadialContraction
