import HeadComplexity.Research.SelectedNegativeControl
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.FracAtomSymmetry

set_option linter.style.header false
set_option linter.style.longLine false

noncomputable section
namespace HeadComplexity.NonnegativePointApproximation
open Finset RelativeMarginQuantifiers
open scoped BigOperators

/-- A sum of nonnegative genuine heads, with nonnegative bias, cannot
uniformly approximate a mixed point to error below one fifth. -/
theorem point_error_ge_one_fifth {n H : ℕ} (φ : Fin H → FracAtom n)
    (bias ε : ℝ) (hbias : 0 ≤ bias) (hφ : ∀ h x, 0 ≤ (φ h).eval x)
    (v : Fin n → Bool) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hi : v i = true) (hj : v j = true) (hk : v k = false) (hl : v l = false)
    (happrox : ∀ x, |score φ bias x - (if x = v then 1 else 0)| ≤ ε) :
    (1 : ℝ) / 5 ≤ ε := by
  classical
  have hdi : Function.update v i false ≠ v := by
    intro he
    have hh := congrFun he i
    simp [hi] at hh
  have hdj : Function.update v j false ≠ v := by
    intro he
    have hh := congrFun he j
    simp [hj] at hh
  have huk : Function.update v k true ≠ v := by
    intro he
    have hh := congrFun he k
    simp [hk] at hh
  have hul : Function.update v l true ≠ v := by
    intro he
    have hh := congrFun he l
    simp [hl] at hh
  have hv := (abs_le.mp (happrox v)).1
  have hd₁ := (abs_le.mp (happrox (Function.update v i false))).2
  have hd₂ := (abs_le.mp (happrox (Function.update v j false))).2
  have hu₁ := (abs_le.mp (happrox (Function.update v k true))).2
  have hu₂ := (abs_le.mp (happrox (Function.update v l true))).2
  simp only [ite_eq_right hdi, ite_eq_right hdj, ite_eq_right huk, ite_eq_right hul,
    ite_true,
    sub_zero, score] at hv hd₁ hd₂ hu₁ hu₂
  have hh := SelectedNegativeControl.sum_four_neighbors_le φ hφ v i j k l
    hij hkl hi hj hk hl
  linarith

def mixedVertex : Fin 4 → Bool := ![true, true, false, false]

def positiveFactor : FracAtom 4 :=
  FracAtom.ofPositiveAffineRatio 1 (fun _ => 0) 1
    ![1/100, 1/100, 100, 100] (by norm_num) (by intro i; fin_cases i <;> norm_num)

def negativeFactor : FracAtom 4 :=
  (FracAtom.ofPositiveAffineRatio 1 (fun _ => 0) 1
    ![100, 100, 1/100, 1/100] (by norm_num)
    (by intro i; fin_cases i <;> norm_num)).flip

def mixedProduct (x : Fin 4 → Bool) : ℝ :=
  positiveFactor.eval x * negativeFactor.eval x

theorem mixedProduct_formula (x : Fin 4 → Bool) :
    mixedProduct x =
      1 / (1 + boolToReal (x 0)/100 + boolToReal (x 1)/100 +
        100*boolToReal (x 2) + 100*boolToReal (x 3)) *
      (1 / (1 + 100*boolToReal (!(x 0)) + 100*boolToReal (!(x 1)) +
        boolToReal (!(x 2))/100 + boolToReal (!(x 3))/100)) := by
  simp [mixedProduct, positiveFactor, negativeFactor, FracAtom.ofPositiveAffineRatio_eval,
    affineValue, Fin.sum_univ_succ, flipBits]
  ring

theorem mixedProduct_point_error (x : Fin 4 → Bool) :
    |mixedProduct x - (if x = mixedVertex then 1 else 0)| ≤ (1 : ℝ)/25 := by
  classical
  have he : x = mixedVertex ↔ x 0 = true ∧ x 1 = true ∧ x 2 = false ∧ x 3 = false := by
    constructor
    · intro hx; subst x; simp [mixedVertex]
    · rintro ⟨h0,h1,h2,h3⟩
      funext i
      fin_cases i <;> simp [mixedVertex, h0, h1, h2, h3]
  rw [mixedProduct_formula]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [he, h0, h1, h2, h3, boolToReal]

/-- Even a product of two genuine reciprocal heads of opposite orientations
cannot be uniformly compiled into nonnegative heads with arbitrarily small
error. Arbitrary signed output heads are not excluded by this theorem. -/
theorem mixedProduct_nonnegative_compiler_error {H : ℕ} (φ : Fin H → FracAtom 4)
    (bias ε : ℝ) (hbias : 0 ≤ bias) (hφ : ∀ h x, 0 ≤ (φ h).eval x)
    (happrox : ∀ x, |score φ bias x - mixedProduct x| ≤ ε) :
    (4 : ℝ)/25 ≤ ε := by
  have hp : ∀ x, |score φ bias x - (if x = mixedVertex then 1 else 0)| ≤ ε+1/25 := by
    intro x
    calc
      _ ≤ |score φ bias x - mixedProduct x| +
          |mixedProduct x - (if x = mixedVertex then 1 else 0)| := abs_sub_le _ _ _
      _ ≤ ε+1/25 := add_le_add (happrox x) (mixedProduct_point_error x)
  have hh := point_error_ge_one_fifth φ bias (ε+1/25) hbias hφ mixedVertex 0 1 2 3
    (by decide) (by decide) rfl rfl rfl rfl hp
  linarith

end HeadComplexity.NonnegativePointApproximation
