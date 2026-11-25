import HeadComplexity.Research.OneHeadFullContact

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable section
namespace HeadComplexity.PencilMoebiusTangentObstruction
open scoped BigOperators

abbrev Cube := Fin 6 → Bool

def numeratorCoeffs : Fin 2 → Fin 6 → ℝ :=
  ![![1,-1,0,0,0,0], ![0,0,1,-1,0,0]]

def numerator (h : Fin 2) (x : Cube) : ℝ := affineValue 0 (numeratorCoeffs h) x

def denominator (h : Fin 2) (x : Cube) : ℝ :=
  affineValue 1 (fun _ ↦ (h.val : ℝ)+1) x

def atom (h : Fin 2) : FracAtom 6 :=
  FracAtom.ofPositiveAffineRatio 0 (numeratorCoeffs h) 1
    (fun _ ↦ (h.val : ℝ)+1) (by norm_num) (by intro i; positivity)

theorem atom_eval (h : Fin 2) (x : Cube) :
    (atom h).eval x = numerator h x / denominator h x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x

def score (x : Cube) : ℝ := 1 + numerator 0 x / denominator 0 x +
  numerator 1 x / denominator 1 x

theorem score_pos (x : Cube) : 0 < score x := by
  have hx : x = ![x 0,x 1,x 2,x 3,x 4,x 5] := by
    ext i; fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    simp only [score,numerator,denominator,affineValue,Fin.sum_univ_succ] <;>
    norm_num [numeratorCoeffs,boolToReal]

def points (k : Fin 3) (j : Fin 4) : Cube :=
  ![![true,false,true,false,decide (1 ≤ k.val),decide (2 ≤ k.val)],
    ![true,false,false,true,decide (1 ≤ k.val),decide (2 ≤ k.val)],
    ![false,true,true,false,decide (1 ≤ k.val),decide (2 ≤ k.val)],
    ![false,true,false,true,decide (1 ≤ k.val),decide (2 ≤ k.val)]] j

def weights : Fin 3 → ℝ := ![-15975,81536,-83025]
def signs : Fin 4 → ℝ := ![1,-1,-1,1]

def annihilator (F : Cube → ℝ) : ℝ :=
  ∑ k, weights k * ∑ j, signs j * F (points k j)

def affine (a : Fin 7 → ℝ) (x : Cube) : ℝ :=
  affineValue (a 0) (fun i ↦ a i.succ) x

/-- An enlargement of the complete parameter tangent: arbitrary affine
numerator and denominator variations, and an arbitrary bias variation. -/
def tangent (c : ℝ) (a₀ a₁ d₀ d₁ : Fin 7 → ℝ) (x : Cube) : ℝ :=
  c + affine a₀ x / denominator 0 x + affine a₁ x / denominator 1 x -
    numerator 0 x * affine d₀ x / (denominator 0 x)^2 -
    numerator 1 x * affine d₁ x / (denominator 1 x)^2

/-- Twelve actual Boolean evaluations annihilate every full affine-parameter
quotient-rule tangent at these two admissible pencil heads. -/
theorem annihilator_tangent (c : ℝ) (a₀ a₁ d₀ d₁ : Fin 7 → ℝ) :
    annihilator (tangent c a₀ a₁ d₀ d₁) = 0 := by
  simp only [annihilator,tangent,affine,numerator,denominator,affineValue,Fin.sum_univ_succ]
  norm_num [weights,signs,points,numeratorCoeffs,boolToReal]
  ring

/-- The infinitesimal Möbius direction does not lie in that tangent space. -/
theorem annihilator_moebius : annihilator (fun x ↦ 1-(score x)^2) = -16 := by
  simp only [annihilator,score,numerator,denominator,affineValue,Fin.sum_univ_succ]
  norm_num [weights,signs,points,numeratorCoeffs,boolToReal]

theorem no_moebius_tangent (c : ℝ) (a₀ a₁ d₀ d₁ : Fin 7 → ℝ) :
    ¬ ∀ x, tangent c a₀ a₁ d₀ d₁ x = 1-(score x)^2 := by
  intro h
  have he : tangent c a₀ a₁ d₀ d₁ = fun x ↦ 1-(score x)^2 := funext h
  have ha := annihilator_tangent c a₀ a₁ d₀ d₁
  rw [he,annihilator_moebius] at ha
  norm_num at ha

end HeadComplexity.PencilMoebiusTangentObstruction
