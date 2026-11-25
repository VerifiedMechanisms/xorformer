import HeadComplexity.Research.RelativeMarginQuantifiers
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.LiteralMarginNonattainmentWitness
open Finset RelativeMarginQuantifiers
open scoped BigOperators

variable (n : ℕ)

def literal : (Fin (n+1) → Bool) → Bool := fun x => x 0

def weight (x : Fin (n+1) → Bool) : ℝ := ∑ i, boolToReal (x i)

def literalAtom (ε : ℝ) (hε : 0 < ε) : FracAtom (n+1) :=
  FracAtom.ofPositiveAffineRatio (-1) (fun i => if i = 0 then 2 else 0)
    1 (fun _ => ε) zero_lt_one (fun _ => hε)

theorem weight_bounds (x : Fin (n+1) → Bool) : 0 ≤ weight n x ∧ weight n x ≤ n+1 := by
  constructor
  · apply sum_nonneg; intro i _; cases x i <;> norm_num [boolToReal]
  · calc
      weight n x ≤ ∑ _i : Fin (n+1), (1 : ℝ) := sum_le_sum fun i _ => by
        cases x i <;> norm_num [boolToReal]
      _ = n+1 := by simp

@[simp] theorem literalAtom_eval (ε : ℝ) (hε : 0 < ε) (x : Fin (n+1) → Bool) :
    (literalAtom n ε hε).eval x = (if x 0 then 1 else -1)/(1+ε*weight n x) := by
  rw [literalAtom,FracAtom.ofPositiveAffineRatio_eval]
  have hn : affineValue (-1) (fun i : Fin (n+1) => if i = 0 then 2 else 0) x =
      if x 0 then 1 else -1 := by
    simp only [affineValue,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    cases x 0 <;> norm_num [boolToReal]
  rw [hn]
  simp only [affineValue,← Finset.mul_sum,weight]

theorem literalAtom_abs (ε : ℝ) (hε : 0 < ε) (x : Fin (n+1) → Bool) :
    |(literalAtom n ε hε).eval x| = 1/(1+ε*weight n x) := by
  have hp : 0 < 1+ε*weight n x := by have := (weight_bounds n x).1; positivity
  rw [literalAtom_eval,abs_div,abs_of_pos hp]
  cases x 0 <;> norm_num

theorem literalAtom_signed (ε : ℝ) (hε : 0 < ε) (x : Fin (n+1) → Bool) :
    signedLabel (literal n) x * (literalAtom n ε hε).eval x = 1/(1+ε*weight n x) := by
  rw [literalAtom_eval]
  cases hx : x 0 <;> simp [signedLabel,literal,hx,neg_div]

theorem literalAtom_sup (ε : ℝ) (hε : 0 < ε) : atomSup (literalAtom n ε hε) = 1 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x _
    rw [literalAtom_abs]
    have hp : 1 ≤ 1+ε*weight n x := by nlinarith [mul_nonneg hε.le (weight_bounds n x).1]
    exact (div_le_one (by linarith)).mpr hp
  · have hh := abs_eval_le_atomSup (literalAtom n ε hε) (fun _ => false)
    simpa [literalAtom_abs,weight,boolToReal] using hh

/-- Genuine strictly positive denominator slopes give the literal an exact
relative margin approaching one as epsilon tends to zero. -/
theorem literal_margin (ε : ℝ) (hε : 0 < ε) :
    StrictlyRepresents (literal n) (fun _ : Fin 1 => literalAtom n ε hε) 0 ∧
    relativeMargin (literal n) (fun _ : Fin 1 => literalAtom n ε hε) 0 =
      1/(1+(n+1)*ε) := by
  have hscore (x : Fin (n+1) → Bool) :
      signedLabel (literal n) x * score (fun _ : Fin 1 => literalAtom n ε hε) 0 x =
        1/(1+ε*weight n x) := by simpa [score] using literalAtom_signed n ε hε x
  have hp (x : Fin (n+1) → Bool) : 0 < 1+ε*weight n x := by
    have := (weight_bounds n x).1
    positivity
  have hm : minimumSignedScore (literal n) (fun _ : Fin 1 => literalAtom n ε hε) 0 =
      1/(1+(n+1)*ε) := by
    unfold minimumSignedScore
    apply le_antisymm
    · calc
        _ ≤ signedLabel (literal n) (fun _ => true) *
            score (fun _ : Fin 1 => literalAtom n ε hε) 0 (fun _ => true) :=
          Finset.inf'_le (fun x : Fin (n+1) → Bool => signedLabel (literal n) x *
            score (fun _ : Fin 1 => literalAtom n ε hε) 0 x)
            (Finset.mem_univ (fun _ : Fin (n+1) => true))
        _ = _ := by rw [hscore]; simp [weight,boolToReal,mul_comm]
    · apply Finset.le_inf'
      intro x _
      rw [hscore]
      exact div_le_div_of_nonneg_left (by norm_num) (hp x)
        (by nlinarith [(weight_bounds n x).2])
  constructor
  · intro x; rw [hscore]; exact div_pos zero_lt_one (hp x)
  · simp [relativeMargin,hm,amplitude,literalAtom_sup]


/-- Every margin strictly below one is achievable by one genuine head for
this literal, in every positive input dimension. -/
theorem hasRelativeMargin_below_one (γ : ℝ) (hγ : γ < 1) :
    HasRelativeMargin (n+1) 1 (literal n) γ := by
  let ε := (1-γ)/((n : ℝ)+1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hγ) (by positivity)
  obtain ⟨hs,hm⟩ := literal_margin n ε hε
  refine ⟨(fun _ => literalAtom n ε hε),0,hs,?_⟩
  rw [hm]
  have he : ((n : ℝ)+1)*ε = 1-γ := by
    dsimp [ε]
    field_simp
  rw [he]
  apply (le_div_iff₀ (by linarith : 0 < 1+(1-γ))).mpr
  nlinarith [sq_nonneg (γ-1)]

end HeadComplexity.LiteralMarginNonattainmentWitness
