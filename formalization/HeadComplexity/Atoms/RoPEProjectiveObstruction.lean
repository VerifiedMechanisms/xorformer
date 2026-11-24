import HeadComplexity.Atoms.RoPE

set_option linter.style.header false

/-!
# A limitation of common projective input shifts

In centered coordinates, the substitution `z ↦ z / (1 + a*z₀ + b*z₁)`
changes denominator directions `(r,0)` and `(-r,0)` into `(a+r,b)` and
`(a-r,b)`. For `r ≥ 1/2`, these cannot both be positive denominators with
uniform slopes. This is an obstruction to that particular transformation,
not a separation between Boolean head-complexity classes.
-/

namespace HeadComplexity.RoPEProjectiveObstruction

open scoped BigOperators
open AffineFraction

theorem no_common_oriented_shift (r a b : ℝ) (hr : (1 : ℝ) / 2 ≤ r)
    (hplus : 0 < 1 - (a + r) - b) (hminus : 0 < 1 + (a - r) + b) :
    ¬ (UniformSign (![a + r, b] : Fin 2 → ℝ) ∧
      UniformSign (![a - r, b] : Fin 2 → ℝ)) := by
  rintro ⟨hp, hm⟩
  rcases hp with hp | hp | hp <;> rcases hm with hm | hm | hm
  all_goals
    have hp0 := hp 0
    have hp1 := hp 1
    have hm0 := hm 0
    have hm1 := hm 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hp0 hp1 hm0 hm1
    linarith

/-- The affine denominator obtained from the centered direction `(r,0)`
after a common projective input shift by `(a,b)`. -/
noncomputable def shiftedRatio (r a b : ℝ) : AffineFraction 2 where
  A := fun _ ↦ 0
  b := 0
  C := ![2 * (a + r), 2 * b]
  d := 1 - (a + r) - b

theorem shifted_denominator (r a b : ℝ) (x : Fin 2 → Bool) :
    (shiftedRatio r a b).denominator x =
      1 + (a + r) * (2 * boolToReal (x 0) - 1) +
        b * (2 * boolToReal (x 1) - 1) := by
  simp [shiftedRatio, AffineFraction.denominator, Fin.sum_univ_two]
  ring

private theorem uniform_unscale (v : Fin 2 → ℝ)
    (hv : UniformSign (fun i ↦ 2 * v i)) : UniformSign v := by
  rcases hv with hv | hv | hv
  · exact Or.inl fun i ↦ by linarith [hv i]
  · exact Or.inr (Or.inl fun i ↦ by linarith [hv i])
  · exact Or.inr (Or.inr fun i ↦ by linarith [hv i])

/-- No shift makes both opposite directions vanilla-admissible. -/
theorem shifted_pair_not_admissible (r a b : ℝ) (hr : (1 : ℝ) / 2 ≤ r) :
    ¬ ((shiftedRatio r a b).Admissible ∧ (shiftedRatio (-r) a b).Admissible) := by
  rintro ⟨hp, hm⟩
  have hplus := hp.1 ![false, false]
  have hminus := hm.1 ![true, true]
  rw [shifted_denominator] at hplus hminus
  norm_num [boolToReal] at hplus hminus
  apply no_common_oriented_shift r a b hr (by linarith) (by linarith)
  constructor
  · apply uniform_unscale
    convert hp.2.1 using 1
    funext i
    fin_cases i <;> rfl
  · apply uniform_unscale
    convert hm.2.1 using 1
    funext i
    fin_cases i <;> simp [shiftedRatio, sub_eq_add_neg]

/-- A genuine nondegenerate pure atom whose normalized centered denominator
direction is `(3/4,0)`. Complementation supplies the opposite direction. -/
noncomputable def positiveDirection : PureRoPEAtom 2 where
  a := ![1 / 20, 1 / 10]
  b := ![31 / 20, 1 / 10]
  γ := 1 / 10
  η := 0
  v₀ := 0
  v₁ := 1
  ha i := by fin_cases i <;> norm_num
  hb i := by fin_cases i <;> norm_num
  hγ := by norm_num

theorem positiveDirection_denominator (x : Fin 2 → Bool) :
    positiveDirection.toAffineFraction.denominator x =
      1 + (3 / 4 : ℝ) * (2 * boolToReal (x 0) - 1) := by
  simp [positiveDirection, PureRoPEAtom.toAffineFraction,
    AffineFraction.denominator, Fin.sum_univ_two]
  ring

theorem negativeDirection_denominator (x : Fin 2 → Bool) :
    positiveDirection.flip.toAffineFraction.denominator x =
      1 - (3 / 4 : ℝ) * (2 * boolToReal (x 0) - 1) := by
  simp [positiveDirection, PureRoPEAtom.flip, PureRoPEAtom.toAffineFraction,
    AffineFraction.denominator, Fin.sum_univ_two]
  ring

end HeadComplexity.RoPEProjectiveObstruction
