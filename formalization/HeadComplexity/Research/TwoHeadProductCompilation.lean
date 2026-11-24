import HeadComplexity.Research.RadialMomentTransfer
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
Every strict two-ratio score on a finite set has the same signs as a sum of
three affine-times-exponential terms when the data are affine. This is a
joint compilation with a third term, not a fixed atomwise replacement.
It supplies no bound for arbitrary head counts.
-/

noncomputable section

namespace HeadComplexity.TwoHeadProductCompilation

open Filter Finset
open scoped Topology BigOperators
open RadialMomentTransfer

def compiled (a b u v t : ℝ) : ℝ :=
  a * Real.exp (t*v) + b * Real.exp (t*u) - (a+b)

theorem compiled_scaled_limit (a b u v : ℝ) :
    Tendsto (fun t : ℝ => compiled a b u v t / t) (𝓝[>] 0)
      (𝓝 (a*v+b*u)) := by
  let weights : Fin 3 → ℝ := ![a,b,-(a+b)]
  let shifts : Fin 3 → ℝ := ![v,u,0]
  have hz : ∀ j < 1, moment weights shifts j = 0 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [moment, weights, shifts, Fin.sum_univ_succ]
  have ht := exponential_scaled_limit weights shifts 1 hz
  simpa [exponential, moment, weights, shifts, compiled, Fin.sum_univ_succ,
    sub_eq_add_neg, add_assoc] using ht

/-- The three exponential directions are the two original denominators and
the zero direction. The bias is first absorbed into one numerator. -/
theorem uniform_two_head_sign_compilation {X : Type*} [Fintype X]
    (A D B C : X → ℝ) (c : ℝ)
    (hB : ∀ x, 0 < B x) (hC : ∀ x, 0 < C x)
    (hstrict : ∀ x, c + A x/B x + D x/C x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → ∀ x,
      0 < (c + A x/B x + D x/C x) *
        compiled (A x+c*B x) (D x) (B x) (C x) t := by
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x,
      0 < (c + A x/B x + D x/C x) *
        compiled (A x+c*B x) (D x) (B x) (C x) t := by
    rw [Filter.eventually_all]
    intro x
    have hid : (A x+c*B x)*C x+D x*B x =
        (c+A x/B x+D x/C x)*(B x*C x) := by
      field_simp [ne_of_gt (hB x), ne_of_gt (hC x)]
      ring
    have hp : 0 < (c+A x/B x+D x/C x)*
        ((A x+c*B x)*C x+D x*B x) := by
      rw [hid]
      have hm := mul_pos (mul_self_pos.mpr (hstrict x)) (mul_pos (hB x) (hC x))
      nlinarith
    have hl := (compiled_scaled_limit (A x+c*B x) (D x) (B x) (C x)).const_mul
      (c+A x/B x+D x/C x)
    have hev := hl.eventually_const_lt hp
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htp
    have ht0 : t ≠ 0 := ne_of_gt htp
    have hm := mul_pos ht htp
    convert hm using 1
    field_simp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨ε, hε, fun t ht hte => hsub ⟨?_, ht⟩⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hte

/-- The exponential of an affine Boolean form is one positive product atom.
The constant exponential factor may be absorbed into its affine numerator. -/
theorem affine_exponential_product {n : ℕ} (b₀ : ℝ) (b : Fin n → ℝ)
    (t : ℝ) (x : Fin n → Bool) :
    Real.exp (t * affineValue b₀ b x) =
      Real.exp (t*b₀) * ∏ i, (if x i then Real.exp (t*b i) else 1) := by
  rw [affineValue, mul_add, Real.exp_add, mul_sum, Real.exp_sum]
  congr 1
  apply prod_congr rfl
  intro i hi
  cases hx : x i <;> simp [boolToReal, hx]

#print axioms uniform_two_head_sign_compilation
#print axioms affine_exponential_product

end HeadComplexity.TwoHeadProductCompilation
