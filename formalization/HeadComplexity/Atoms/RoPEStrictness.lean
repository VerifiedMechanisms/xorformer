import HeadComplexity.Atoms.RoPE
import HeadComplexity.Foundation.FiniteSignMargin

set_option linter.style.header false

/-!
# Finite strict perturbations of pure rotary classifiers

All changes here use finite real parameters and preserve Boolean labels.
They do not preserve the original real-valued score.
-/

namespace HeadComplexity

open scoped BigOperators

namespace PureRoPEAtom

variable {n : ℕ}

/-- Change only the value of token one. -/
def withValueOne (p : PureRoPEAtom n) (v : ℝ) : PureRoPEAtom n :=
  { p with v₁ := v }

/-- Total attention mass assigned to input tokens of value one. -/
noncomputable def oneMass (p : PureRoPEAtom n) (x : Fin n → Bool) : ℝ :=
  (∑ i, if x i then p.b i else 0) / p.toAffineFraction.denominator x

theorem oneMass_nonneg (p : PureRoPEAtom n) (x : Fin n → Bool) :
    0 ≤ p.oneMass x := by
  apply div_nonneg _ (p.denominator_pos x).le
  exact Finset.sum_nonneg fun i _ ↦ by
    split
    · exact (p.hb i).le
    · exact le_refl 0

theorem oneMass_le_one (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.oneMass x ≤ 1 := by
  apply (div_le_one (p.denominator_pos x)).mpr
  rw [p.denominator_eq]
  have h : (∑ i, if x i then p.b i else 0) ≤
      ∑ i, if x i then p.b i else p.a i := by
    apply Finset.sum_le_sum
    intro i _
    split
    · exact le_refl _
    · exact (p.ha i).le
  linarith [p.hγ]

theorem withValueOne_eval (p : PureRoPEAtom n) (t : ℝ) (x : Fin n → Bool) :
    (p.withValueOne (p.v₁ + t)).eval x = p.eval x + t * p.oneMass x := by
  have hnum :
      (∑ i, if x i then p.b i * (p.v₁ + t) else p.a i * p.v₀) =
        (∑ i, if x i then p.b i * p.v₁ else p.a i * p.v₀) +
          t * ∑ i, if x i then p.b i else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp <;> ring
  simp only [withValueOne, eval, oneMass, denominator_eq]
  rw [hnum]
  ring

theorem withValueOne_eval_sub_abs_le (p : PureRoPEAtom n) (t : ℝ)
    (ht : 0 ≤ t) (x : Fin n → Bool) :
    |(p.withValueOne (p.v₁ + t)).eval x - p.eval x| ≤ t := by
  rw [withValueOne_eval, add_sub_cancel_left,
    abs_of_nonneg (mul_nonneg ht (p.oneMass_nonneg x))]
  nlinarith [p.oneMass_le_one x]

end PureRoPEAtom

/-- A pure two-head classifier has a representation whose first head has a
nonzero token-value difference. The classifier, including its threshold
convention, is unchanged. -/
theorem pureRoPEComputable_two_nondegenerate {n : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n 2 f) :
    ∃ p q : PureRoPEAtom n, ∃ c : ℝ,
      p.v₁ ≠ p.v₀ ∧ ∀ x, (0 < c + p.eval x + q.eval x ↔ f x = true) := by
  obtain ⟨p, c, hp⟩ := hf
  simp_rw [Fin.sum_univ_two] at hp
  let S (x : Fin n → Bool) := c + (p 0).eval x + (p 1).eval x
  obtain ⟨δ, hδ, hshift⟩ := exists_strict_shift S
  obtain ⟨ε, hε, hstable⟩ := exists_sign_stability_margin
    (fun x ↦ S x - δ) (fun x ↦ (hshift x).2)
  have hex : ∃ t : ℝ, 0 < t ∧ t < ε ∧ (p 0).v₁ + t ≠ (p 0).v₀ := by
    by_cases h : (p 0).v₁ + ε / 2 = (p 0).v₀
    · refine ⟨ε / 3, by positivity, by linarith, ?_⟩
      intro heq
      linarith
    · exact ⟨ε / 2, by positivity, by linarith, h⟩
  obtain ⟨t, ht, htε, hne⟩ := hex
  let p' := (p 0).withValueOne ((p 0).v₁ + t)
  refine ⟨p', p 1, c - δ, hne, fun x ↦ ?_⟩
  have hclose : ∀ x, |(c - δ + p'.eval x + (p 1).eval x) - (S x - δ)| < ε := by
    intro x
    have heq : (c - δ + p'.eval x + (p 1).eval x) - (S x - δ) =
        p'.eval x - (p 0).eval x := by dsimp [S]; ring
    rw [heq]
    exact ((p 0).withValueOne_eval_sub_abs_le t ht.le x).trans_lt htε
  have hs := (hstable (fun x ↦ c - δ + p'.eval x + (p 1).eval x) hclose x).1
  exact hs.trans ((hshift x).1.trans (by simpa only [S, add_assoc] using hp x))

end HeadComplexity
