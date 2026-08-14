import HeadComplexity.Atoms.WeightedAtom
import HeadComplexity.Atoms.HeadToFracAtom
import HeadComplexity.Polynomial.UnivariateThresholdDegree

set_option linter.style.header false

/-!
# Weighted polynomial predicates

This module bridges the two reusable upper-bound abstractions:

* `exists_partialFraction_sign_atoms` converts any univariate polynomial of
  degree at most `K` into `K` reciprocal affine atoms on a half-line;
* `weightedAtomFamily_readout` realizes those atoms by `K` attention heads when
  the polynomial is evaluated at the positive weighted statistic `wT lam`.

Consequently, every Boolean predicate sign-represented by
`P.eval (wT lam bits)` is computable with `K` heads.  Unlike interpolation over
the entire image of `wT`, this bound depends on the degree of the supplied
polynomial and can therefore be much smaller than the image size minus one.
-/

namespace HeadComplexity

open Polynomial Finset
open scoped BigOperators InnerProductSpace

variable {n K : ℕ}

/-- A degree-`K` polynomial in a positive weighted statistic yields `K`
reciprocal atoms whose threshold has exactly the same strict sign test on the
Boolean cube. -/
theorem exists_weightedPolynomial_atoms (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : ℝ[X]) (hdeg : P.natDegree ≤ K) :
    ∃ (av bv : Fin K → ℝ) (τ : ℝ),
      (∀ h, wLam lam + 1 < av h) ∧
      ∀ bits, ((∑ h, bv h / (wT lam bits + av h)) > τ ↔
        0 < P.eval (wT lam bits)) := by
  obtain ⟨av, bv, τ, hav, hsign⟩ :=
    exists_partialFraction_sign_atoms P (wLam lam + 1) hdeg
  refine ⟨av, bv, τ, hav, fun bits => hsign (wT lam bits) ?_⟩
  have hT : 0 ≤ wT lam bits := wT_nonneg hlam bits
  have hL : 0 ≤ wLam lam := Finset.sum_nonneg (fun i _ => (hlam i).le)
  linarith

/-- **Weighted-polynomial upper construction.** If a Boolean function is
strictly sign-represented by a univariate polynomial of degree at most `K`
applied to a positive weighted sum, then it is computable with `K` heads. -/
theorem weightedPolynomial_computable (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : ℝ[X]) (hdeg : P.natDegree ≤ K) (f : (Fin n → Bool) → Bool)
    (hsign : ∀ bits, (0 < P.eval (wT lam bits) ↔ f bits = true)) :
    computableWithHeadsN n K f := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨2, (fun _ => weightedAtomHead lam 2 0), 0,
      (if f default then -1 else 1), ?_⟩
    intro bits
    rw [inner_zero_left, Subsingleton.elim bits default]
    cases f default <;> norm_num
  · obtain ⟨av, bv, τ, hav, hatom⟩ :=
      exists_weightedPolynomial_atoms lam hlam P hdeg
    refine ⟨2, (fun h => weightedAtomHead lam (av h) (bv h)), atomReadout, τ, ?_⟩
    intro bits
    change ⟪atomReadout,
      ∑ h, (weightedAtomHead lam (av h) (bv h)).attnUpdate bits⟫_ℝ > τ ↔ _
    rw [weightedAtomFamily_readout lam hn hlam av bv hav bits]
    exact (hatom bits).trans (hsign bits)

/-- A statistic-level univariate threshold certificate over `wT lam` is
realized by the same number of weighted attention heads. -/
theorem weighted_computable_of_UnivariateThresholdDegLE
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) (f : (Fin n → Bool) → Bool)
    (hpoly : UnivariateThresholdDegLE (wT lam) f K) :
    computableWithHeadsN n K f := by
  obtain ⟨P, hdeg, hsign⟩ := hpoly
  exact weightedPolynomial_computable lam hlam P hdeg f hsign

/-- The weighted univariate certificate also produces the repository's exact
fractional-atom normal form, via the general head-to-atom equivalence. -/
theorem weighted_fracComputable_of_UnivariateThresholdDegLE
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) (f : (Fin n → Bool) → Bool)
    (hpoly : UnivariateThresholdDegLE (wT lam) f K) :
    fracComputable n K f :=
  fracComputable_of_computable
    (weighted_computable_of_UnivariateThresholdDegLE lam hlam f hpoly)

end HeadComplexity
