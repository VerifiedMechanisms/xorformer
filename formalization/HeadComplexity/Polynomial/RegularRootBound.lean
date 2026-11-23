import HeadComplexity.Polynomial.DiagonalRootBound
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Persistence and counting of regular polynomial roots

A zero with invertible derivative persists under a sufficiently small diagonal
perturbation. Distinct regular zeros persist as distinct zeros. The diagonal
root bound then bounds every finite family of regular zeros of a polynomial
system, without using a sign-pattern theorem.
-/

namespace HeadComplexity.PolynomialRootCount

open Filter MvPolynomial
open scoped Topology

section Persistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A regular zero persists under a differentiable perturbation. -/
theorem exists_zero_branch {f g : E → E} {x : E}
    (A : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (hf : HasStrictFDerivAt f A.toContinuousLinearMap x)
    (hg : HasStrictFDerivAt g B x) (hz : f x = 0) :
    ∃ u : ℝ → E, Tendsto u (𝓝 0) (𝓝 x) ∧
      ∀ᶠ t in 𝓝 0, f (u t) + t • g (u t) = 0 := by
  let F : ℝ × E → E := fun z ↦ f z.2 + z.1 • g z.2
  let D : ℝ × E →L[ℝ] E :=
    A.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E) +
      (ContinuousLinearMap.fst ℝ ℝ E).smulRight (g x)
  have hF : HasStrictFDerivAt F D (0, x) := by
    have hsnd : HasStrictFDerivAt (Prod.snd : ℝ × E → E)
        (ContinuousLinearMap.snd ℝ ℝ E) (0, x) := hasStrictFDerivAt_snd
    have hfst : HasStrictFDerivAt (Prod.fst : ℝ × E → ℝ)
        (ContinuousLinearMap.fst ℝ ℝ E) (0, x) := hasStrictFDerivAt_fst
    have h := (hf.comp ((0 : ℝ), x) hsnd).add
      (hfst.smul (hg.comp ((0 : ℝ), x) hsnd))
    convert h using 1
    simp [D]
  have hD : (D ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible := by
    refine ⟨A, ?_⟩
    ext z
    simp [D]
  refine ⟨hF.implicitFunctionOfProdDomain hD,
    hF.tendsto_implicitFunctionOfProdDomain hD, ?_⟩
  simpa [F, hz] using hF.eventually_apply_implicitFunctionOfProdDomain hD

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Finitely many branches with distinct limits are eventually distinct. -/
theorem eventually_injective_branches {ι T : Type*} [Finite ι]
    {l : Filter T} (x : ι → E) (hx : Function.Injective x)
    (u : ι → T → E) (hu : ∀ a, Tendsto (u a) l (𝓝 (x a))) :
    ∀ᶠ t in l, Function.Injective (fun a ↦ u a t) := by
  classical
  have hne (a b : ι) : ∀ᶠ t in l, a ≠ b → u a t ≠ u b t := by
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hab).elim
    have hlim := ((hu a).sub (hu b)).eventually_ne
      (sub_ne_zero.mpr (fun h ↦ hab (hx h)))
    filter_upwards [hlim] with t ht _
    exact sub_ne_zero.mp ht
  have hall : ∀ᶠ t in l, ∀ a b, a ≠ b → u a t ≠ u b t :=
    Filter.eventually_all.mpr fun a ↦ Filter.eventually_all.mpr (hne a)
  filter_upwards [hall] with t ht
  intro a b h
  by_contra hab
  exact ht a b hab h

end Persistence

section PolynomialSystems

variable {n d : ℕ} {ι : Type*} [Fintype ι]

/-- Every finite family of regular roots of a degree-`d` system has at most
`(d + 1)^n` members. The extra degree is used only for the diagonal perturbation. -/
theorem regular_roots_card_le
    (p : Fin n → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ d)
    (x : ι → Fin n → ℝ) (hx : Function.Injective x)
    (hroot : ∀ a i, eval (x a) (p i) = 0)
    (A : ι → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hA : ∀ a, HasStrictFDerivAt (fun z i ↦ eval z (p i))
      (A a).toContinuousLinearMap (x a)) :
    Fintype.card ι ≤ (d + 1) ^ n := by
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun z i ↦ z i ^ (d + 1)
  let B (a : ι) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦
      ((d + 1) • (x a i) ^ d) • ContinuousLinearMap.proj i)
  have hg (a : ι) : HasStrictFDerivAt g (B a) (x a) := by
    apply hasStrictFDerivAt_pi.mpr
    intro i
    simpa [B] using (hasStrictFDerivAt_apply (𝕜 := ℝ) i (x a)).pow (d + 1)
  have hzero (a : ι) : (fun i ↦ eval (x a) (p i)) = 0 := funext (hroot a)
  choose u hu hsol using fun a ↦ exists_zero_branch (A a) (B a) (hA a) (hg a) (hzero a)
  have hinj := eventually_injective_branches x hx u hu
  have hsols : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ a,
      (fun i ↦ eval (u a t) (p i)) + t • g (u a t) = 0 :=
    Filter.eventually_all.mpr hsol
  have hgood : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Function.Injective (fun a ↦ u a t) ∧
      ∀ a, (fun i ↦ eval (u a t) (p i)) + t • g (u a t) = 0 :=
    (hinj.and hsols).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεinj, hεsol⟩ := (Filter.Eventually.and hne hgood).exists
  apply perturbed_roots_card_le p (fun i ↦ Nat.lt_succ_of_le (hp i))
    (Nat.zero_lt_succ d) ε hε (fun a ↦ u a ε) hεinj
  intro a i
  have hi := congrFun (hεsol a) i
  simpa [g] using hi

end PolynomialSystems

end HeadComplexity.PolynomialRootCount
