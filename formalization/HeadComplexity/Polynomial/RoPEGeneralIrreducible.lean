import HeadComplexity.Polynomial.RoPECubicIrreducible
import Mathlib.RingTheory.Coprime.Lemmas

set_option linter.style.header false

/-!
# Irreducibility of the general-head source polynomial

The source is linear in the numerator variables, with relatively prime
squarefree denominator products as coefficients. Extra unused variables are
included explicitly, so the statement applies before removing physical tails.
This is one algebraic component of the mathematical arbitrary-head separation.
-/

namespace HeadComplexity.RoPEGeneralPolynomial

open scoped BigOperators
open MvPolynomial

abbrev Var (H K : ℕ) := Fin H ⊕ (Fin H ⊕ Fin K)
abbrev Poly (H K : ℕ) := MvPolynomial (Var H K) ℝ

def denominatorIndex {H K : ℕ} (i : Fin H) : Var H K := Sum.inl i
def numeratorIndex {H K : ℕ} (i : Fin H) : Var H K := Sum.inr (Sum.inl i)

noncomputable def omittedProduct (H K : ℕ) (i : Fin H) : Poly H K :=
  ∏ j ∈ Finset.univ.erase i, X (denominatorIndex j)

noncomputable def core (H K : ℕ) : Poly H K :=
  ∑ i, X (numeratorIndex i) * omittedProduct H K i

noncomputable def remainder (H K : ℕ) (i : Fin H) : Poly H K :=
  ∑ j ∈ Finset.univ.erase i, X (numeratorIndex j) * omittedProduct H K j

theorem core_split (H K : ℕ) (i : Fin H) :
    core H K = omittedProduct H K i * X (numeratorIndex i) + remainder H K i := by
  rw [core, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  dsimp [remainder]
  ring

theorem eval_core {H K : ℕ} (x : Var H K → ℝ) :
    eval x (core H K) = ∑ i, x (numeratorIndex i) *
      ∏ j ∈ Finset.univ.erase i, x (denominatorIndex j) := by
  simp [core, omittedProduct]

private theorem not_mem_vars_mul {σ : Type*}
    (p q : MvPolynomial σ ℝ) (i : σ) (hp : i ∉ p.vars) (hq : i ∉ q.vars) :
    i ∉ (p * q).vars := by
  classical
  intro h
  exact (Finset.mem_union.mp (vars_mul p q h)).elim hp hq

private theorem not_mem_vars_prod {σ ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial σ ℝ) (i : σ)
    (h : ∀ j ∈ s, i ∉ (p j).vars) : i ∉ (∏ j ∈ s, p j).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact not_mem_vars_mul _ _ _ (h a (by simp))
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

private theorem not_mem_vars_sum {σ ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial σ ℝ) (i : σ)
    (h : ∀ j ∈ s, i ∉ (p j).vars) : i ∉ (∑ j ∈ s, p j).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro hi
      rcases Finset.mem_union.mp (vars_add_subset _ _ hi) with hia | his
      · exact h a (by simp) hia
      · exact ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)) his

theorem omittedProduct_ne_zero (H K : ℕ) (i : Fin H) :
    omittedProduct H K i ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun j _ ↦ X_ne_zero (denominatorIndex j))

theorem numerator_not_mem_omittedProduct_vars (H K : ℕ) (i j : Fin H) :
    numeratorIndex i ∉ (omittedProduct H K j).vars := by
  apply not_mem_vars_prod
  intro k _
  simp [numeratorIndex, denominatorIndex]

theorem numerator_not_mem_remainder_vars (H K : ℕ) (i : Fin H) :
    numeratorIndex i ∉ (remainder H K i).vars := by
  apply not_mem_vars_sum
  intro j hj
  apply not_mem_vars_mul
  · have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [numeratorIndex, Ne.symm hji]
  · exact numerator_not_mem_omittedProduct_vars H K i j

theorem core_not_dvd_omittedProduct (H K : ℕ) (i : Fin H) :
    ¬ core H K ∣ omittedProduct H K i := by
  rintro ⟨r, hr⟩
  let point : Var H K → ℝ := Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)
  have he := congrArg (eval point) hr
  simp [point, core, omittedProduct, numeratorIndex, denominatorIndex] at he

/-- Irreducibility holds for every positive head count, with arbitrary unused
coordinates already present in the polynomial ring. -/
theorem core_irreducible (H K : ℕ) (hH : 0 < H) : Irreducible (core H K) := by
  classical
  let i₀ : Fin H := ⟨0, hH⟩
  let f : Poly H K := omittedProduct H K i₀
  let g : Poly H K := ∑ i ∈ Finset.univ.erase i₀,
    X (numeratorIndex i) * omittedProduct H K i
  have hsplit : core H K = f * X (numeratorIndex i₀) + g := by
    rw [core, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    dsimp [f, g]
    ring
  rw [hsplit]
  apply irreducible_mul_X_add f g (numeratorIndex i₀)
  · exact omittedProduct_ne_zero H K i₀
  · exact numerator_not_mem_omittedProduct_vars H K i₀ i₀
  · apply not_mem_vars_sum
    intro i hi
    apply not_mem_vars_mul
    · have hi' : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      simp [numeratorIndex, Ne.symm hi']
    · exact numerator_not_mem_omittedProduct_vars H K i₀ i
  · apply IsRelPrime.prod_left
    intro j hj
    apply (X_prime.irreducible).isRelPrime_iff_not_dvd.mpr
    intro hdiv
    let point : Var H K → ℝ := fun z ↦ match z with
      | Sum.inl k => if k = j then 0 else 1
      | Sum.inr (Sum.inl k) => if k = j then 1 else 0
      | Sum.inr (Sum.inr _) => 0
    have hterm : eval point g = 1 := by
      dsimp [g]
      simp only [map_sum, map_mul, eval_X]
      rw [Finset.sum_eq_single_of_mem j hj]
      · simp only [point, numeratorIndex, if_pos rfl, one_mul, omittedProduct, map_prod, eval_X]
        apply Finset.prod_eq_one
        intro k hk
        simp only [denominatorIndex]
        exact if_neg (Finset.mem_erase.mp hk).1
      · intro i hi hij
        simp [point, numeratorIndex, hij]
    obtain ⟨r, hr⟩ := hdiv
    have he := congrArg (eval point) hr
    rw [hterm] at he
    simp [point, denominatorIndex] at he

theorem omittedProduct_homogeneous (H K : ℕ) (i : Fin H) :
    (omittedProduct H K i).IsHomogeneous (H - 1) := by
  have h := IsHomogeneous.prod (Finset.univ.erase i)
    (fun j ↦ (X (denominatorIndex j) : Poly H K)) (fun _ ↦ 1)
    (fun j _ ↦ isHomogeneous_X ℝ (denominatorIndex j))
  simpa [omittedProduct] using h

theorem core_homogeneous (H K : ℕ) (hH : 0 < H) :
    (core H K).IsHomogeneous H := by
  apply IsHomogeneous.sum
  intro i _
  have h := (isHomogeneous_X ℝ (numeratorIndex i)).mul
    (omittedProduct_homogeneous H K i)
  convert h using 1
  omega

theorem core_totalDegree (H K : ℕ) (hH : 0 < H) : (core H K).totalDegree = H :=
  (core_homogeneous H K hH).totalDegree (core_irreducible H K hH).ne_zero

/-- Degree rigidity after divisibility by the general source polynomial. -/
theorem scalar_multiple_of_core_dvd {H K : ℕ} (hH : 0 < H) (Q : Poly H K)
    (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ H) (hdiv : core H K ∣ Q) :
    ∃ c : ℝ, c ≠ 0 ∧ Q = C c * core H K := by
  obtain ⟨R, rfl⟩ := hdiv
  have hR : R ≠ 0 := by intro hz; simp [hz] at hQ
  rw [totalDegree_mul_of_isDomain (core_irreducible H K hH).ne_zero hR,
    core_totalDegree H K hH] at hdeg
  have hRdeg : R.totalDegree = 0 := by omega
  have hRc := totalDegree_eq_zero_iff_eq_C.mp hRdeg
  refine ⟨R.coeff 0, ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hRc
    exact hR hRc
  · rw [hRc, mul_comm]
    simp

end HeadComplexity.RoPEGeneralPolynomial
