import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Cross-group coefficients of centered Boolean reductions

Collapsing every replica in a group to its group variable aggregates affine
slopes. The top-degree squarefree coefficients of this collapsed polynomial
survive centered Boolean reduction. Group-preserving permutations also leave
the collapsed polynomial unchanged. These are exact polynomial identities;
they make no assertion about lower-degree or repeated-group coefficients.
-/

namespace HeadComplexity.RoPECrossBlockCoefficients

open scoped BigOperators
open MvPolynomial

noncomputable def affine {σ : Type*} [Fintype σ] (c : ℝ) (v : σ → ℝ) :
    MvPolynomial σ ℝ := C c + ∑ i, C (v i) * X i

/-- Replica collapse aggregates, rather than averages, each affine slope. -/
theorem rename_group_affine {G I : Type*} [Fintype G] [Fintype I]
    (c : ℝ) (v : G × I → ℝ) :
    rename Prod.fst (affine c v) = affine c (fun g ↦ ∑ i, v (g, i)) := by
  simp only [affine, map_add, map_sum, map_mul, rename_C, rename_X,
    Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_mul]

noncomputable def oddPart {σ : Type*} (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun k ↦ k % 2) (by simp)

theorem oddPart_apply {σ : Type*} (d : σ →₀ ℕ) (i : σ) :
    oddPart d i = d i % 2 := rfl

theorem exponent_sum_mapDomain {σ τ : Type*} (g : σ → τ) (d : σ →₀ ℕ) :
    (d.mapDomain g).sum (fun _ e ↦ e) = d.sum (fun _ e ↦ e) := by
  apply Finsupp.sum_mapDomain_index <;> simp

theorem oddPart_eq_of_squarefree_collapse {σ τ : Type*} (g : σ → τ)
    (d : σ →₀ ℕ) (e : τ →₀ ℕ) (he : ∀ t, e t ≤ 1)
    (h : d.mapDomain g = e) : oddPart d = d := by
  classical
  ext i
  change d i % 2 = d i
  apply Nat.mod_eq_of_lt
  have hi : d i ≤ (d.mapDomain g) (g i) := by
    rw [Finsupp.mapDomain_apply_eq_sum]
    by_cases hz : d i = 0
    · simp [hz]
    · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp [hz])
  rw [h] at hi
  have := he (g i)
  omega

theorem oddPart_sum_le {σ : Type*} [Finite σ] (d : σ →₀ ℕ) :
    (oddPart d).sum (fun _ e ↦ e) ≤ d.sum (fun _ e ↦ e) := by
  classical
  letI := Fintype.ofFinite σ
  rw [Finsupp.sum_fintype _ (fun _ e ↦ e) (fun _ ↦ rfl),
    Finsupp.sum_fintype _ (fun _ e ↦ e) (fun _ ↦ rfl)]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mod_le _ _

/-- A top-degree collapsed monomial cannot be created by deleting pairs of
replica occurrences. If it is squarefree, those deletions cannot destroy it. -/
theorem oddPart_collapse_eq_iff {σ τ : Type*} [Finite σ] (g : σ → τ)
    (d : σ →₀ ℕ) (e : τ →₀ ℕ) (he : ∀ t, e t ≤ 1)
    (hd : d.sum (fun _ k ↦ k) ≤ e.sum (fun _ k ↦ k)) :
    (oddPart d).mapDomain g = e ↔ d.mapDomain g = e := by
  classical
  letI := Fintype.ofFinite σ
  constructor
  · intro h
    have hs : (oddPart d).sum (fun _ k ↦ k) = d.sum (fun _ k ↦ k) := by
      have heq := exponent_sum_mapDomain g (oddPart d)
      rw [h] at heq
      exact le_antisymm (oddPart_sum_le d) (by omega)
    have heq : oddPart d = d := by
      rw [Finsupp.sum_fintype _ (fun _ e ↦ e) (fun _ ↦ rfl),
        Finsupp.sum_fintype _ (fun _ e ↦ e) (fun _ ↦ rfl)] at hs
      have hall := (Finset.sum_eq_sum_iff_of_le
        (fun i (_ : i ∈ Finset.univ) ↦ Nat.mod_le (d i) 2)).mp hs
      ext i
      exact hall i (Finset.mem_univ i)
    simpa only [heq] using h
  · intro h
    rw [oddPart_eq_of_squarefree_collapse g d e he h, h]

/-- Centered Boolean reduction, using the relations X_i squared equals one. -/
noncomputable def centeredReduction {σ : Type*} (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  ∑ d ∈ P.support, monomial (oddPart d) (P.coeff d)

/-- The actual coefficient of any squarefree monomial at the degree bound
survives Boolean reduction and replica collapse exactly. -/
theorem coeff_collapse_centeredReduction {σ τ : Type*} [Finite σ]
    (g : σ → τ) (P : MvPolynomial σ ℝ) (e : τ →₀ ℕ)
    (he : ∀ t, e t ≤ 1) (hP : P.totalDegree ≤ e.sum (fun _ k ↦ k)) :
    (rename g (centeredReduction P)).coeff e = (rename g P).coeff e := by
  classical
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  simp only [centeredReduction, map_sum, coeff_sum, rename_monomial, coeff_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [oddPart_collapse_eq_iff g d e he ((le_totalDegree hd).trans hP)]

theorem centeredReduction_totalDegree_le {σ : Type*} [Finite σ]
    (P : MvPolynomial σ ℝ) : (centeredReduction P).totalDegree ≤ P.totalDegree := by
  classical
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_monomial_le _ _).trans ((oddPart_sum_le d).trans (le_totalDegree hd))

/-- The reduction is exact at every centered Boolean point. -/
theorem centeredReduction_eval_eq {σ : Type*} (P : MvPolynomial σ ℝ)
    (z : σ → ℝ) (hz : ∀ i, z i ^ 2 = 1) :
    eval z (centeredReduction P) = eval z P := by
  classical
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  simp only [centeredReduction, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  rw [oddPart, Finsupp.prod_mapRange_index (fun i ↦ pow_zero (z i))]
  apply Finsupp.prod_congr
  intro i _
  conv_rhs => rw [← Nat.mod_add_div (d i) 2]
  simp only [pow_add, pow_mul, hz, one_pow, mul_one]

/-- Renaming within a group has no effect after replica collapse. -/
theorem collapse_rename_preserving {σ τ : Type*} (g : σ → τ)
    (π : σ → σ) (hπ : ∀ i, g (π i) = g i) (P : MvPolynomial σ ℝ) :
    rename g (rename π P) = rename g P := by
  rw [rename_rename]
  have he : g ∘ π = g := funext hπ
  rw [he]

/-- Finite averaging over arbitrary group-preserving maps commutes with
collapse. No permutation or nonempty-family assumption is needed for this
unnormalized sum identity. -/
theorem collapse_sum_rename_preserving {σ τ κ : Type*} [Fintype κ]
    (g : σ → τ) (π : κ → σ → σ) (hπ : ∀ k i, g (π k i) = g i)
    (P : MvPolynomial σ ℝ) :
    rename g (∑ k, rename (π k) P) = Fintype.card κ • rename g P := by
  simp only [map_sum, collapse_rename_preserving g _ (hπ _), Finset.sum_const,
    Finset.card_univ]

noncomputable def threeExponent : Fin 3 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1

/-- The six assignments of three distinct variables to three affine factors
are exactly their mixed cubic coefficient. All affine constants disappear. -/
theorem coeff_three_affine_product (a b c : ℝ) (A B C' : Fin 3 → ℝ) :
    coeff threeExponent (affine a A * affine b B * affine c C') =
      A 0 * B 1 * C' 2 + A 0 * B 2 * C' 1 +
      A 1 * B 0 * C' 2 + A 1 * B 2 * C' 0 +
      A 2 * B 0 * C' 1 + A 2 * B 1 * C' 0 := by
  simp only [affine, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [add_mul, mul_add, coeff_add, X, C_apply, monomial_mul, coeff_monomial]
  have he (s t : Fin 3 →₀ ℕ) : s = t ↔ s 0 = t 0 ∧ s 1 = t 1 ∧ s 2 = t 2 := by
    constructor
    · rintro rfl; simp
    · intro h; ext i; fin_cases i <;> simp_all
  norm_num [threeExponent, he, Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff]
  ring

/-- Combining slope aggregation with the actual mixed coefficient identity
shows that the cross-group cubic tensor depends only on the three group sums
of each affine factor, even when the replica count is zero. -/
theorem coeff_three_collapsed_affine_product {I : Type*} [Fintype I]
    (a b c : ℝ) (A B C' : Fin 3 × I → ℝ) :
    coeff threeExponent
      (rename Prod.fst (affine a A * affine b B * affine c C')) =
      (∑ r, A (0, r)) * (∑ r, B (1, r)) * (∑ r, C' (2, r)) +
      (∑ r, A (0, r)) * (∑ r, B (2, r)) * (∑ r, C' (1, r)) +
      (∑ r, A (1, r)) * (∑ r, B (0, r)) * (∑ r, C' (2, r)) +
      (∑ r, A (1, r)) * (∑ r, B (2, r)) * (∑ r, C' (0, r)) +
      (∑ r, A (2, r)) * (∑ r, B (0, r)) * (∑ r, C' (1, r)) +
      (∑ r, A (2, r)) * (∑ r, B (1, r)) * (∑ r, C' (0, r)) := by
  simp only [map_mul, rename_group_affine, coeff_three_affine_product]

end HeadComplexity.RoPECrossBlockCoefficients
