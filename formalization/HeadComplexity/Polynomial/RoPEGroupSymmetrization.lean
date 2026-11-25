import HeadComplexity.Polynomial.UnivariateReduction
import HeadComplexity.Polynomial.RoPECrossBlockCoefficients
import HeadComplexity.Polynomial.RoPECubeCoefficientUniqueness

set_option linter.style.header false

/-!
# Polynomial reduction by independent groups of Boolean coordinates

Each monomial is a product of one monomial per group. Symmetrizing these
factors separately and using the existing univariate Hamming-weight reduction
produces a polynomial in the group weights without increasing total degree.
-/

namespace HeadComplexity.RoPEGroupSymmetrization

open scoped BigOperators
open MvPolynomial

noncomputable def liftAt {G : Type*} (v : MvPolynomial G ℝ)
    (p : Polynomial ℝ) : MvPolynomial G ℝ :=
  ∑ k ∈ p.support, C (p.coeff k) * v ^ k

theorem liftAt_eval {G : Type*} (v : MvPolynomial G ℝ)
    (p : Polynomial ℝ) (q : G → ℝ) :
    eval q (liftAt v p) = p.eval (eval q v) := by
  simp only [liftAt, map_sum, map_mul, map_pow, eval_C,
    Polynomial.eval_eq_sum, Polynomial.sum_def]

theorem liftAt_totalDegree_le {G : Type*} (v : MvPolynomial G ℝ)
    (hv : v.totalDegree ≤ 1) (p : Polynomial ℝ) :
    (liftAt v p).totalDegree ≤ p.natDegree := by
  classical
  apply totalDegree_finsetSum_le
  intro k hk
  have hk' := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
  have hp := totalDegree_pow v k
  have hc := totalDegree_mul (C (p.coeff k)) (v ^ k)
  rw [totalDegree_C, zero_add] at hc
  exact hc.trans (hp.trans ((Nat.mul_le_mul_left k hv).trans (by simpa using hk')))

noncomputable def blockExponent {G : Type*} {m : ℕ}
    (d : G × Fin m →₀ ℕ) (g : G) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun r ↦ d (g, r))

@[simp] theorem blockExponent_apply {G : Type*} {m : ℕ}
    (d : G × Fin m →₀ ℕ) (g : G) (r : Fin m) :
    blockExponent d g r = d (g, r) := by simp [blockExponent]

theorem sum_blockExponent {G : Type*} [Fintype G] {m : ℕ}
    (d : G × Fin m →₀ ℕ) :
    (∑ g, (blockExponent d g).sum (fun _ k ↦ k)) = d.sum (fun _ k ↦ k) := by
  simp only [Finsupp.sum_fintype _ (fun _ k ↦ k) (fun _ ↦ rfl),
    Fintype.sum_prod_type, blockExponent_apply]

theorem exists_block_polynomial {G : Type*} {m : ℕ}
    (d : G × Fin m →₀ ℕ) (g : G) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ (blockExponent d g).sum (fun _ k ↦ k) ∧
      ∀ x : Fin m → Bool,
        p.eval (hammingWeight x : ℝ) =
          ∑ π : Equiv.Perm (Fin m),
            ∏ r : Fin m, boolToReal (x (π r)) ^ d (g, r) := by
  classical
  let M : MvPolynomial (Fin m) ℝ := monomial (blockExponent d g) 1
  have hdeg : (symmetrize M).totalDegree ≤ (blockExponent d g).sum (fun _ k ↦ k) :=
    symmetrize_totalDegree_le (totalDegree_monomial_le _ _)
  obtain ⟨p, hp, he⟩ := exists_univariate_of_symmetric (symmetrize M)
    (symmetrize_isSymmetric M) hdeg
  refine ⟨p, hp, fun x ↦ ?_⟩
  rw [he]
  simp only [symmetrize, map_sum, eval_rename, M, eval_monomial, one_mul]
  apply Finset.sum_congr rfl
  intro π _
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [Function.comp_apply, blockExponent_apply, cubePoint]

noncomputable def blockPolynomial {G : Type*} {m : ℕ}
    (d : G × Fin m →₀ ℕ) (g : G) : Polynomial ℝ :=
  (exists_block_polynomial d g).choose

theorem blockPolynomial_degree {G : Type*} {m : ℕ}
    (d : G × Fin m →₀ ℕ) (g : G) :
    (blockPolynomial d g).natDegree ≤ (blockExponent d g).sum (fun _ k ↦ k) :=
  (exists_block_polynomial d g).choose_spec.1

theorem blockPolynomial_eval {G : Type*} {m : ℕ}
    (d : G × Fin m →₀ ℕ) (g : G) (x : Fin m → Bool) :
    (blockPolynomial d g).eval (hammingWeight x : ℝ) =
      ∑ π : Equiv.Perm (Fin m), ∏ r : Fin m, boolToReal (x (π r)) ^ d (g, r) :=
  (exists_block_polynomial d g).choose_spec.2 x

noncomputable def groupPolynomial {G : Type*} [Fintype G] {m : ℕ}
    (P : MvPolynomial (G × Fin m) ℝ) : MvPolynomial G ℝ :=
  ∑ d ∈ P.support, C (P.coeff d) * ∏ g, liftAt (X g) (blockPolynomial d g)

theorem groupPolynomial_degree {G : Type*} [Fintype G] {m : ℕ}
    (P : MvPolynomial (G × Fin m) ℝ) :
    (groupPolynomial P).totalDegree ≤ P.totalDegree := by
  classical
  apply totalDegree_finsetSum_le
  intro d hd
  have hc := totalDegree_mul (C (P.coeff d))
    (∏ g, liftAt (X g) (blockPolynomial d g))
  rw [totalDegree_C, zero_add] at hc
  refine hc.trans ((totalDegree_finsetProd _ _).trans ?_)
  calc
    ∑ g, (liftAt (X g) (blockPolynomial d g)).totalDegree
      ≤ ∑ g, (blockExponent d g).sum (fun _ k ↦ k) := by
        apply Finset.sum_le_sum
        intro g _
        exact (liftAt_totalDegree_le (X g) (by simp) _).trans (blockPolynomial_degree d g)
    _ = d.sum (fun _ k ↦ k) := sum_blockExponent d
    _ ≤ P.totalDegree := le_totalDegree hd

/-- The constructed polynomial equals the exact unnormalized average over
independent permutations in all groups, on every Boolean input. -/
theorem groupPolynomial_eval {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ}
    (P : MvPolynomial (G × Fin m) ℝ) (x : G × Fin m → Bool) :
    eval (fun g ↦ (hammingWeight (fun r ↦ x (g, r)) : ℝ)) (groupPolynomial P) =
      ∑ π : G → Equiv.Perm (Fin m),
        eval (fun p : G × Fin m ↦ boolToReal (x (p.1, π p.1 p.2))) P := by
  classical
  conv_rhs => arg 2; ext π; rw [← P.support_sum_monomial_coeff]
  simp only [groupPolynomial, map_sum, map_mul, map_prod, eval_C, liftAt_eval, eval_X,
    blockPolynomial_eval, eval_monomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fintype.prod_prod_type]

/-- Substituting affine polynomials never increases total degree. -/
theorem affine_substitution_degree {σ τ : Type*} (P : MvPolynomial σ ℝ)
    (v : σ → MvPolynomial τ ℝ) (hv : ∀ i, (v i).totalDegree ≤ 1) :
    (aeval v P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [← P.support_sum_monomial_coeff]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial]
  have hc := totalDegree_mul (C (P.coeff d)) (d.prod fun i k ↦ v i ^ k)
  rw [totalDegree_C, zero_add] at hc
  refine hc.trans ((totalDegree_finsetProd _ _).trans ?_)
  change (∑ i ∈ d.support, (v i ^ d i).totalDegree) ≤ P.totalDegree
  calc
    (∑ i ∈ d.support, (v i ^ d i).totalDegree) ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
    _ ≤ P.totalDegree := le_totalDegree hd

theorem eval_affine_substitution {σ τ : Type*} (P : MvPolynomial σ ℝ)
    (v : σ → MvPolynomial τ ℝ) (q : τ → ℝ) :
    eval q (aeval v P) = eval (fun i ↦ eval q (v i)) P :=
  comp_aeval_apply v (aeval q) P

noncomputable def centeredInput {σ : Type*} (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ := aeval (fun i ↦ C 2 * X i - 1) P

noncomputable def mean {G : Type*} {m : ℕ} (x : G × Fin m → Bool) (g : G) : ℝ :=
  (∑ r, (2 * boolToReal (x (g, r)) - 1)) / m

theorem mean_to_weight {G : Type*} {m : ℕ} (hm : 0 < m)
    (x : G × Fin m → Bool) (g : G) :
    ((m : ℝ) / 2) * (mean x g + 1) = (hammingWeight (fun r ↦ x (g, r)) : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hw : (hammingWeight (fun r ↦ x (g, r)) : ℝ) =
      ∑ r, boolToReal (x (g, r)) := by
    unfold hammingWeight boolToReal
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r _
    cases hx : x (g, r) <;> simp [hx]
  rw [hw]
  simp only [mean, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem mean_permute {G : Type*} {m : ℕ} (x : G × Fin m → Bool)
    (π : G → Equiv.Perm (Fin m)) :
    mean (fun p ↦ x (p.1, π p.1 p.2)) = mean x := by
  funext g
  unfold mean
  congr 1
  exact Equiv.sum_comp (π g) (fun r ↦ 2 * boolToReal (x (g, r)) - 1)

noncomputable def centeredGroupPolynomial {G : Type*} [Fintype G] {m : ℕ}
    (P : MvPolynomial (G × Fin m) ℝ) : MvPolynomial G ℝ :=
  aeval (fun g ↦ C ((m : ℝ) / 2) * (X g + 1)) (groupPolynomial (centeredInput P))

theorem centeredGroupPolynomial_degree {G : Type*} [Fintype G] {m : ℕ}
    (P : MvPolynomial (G × Fin m) ℝ) :
    (centeredGroupPolynomial P).totalDegree ≤ P.totalDegree := by
  have hm (g : G) : (C ((m : ℝ) / 2) * (X g + 1) : MvPolynomial G ℝ).totalDegree ≤ 1 := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_add _ _).trans (by simp)
  have hz (i : G × Fin m) : (C 2 * X i - 1 : MvPolynomial (G × Fin m) ℝ).totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    have hc := totalDegree_mul (C (2 : ℝ)) (X i)
    simp only [totalDegree_C, totalDegree_X, zero_add] at hc
    simpa using hc
  exact (affine_substitution_degree _ _ hm).trans
    ((groupPolynomial_degree _).trans (affine_substitution_degree P _ hz))

theorem centeredGroupPolynomial_eval {G : Type*} [Fintype G] [DecidableEq G]
    {m : ℕ} (hm : 0 < m) (P : MvPolynomial (G × Fin m) ℝ)
    (x : G × Fin m → Bool) :
    eval (mean x) (centeredGroupPolynomial P) =
      ∑ π : G → Equiv.Perm (Fin m),
        eval (fun p : G × Fin m ↦ 2 * boolToReal (x (p.1, π p.1 p.2)) - 1) P := by
  rw [centeredGroupPolynomial, eval_affine_substitution]
  simp only [map_mul, map_add, eval_C, eval_X, map_one, mean_to_weight hm]
  rw [groupPolynomial_eval]
  apply Finset.sum_congr rfl
  intro π _
  rw [centeredInput, eval_affine_substitution]
  simp only [map_sub, map_mul, eval_C, eval_X, map_one]

/-- Strict signs of a classifier depending only on group means survive the
group averaging, including every zero-free false-labelled margin. -/
theorem centeredGroupPolynomial_strict_sign {G : Type*} [Fintype G]
    {m : ℕ} (hm : 0 < m) (P : MvPolynomial (G × Fin m) ℝ)
    (F : (G → ℝ) → Bool)
    (hP : ∀ x : G × Fin m → Bool,
      (F (mean x) = true → 0 < eval (fun p ↦ 2 * boolToReal (x p) - 1) P) ∧
      (F (mean x) = false → eval (fun p ↦ 2 * boolToReal (x p) - 1) P < 0))
    (x : G × Fin m → Bool) :
    (F (mean x) = true → 0 < eval (mean x) (centeredGroupPolynomial P)) ∧
    (F (mean x) = false → eval (mean x) (centeredGroupPolynomial P) < 0) := by
  classical
  rw [centeredGroupPolynomial_eval hm]
  constructor
  · intro hx
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro π _
    exact (hP (fun p ↦ x (p.1, π p.1 p.2))).1 (by simpa only [mean_permute] using hx)
  · intro hx
    apply Finset.sum_neg _ Finset.univ_nonempty
    intro π _
    exact (hP (fun p ↦ x (p.1, π p.1 p.2))).2 (by simpa only [mean_permute] using hx)

noncomputable def averagedGroupPolynomial {G : Type*} [Fintype G] [DecidableEq G]
    {m : ℕ} (P : MvPolynomial (G × Fin m) ℝ) : MvPolynomial G ℝ :=
  C ((Fintype.card (G → Equiv.Perm (Fin m)) : ℝ)⁻¹) * centeredGroupPolynomial P

theorem permutation_count_pos {G : Type*} [Fintype G] [DecidableEq G] (m : ℕ) :
    0 < (Fintype.card (G → Equiv.Perm (Fin m)) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem averagedGroupPolynomial_degree {G : Type*} [Fintype G] [DecidableEq G]
    {m : ℕ} (P : MvPolynomial (G × Fin m) ℝ) :
    (averagedGroupPolynomial P).totalDegree ≤ P.totalDegree := by
  have hc := totalDegree_mul (C ((Fintype.card (G → Equiv.Perm (Fin m)) : ℝ)⁻¹))
    (centeredGroupPolynomial P)
  rw [totalDegree_C, zero_add] at hc
  exact hc.trans (centeredGroupPolynomial_degree P)

theorem averagedGroupPolynomial_eval {G : Type*} [Fintype G] [DecidableEq G]
    {m : ℕ} (hm : 0 < m) (P : MvPolynomial (G × Fin m) ℝ)
    (x : G × Fin m → Bool) :
    eval (mean x) (averagedGroupPolynomial P) =
      (Fintype.card (G → Equiv.Perm (Fin m)) : ℝ)⁻¹ *
      ∑ π : G → Equiv.Perm (Fin m),
        eval (fun p : G × Fin m ↦ 2 * boolToReal (x (p.1, π p.1 p.2)) - 1) P := by
  simp only [averagedGroupPolynomial, map_mul, eval_C, centeredGroupPolynomial_eval hm]

theorem averagedGroupPolynomial_strict_sign {G : Type*} [Fintype G] [DecidableEq G]
    {m : ℕ} (hm : 0 < m) (P : MvPolynomial (G × Fin m) ℝ)
    (F : (G → ℝ) → Bool)
    (hP : ∀ x : G × Fin m → Bool,
      (F (mean x) = true → 0 < eval (fun p ↦ 2 * boolToReal (x p) - 1) P) ∧
      (F (mean x) = false → eval (fun p ↦ 2 * boolToReal (x p) - 1) P < 0))
    (x : G × Fin m → Bool) :
    (F (mean x) = true → 0 < eval (mean x) (averagedGroupPolynomial P)) ∧
    (F (mean x) = false → eval (mean x) (averagedGroupPolynomial P) < 0) := by
  have hp := inv_pos.mpr (permutation_count_pos (G := G) m)
  have hs := centeredGroupPolynomial_strict_sign hm P F hP x
  simp only [averagedGroupPolynomial, map_mul, eval_C]
  exact ⟨fun hx ↦ mul_pos hp (hs.1 hx), fun hx ↦ mul_neg_of_pos_of_neg hp (hs.2 hx)⟩

theorem mean_group_constant {G : Type*} {m : ℕ} (hm : 0 < m) (y : G → Bool) :
    mean (fun p : G × Fin m ↦ y p.1) = fun g ↦ 2 * boolToReal (y g) - 1 := by
  funext g
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- On group-constant inputs, averaging is the identity. Consequently the
averaged group polynomial and the literal replica-collapse polynomial agree
on the entire centered Boolean cube of group variables. -/
theorem averagedGroupPolynomial_group_cube {G : Type*} [Fintype G] [DecidableEq G]
    {m : ℕ} (hm : 0 < m) (P : MvPolynomial (G × Fin m) ℝ) (y : G → Bool) :
    eval (fun g ↦ 2 * boolToReal (y g) - 1) (averagedGroupPolynomial P) =
      eval (fun g ↦ 2 * boolToReal (y g) - 1) (rename Prod.fst P) := by
  rw [← mean_group_constant hm y, averagedGroupPolynomial_eval hm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [inv_mul_cancel_left₀ (permutation_count_pos (G := G) m).ne']
  rw [eval_rename, mean_group_constant hm y]
  rfl

/-- The exact top-degree squarefree coefficients of the averaged polynomial
are the corresponding coefficients of literal replica collapse. This applies
in particular to every cubic coefficient using three distinct groups. -/
theorem averagedGroupPolynomial_coeff_top_squarefree {G : Type*}
    [Fintype G] [DecidableEq G] {m : ℕ} (hm : 0 < m)
    (P : MvPolynomial (G × Fin m) ℝ) (e : G →₀ ℕ)
    (he : ∀ g, e g ≤ 1) (hP : P.totalDegree ≤ e.sum (fun _ k ↦ k)) :
    (averagedGroupPolynomial P).coeff e = (rename Prod.fst P).coeff e := by
  classical
  apply RoPECrossBlockCoefficients.coeff_eq_of_top_squarefree_cube_eval_eq _ _ e he
    ((averagedGroupPolynomial_degree P).trans hP) ((totalDegree_rename_le _ P).trans hP)
  intro z hz
  let y : G → Bool := fun g ↦ decide (z g = 1)
  have hy : (fun g ↦ 2 * boolToReal (y g) - 1) = z := by
    funext g
    rcases hz g with h | h <;> norm_num [y, boolToReal, h]
  simpa only [hy] using averagedGroupPolynomial_group_cube hm P y

end HeadComplexity.RoPEGroupSymmetrization
