import HeadComplexity.Polynomial.DiagonalRootBound
import HeadComplexity.Polynomial.WeightedDegree

set_option linter.style.header false

/-! Diagonal root bounds using positive integer monomial weights. -/

noncomputable section
namespace HeadComplexity.PolynomialRootCount
open MvPolynomial Finset
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

noncomputable def weightedDiagonalIdeal (p : Fin n → MvPolynomial (Fin n) K)
    (e : Fin n → ℕ) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range fun i ↦ X i ^ e i - p i)

noncomputable def exponentBox (e : Fin n → ℕ) : Set (Fin n →₀ ℕ) :=
  {m | ∀ i, m i < e i}

private theorem quotient_monomial_mem (w e : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i)
    (m : Fin n →₀ ℕ) :
    (Ideal.Quotient.mkₐ K (weightedDiagonalIdeal p e)) (monomial m 1) ∈
      (restrictSupport K (exponentBox e)).map
        (Ideal.Quotient.mkₐ K (weightedDiagonalIdeal p e)).toLinearMap := by
  classical
  let q := Ideal.Quotient.mkₐ K (weightedDiagonalIdeal p e)
  let V := (restrictSupport K (exponentBox e)).map q.toLinearMap
  change q (monomial m 1) ∈ V
  induction hm : monomialWeight w m using Nat.strong_induction_on generalizing m with
  | h k ih =>
    by_cases hb : ∀ i, m i < e i
    · exact Submodule.mem_map.mpr ⟨monomial m 1,
        (monomial_mem_restrictSupport K).mpr (Or.inl hb), rfl⟩
    · push Not at hb
      obtain ⟨i, hi⟩ := hb
      let t := m - Finsupp.single i (e i)
      have hle : Finsupp.single i (e i) ≤ m := Finsupp.single_le_iff.mpr hi
      have hdecomp : t + Finsupp.single i (e i) = m := tsub_add_cancel_of_le hle
      have hrel : q (X i ^ e i) = q (p i) := by
        apply sub_eq_zero.mp
        rw [← map_sub]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.subset_span ⟨i, rfl⟩
      have heq : q (monomial m 1) = q (monomial t 1 * p i) := by
        calc
          _ = q (monomial t 1 * X i ^ e i) := by
            rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, hdecomp]
          _ = _ := by rw [map_mul, hrel, ← map_mul]
      rw [heq]
      rw [MvPolynomial.as_sum (p i)]
      rw [Finset.mul_sum, map_sum]
      apply Submodule.sum_mem
      intro a ha
      rw [monomial_mul_monomial, one_mul]
      have hsmall : monomialWeight w (t + a) < k := by
        have ha' := hp i a ha
        have hm' := congrArg (monomialWeight w) hdecomp
        rw [monomialWeight_add, monomialWeight_single, Nat.mul_comm (w i) (e i)] at hm'
        rw [monomialWeight_add, ← hm]
        omega
      have hh := ih (monomialWeight w (t + a)) hsmall (t + a) rfl
      have hc := V.smul_mem ((p i).coeff a) hh
      simpa only [← map_smul, smul_monomial, smul_eq_mul, mul_one] using hc


private theorem weighted_quotient_surjective (w e : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i) :
    Function.Surjective
      ((Ideal.Quotient.mkₐ K (weightedDiagonalIdeal p e)).toLinearMap.comp
        (restrictSupport K (exponentBox e)).subtype) := by
  classical
  let q := Ideal.Quotient.mkₐ K (weightedDiagonalIdeal p e)
  let V := (restrictSupport K (exponentBox e)).map q.toLinearMap
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (weightedDiagonalIdeal p e) z
  have hf : q f ∈ V := by
    rw [MvPolynomial.as_sum f, map_sum]
    apply Submodule.sum_mem
    intro m hm
    have hh := quotient_monomial_mem w e hw he p hp m
    have hc := V.smul_mem (f.coeff m) hh
    simpa only [← map_smul, smul_monomial, smul_eq_mul, mul_one] using hc
  obtain ⟨r, hr, heq⟩ := Submodule.mem_map.mp hf
  exact ⟨⟨r, hr⟩, heq⟩

private noncomputable def variableBoxEquiv (e : Fin n → ℕ) :
    exponentBox e ≃ (∀ i, Fin (e i)) where
  toFun s i := ⟨s.1 i, s.2 i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).val), by
    intro i
    simpa using (a i).isLt⟩
  left_inv s := by apply Subtype.ext; ext i; simp
  right_inv a := by funext i; apply Fin.ext; simp

private theorem finrank_variable_box (e : Fin n → ℕ) :
    Module.finrank K (restrictSupport K (exponentBox e)) = ∏ i, e i := by
  classical
  let E := variableBoxEquiv e
  let : Fintype (exponentBox e) := Fintype.ofEquiv (∀ i, Fin (e i)) E.symm
  rw [Module.finrank_eq_card_basis (basisRestrictSupport K (exponentBox e)),
    Fintype.card_congr E]
  simp

theorem weightedDiagonalIdeal_quotient_finite (w e : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ weightedDiagonalIdeal p e) := by
  classical
  let E := variableBoxEquiv e
  let : Fintype (exponentBox e) := Fintype.ofEquiv (∀ i, Fin (e i)) E.symm
  let : Module.Finite K (restrictSupport K (exponentBox e)) :=
    Module.Finite.of_basis (basisRestrictSupport K (exponentBox e))
  exact Module.Finite.of_surjective _ (weighted_quotient_surjective w e hw he p hp)

theorem weightedDiagonalIdeal_finrank_le (w e : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ weightedDiagonalIdeal p e) ≤ ∏ i, e i := by
  classical
  let E := variableBoxEquiv e
  let : Fintype (exponentBox e) := Fintype.ofEquiv (∀ i, Fin (e i)) E.symm
  let : Module.Finite K (restrictSupport K (exponentBox e)) :=
    Module.Finite.of_basis (basisRestrictSupport K (exponentBox e))
  have hh := LinearMap.finrank_le_finrank_of_surjective
    (weighted_quotient_surjective w e hw he p hp)
  simpa only [finrank_variable_box] using hh

def WeightedDiagonalRoot (p : Fin n → MvPolynomial (Fin n) K) (e : Fin n → ℕ) :=
  {x : Fin n → K // ∀ i, eval x (X i ^ e i - p i) = 0}

private noncomputable def weightedRootHom (p : Fin n → MvPolynomial (Fin n) K)
    (e : Fin n → ℕ) (x : WeightedDiagonalRoot p e) :
    (MvPolynomial (Fin n) K ⧸ weightedDiagonalIdeal p e) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (aeval x.1) (by
    have hker : weightedDiagonalIdeal p e ≤ RingHom.ker (aeval x.1).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact x.2 i
    exact fun _ h ↦ hker h)

private theorem weightedRootHom_injective (p : Fin n → MvPolynomial (Fin n) K)
    (e : Fin n → ℕ) : Function.Injective (weightedRootHom p e) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h
    (Ideal.Quotient.mk (weightedDiagonalIdeal p e) (X i))
  change aeval x.1 (X i) = aeval y.1 (X i) at hi
  simpa using hi

theorem weightedDiagonalRoot_finite (w e : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i) :
    Finite (WeightedDiagonalRoot p e) := by
  let := weightedDiagonalIdeal_quotient_finite w e hw he p hp
  exact Finite.of_injective _ (weightedRootHom_injective p e)

theorem weightedDiagonalRoot_card_le (w e : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i) :
    Nat.card (WeightedDiagonalRoot p e) ≤ ∏ i, e i := by
  let := weightedDiagonalIdeal_quotient_finite w e hw he p hp
  exact (Nat.card_le_card_of_injective _ (weightedRootHom_injective p e)).trans
    ((card_algHom_le_finrank K _ K).trans
      (weightedDiagonalIdeal_finrank_le w e hw he p hp))

theorem weighted_perturbed_roots_card_le {ι : Type*} [Fintype ι]
    (w e : Fin n → ℕ) (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) K)
    (hp : ∀ i m, m ∈ (p i).support → monomialWeight w m < e i * w i)
    (ε : K) (hε : ε ≠ 0) (x : ι → Fin n → K)
    (hx : Function.Injective x)
    (hroot : ∀ a i, eval (x a) (p i) + ε * x a i ^ e i = 0) :
    Fintype.card ι ≤ ∏ i, e i := by
  classical
  let q : Fin n → MvPolynomial (Fin n) K := fun i ↦ C (-ε⁻¹) * p i
  have hq (i : Fin n) (m : Fin n →₀ ℕ) (hm : m ∈ (q i).support) :
      monomialWeight w m < e i * w i := by
    apply hp i m
    have hnonzero := mem_support_iff.mp hm
    change (C (-ε⁻¹) * p i).coeff m ≠ 0 at hnonzero
    rw [coeff_C_mul] at hnonzero
    exact mem_support_iff.mpr (fun hz ↦ hnonzero (by rw [hz, mul_zero]))
  let f : ι → WeightedDiagonalRoot q e := fun a ↦ ⟨x a, fun i ↦ by
    have hr := hroot a i
    simp only [q, map_sub, map_pow, eval_X, map_mul, eval_C]
    have hh := congrArg (fun z ↦ ε⁻¹ * z) hr
    simpa [mul_add, ← mul_assoc, hε, sub_neg_eq_add, add_comm] using hh⟩
  have hf : Function.Injective f := fun a b h ↦ hx (congrArg Subtype.val h)
  let := weightedDiagonalRoot_finite w e hw he q hq
  have hh := (Nat.card_le_card_of_injective f hf).trans
    (weightedDiagonalRoot_card_le w e hw he q hq)
  simpa using hh

end HeadComplexity.PolynomialRootCount
