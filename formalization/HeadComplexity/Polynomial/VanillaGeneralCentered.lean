import HeadComplexity.Polynomial.VanillaThreeCentered
import HeadComplexity.Polynomial.RoPEGroupSymmetrization

set_option linter.style.header false

/-!
# Actual vanilla classifiers yield strict centered factors at every head count

The original vanilla definitions are preserved. A score constant is absorbed
into one numerator after strictification. Grouped averaging preserves every
squarefree coefficient at the top degree exactly.
-/

namespace HeadComplexity.VanillaGeneralCentered

open MvPolynomial RoPECrossBlockCoefficients
open scoped BigOperators

structure Data (H : ℕ) (σ : Type*) where
  denominatorConstant : Fin H → ℝ
  numeratorConstant : Fin H → ℝ
  denominatorSlope : Fin H → σ → ℝ
  numeratorSlope : Fin H → σ → ℝ

noncomputable def Data.polynomial {H : ℕ} {σ : Type*} [Fintype σ]
    (a : Data H σ) : MvPolynomial σ ℝ :=
  ∑ h, affine (a.numeratorConstant h) (a.numeratorSlope h) *
    ∏ j ∈ Finset.univ.erase h, affine (a.denominatorConstant j) (a.denominatorSlope j)

theorem Data.totalDegree_le {H : ℕ} {σ : Type*} [Fintype σ]
    (a : Data H σ) : a.polynomial.totalDegree ≤ H := by
  classical
  apply totalDegree_finsetSum_le
  intro h _
  apply (totalDegree_mul _ _).trans
  have hN := VanillaThreeCentered.affine_totalDegree_le
    (a.numeratorConstant h) (a.numeratorSlope h)
  have hD : (∏ j ∈ Finset.univ.erase h,
      affine (a.denominatorConstant j) (a.denominatorSlope j)).totalDegree ≤ H - 1 := by
    apply (totalDegree_finsetProd _ _).trans
    calc
      (∑ j ∈ Finset.univ.erase h,
          (affine (a.denominatorConstant j) (a.denominatorSlope j)).totalDegree)
          ≤ ∑ _j ∈ Finset.univ.erase h, 1 := Finset.sum_le_sum
            (fun j _ ↦ VanillaThreeCentered.affine_totalDegree_le _ _)
      _ = H - 1 := by simp
  have hh := h.isLt
  omega

/-- Every positive-head vanilla classifier supplies actual strict factors. -/
theorem exists_data_of_vanilla {n H : ℕ} (hH : 0 < H)
    {σ : Type*} [Fintype σ] (e : σ ≃ Fin n) (f : (Fin n → Bool) → Bool)
    (hf : computableWithSharedHeadsN n H f) :
    ∃ a : Data H σ,
      (∀ h, VanillaThreeCentered.Oriented (a.denominatorSlope h)) ∧
      ∀ x : σ → Bool,
        (0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ↔
          f (fun i ↦ x (e.symm i)) = true) ∧
        eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ≠ 0 := by
  classical
  obtain ⟨r, c, hr, hclass⟩ :=
    (computableWithSharedHeadsN_iff_affineFractionComputable H f).mp hf
  obtain ⟨δ, _, hδ⟩ := exists_strict_shift (fun x ↦ c + ∑ h, (r h).eval x)
  let first : Fin H := ⟨0, hH⟩
  let shift (h : Fin H) : ℝ := if h = first then c - δ else 0
  have hshiftsum : (∑ h, shift h) = c - δ := by simp [shift]
  let N : Fin H → CubeAffine n := fun h ↦
    CubeAffine.combine 1 (r h).numForm (shift h) (r h).denForm
  let D : Fin H → CubeAffine n := fun h ↦ (r h).denForm
  let a : Data H σ := {
    denominatorConstant := fun h ↦ (D h).const + ∑ i, (D h).slope i / 2
    numeratorConstant := fun h ↦ (N h).const + ∑ i, (N h).slope i / 2
    denominatorSlope := fun h i ↦ (D h).slope (e i) / 2
    numeratorSlope := fun h i ↦ (N h).slope (e i) / 2 }
  refine ⟨a, ?_, ?_⟩
  · intro h
    rcases (hr h).2.1 with hp | hn | hz
    · exact Or.inl (fun i ↦ div_pos (hp (e i)) (by norm_num))
    · exact Or.inr (Or.inl (fun i ↦ div_neg_of_neg_of_pos (hn (e i)) (by norm_num)))
    · exact Or.inr (Or.inr (fun i ↦ by change (r h).C (e i) / 2 = 0; rw [hz, zero_div]))
  · intro x
    let y : Fin n → Bool := fun i ↦ x (e.symm i)
    have hpos (h : Fin H) : 0 < (r h).denominator y := (hr h).1 y
    have hp : 0 < ∏ h, (r h).denominator y := Finset.prod_pos (fun h _ ↦ hpos h)
    have hterm (h : Fin H) : (N h).eval y *
        (∏ j ∈ Finset.univ.erase h, (D j).eval y) =
        ((r h).eval y + shift h) * ∏ j, (r j).denominator y := by
      simp only [N, D, CubeAffine.combine_eval, one_mul,
        AffineFraction.numForm_eval, AffineFraction.denForm_eval]
      rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ (r j).denominator y)
        (Finset.mem_univ h), AffineFraction.eval]
      field_simp [(hpos h).ne']
    have he : eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial =
        ((c + ∑ h, (r h).eval y) - δ) * ∏ h, (r h).denominator y := by
      simp only [Data.polynomial, a, map_sum, map_mul, map_prod,
        VanillaThreeCentered.centered_affine_eval e (N _) x,
        VanillaThreeCentered.centered_affine_eval e (D _) x]
      change (∑ h, (N h).eval y * ∏ j ∈ Finset.univ.erase h, (D j).eval y) = _
      simp_rw [hterm]
      rw [← Finset.sum_mul, Finset.sum_add_distrib, hshiftsum]
      ring
    rw [he]
    exact ⟨(mul_pos_iff_of_pos_right hp).trans ((hδ y).1.trans (hclass y)),
      mul_ne_zero (hδ y).2 hp.ne'⟩

open RoPEGroupSymmetrization

/-- Top-degree squarefree coefficients of actual factors survive replica
averaging. The right side is the original factored polynomial with grouped
variables identified, without an assumed alternative factorization. -/
theorem averaged_top_squarefree {H m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    (hm : 0 < m) (a : Data H (G × Fin m)) (e : G →₀ ℕ)
    (he : ∀ g, e g ≤ 1) (hcard : e.sum (fun _ k ↦ k) = H) :
    coeff e (averagedGroupPolynomial a.polynomial) =
      coeff e (rename Prod.fst a.polynomial) := by
  apply averagedGroupPolynomial_coeff_top_squarefree hm a.polynomial e he
  simpa only [hcard] using a.totalDegree_le


noncomputable def Data.aggregate {H m : ℕ} {G : Type*}
    (a : Data H (G × Fin m)) : Data H G where
  denominatorConstant := a.denominatorConstant
  numeratorConstant := a.numeratorConstant
  denominatorSlope := fun h g ↦ ∑ r, a.denominatorSlope h (g, r)
  numeratorSlope := fun h g ↦ ∑ r, a.numeratorSlope h (g, r)

theorem Data.aggregate_polynomial {H m : ℕ} {G : Type*} [Fintype G]
    (a : Data H (G × Fin m)) :
    a.aggregate.polynomial = rename Prod.fst a.polynomial := by
  classical
  simp only [Data.polynomial, map_sum, map_mul, map_prod, rename_group_affine]
  rfl

theorem Data.aggregate_oriented {H m : ℕ} {G : Type*} (hm : 0 < m)
    (a : Data H (G × Fin m))
    (ha : ∀ h, VanillaThreeCentered.Oriented (a.denominatorSlope h)) :
    ∀ h, VanillaThreeCentered.Oriented (a.aggregate.denominatorSlope h) := by
  classical
  intro h
  rcases ha h with hp | hn | hz
  · left
    intro g
    exact Finset.sum_pos (fun r _ ↦ hp (g, r))
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  · right; left
    intro g
    exact Finset.sum_neg (fun r _ ↦ hn (g, r))
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  · right; right
    intro g
    simp only [Data.aggregate, hz, Finset.sum_const_zero]

/-- Actual vanilla attention supplies all generic averaging data, including
strict signs and the exact surviving factored coefficients. -/
theorem exists_averaged_data_of_vanilla {H n m : ℕ} (hH : 0 < H) (hm : 0 < m)
    (F : (Fin n → ℝ) → Bool)
    (hf : computableWithSharedHeadsN (n * m) H
      (fun x ↦ F (mean (fun p : Fin n × Fin m ↦ x (finProdFinEquiv p))))) :
    ∃ a : Data H (Fin n × Fin m),
      (∀ h, VanillaThreeCentered.Oriented (a.aggregate.denominatorSlope h)) ∧
      averagedGroupPolynomial a.polynomial ≠ 0 ∧
      (averagedGroupPolynomial a.polynomial).totalDegree ≤ H ∧
      (∀ x : Fin n × Fin m → Bool,
        (F (mean x) = true → 0 < eval (mean x) (averagedGroupPolynomial a.polynomial)) ∧
        (F (mean x) = false → eval (mean x) (averagedGroupPolynomial a.polynomial) < 0)) ∧
      (∀ e : Fin n →₀ ℕ, (∀ g, e g ≤ 1) → e.sum (fun _ k ↦ k) = H →
        coeff e (averagedGroupPolynomial a.polynomial) = coeff e a.aggregate.polynomial) := by
  classical
  obtain ⟨a, horient, hclass⟩ := exists_data_of_vanilla hH
    (finProdFinEquiv (m := n) (n := m)) _ hf
  have hc (x : Fin n × Fin m → Bool) :
      (0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ↔
        F (mean x) = true) ∧
      eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial ≠ 0 := by
    simpa only [Equiv.symm_apply_apply] using hclass x
  have hs (x : Fin n × Fin m → Bool) :
      (F (mean x) = true → 0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial) ∧
      (F (mean x) = false → eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial < 0) := by
    refine ⟨(hc x).1.mpr, fun hx ↦ ?_⟩
    have hn : ¬ 0 < eval (fun i ↦ 2 * boolToReal (x i) - 1) a.polynomial := by
      intro hp
      have := (hc x).1.mp hp
      simp only [hx, Bool.false_eq_true] at this
    exact lt_of_le_of_ne (le_of_not_gt hn) (hc x).2
  refine ⟨a, a.aggregate_oriented hm horient, ?_,
    (averagedGroupPolynomial_degree a.polynomial).trans a.totalDegree_le,
    averagedGroupPolynomial_strict_sign hm a.polynomial F hs, ?_⟩
  · intro hz
    have he := averagedGroupPolynomial_group_cube hm a.polynomial (fun _ ↦ false)
    rw [hz, map_zero, eval_rename] at he
    exact (hc (fun _ ↦ false)).2 he.symm
  · intro e he hcard
    rw [a.aggregate_polynomial]
    exact averaged_top_squarefree hm a e he hcard

end HeadComplexity.VanillaGeneralCentered
