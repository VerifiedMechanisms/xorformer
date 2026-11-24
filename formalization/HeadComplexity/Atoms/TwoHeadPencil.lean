import HeadComplexity.Results.AffineFractionNormalForm

set_option linter.style.header false

/-!
# Two affine fractions with one admissible denominator pencil

If the span of the numerator and denominator of one fraction contains a
positive affine form with strictly uniform slopes, two fractions can be
replaced by two vanilla-admissible fractions without changing any signs.
-/

namespace HeadComplexity

open scoped BigOperators

/-- An affine form on the Boolean cube, with the coefficients retained. -/
structure CubeAffine (n : ℕ) where
  const : ℝ
  slope : Fin n → ℝ

namespace CubeAffine

variable {n : ℕ}

noncomputable def eval (L : CubeAffine n) (x : Fin n → Bool) : ℝ :=
  L.const + ∑ i, L.slope i * boolToReal (x i)

noncomputable def combine (a : ℝ) (L : CubeAffine n) (b : ℝ)
    (M : CubeAffine n) : CubeAffine n :=
  ⟨a * L.const + b * M.const, fun i ↦ a * L.slope i + b * M.slope i⟩

theorem combine_eval (a : ℝ) (L : CubeAffine n) (b : ℝ)
    (M : CubeAffine n) (x : Fin n → Bool) :
    (combine a L b M).eval x = a * L.eval x + b * M.eval x := by
  simp only [combine, eval, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  ring

noncomputable def ratio (N D : CubeAffine n) : AffineFraction n :=
  ⟨N.slope, N.const, D.slope, D.const⟩

@[simp] theorem ratio_numerator (N D : CubeAffine n) (x : Fin n → Bool) :
    (ratio N D).numerator x = N.eval x := rfl

@[simp] theorem ratio_denominator (N D : CubeAffine n) (x : Fin n → Bool) :
    (ratio N D).denominator x = D.eval x := rfl

@[simp] theorem ratio_eval (N D : CubeAffine n) (x : Fin n → Bool) :
    (ratio N D).eval x = N.eval x / D.eval x := rfl

theorem ratio_admissible (N D : CubeAffine n)
    (hD : ∀ x, 0 < D.eval x)
    (hDs : (∀ i, 0 < D.slope i) ∨ (∀ i, D.slope i < 0)) :
    (ratio N D).Admissible := by
  refine ⟨hD, ?_, ?_⟩
  · exact hDs.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  · intro hz
    left
    intro i
    rcases hDs with hDs | hDs
    · exact False.elim ((ne_of_gt (hDs i)) (hz i))
    · exact False.elim ((ne_of_lt (hDs i)) (hz i))

/-- A finite collection of strict inequalities tolerates one common positive
linear perturbation. The choice is explicit and does not take a limit. -/
theorem exists_positive_perturbation {ι : Type*} [Finite ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 < a i + ε * b i := by
  classical
  letI := Fintype.ofFinite ι
  let K := 1 + ∑ i, |b i| / a i
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun i _ ↦ div_nonneg (abs_nonneg _) (ha i).le)
  refine ⟨1 / K, one_div_pos.mpr hK, ?_⟩
  intro i
  have hterm : |b i| / a i ≤ ∑ j, |b j| / a j :=
    Finset.single_le_sum (fun j _ ↦ div_nonneg (abs_nonneg _) (ha j).le)
      (Finset.mem_univ i)
  have hlt : |b i| / a i < K := by dsimp [K]; linarith
  have hprod : |b i| < K * a i := (div_lt_iff₀ (ha i)).mp hlt
  have hdiv : |b i| / K < a i := (div_lt_iff₀ hK).mpr (by nlinarith)
  have hbound : -(1 / K * b i) ≤ |b i| / K := by
    have hb := neg_le_abs (b i)
    have := mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hK).le
    simpa [div_eq_mul_inv, mul_comm] using this
  linarith

/-- Both cube positivity and one strict slope orientation are open conditions. -/
theorem exists_admissible_perturbation (F Z : CubeAffine n)
    (hF : ∀ x, 0 < F.eval x)
    (hFs : (∀ i, 0 < F.slope i) ∨ (∀ i, F.slope i < 0)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x, 0 < (combine 1 F ε Z).eval x) ∧
      ((∀ i, 0 < (combine 1 F ε Z).slope i) ∨
        (∀ i, (combine 1 F ε Z).slope i < 0)) := by
  rcases hFs with hFs | hFs
  · obtain ⟨ε, hε, hp⟩ := exists_positive_perturbation
      (Sum.elim F.slope F.eval) (Sum.elim Z.slope Z.eval)
      (fun j ↦ Sum.casesOn j hFs hF)
    refine ⟨ε, hε, ?_, Or.inl ?_⟩
    · intro x
      simpa [combine_eval] using hp (Sum.inr x)
    · intro i
      simpa [combine] using hp (Sum.inl i)
  · obtain ⟨ε, hε, hp⟩ := exists_positive_perturbation
      (Sum.elim (fun i ↦ -F.slope i) F.eval)
      (Sum.elim (fun i ↦ -Z.slope i) Z.eval)
      (fun j ↦ Sum.casesOn j (fun i ↦ neg_pos.mpr (hFs i)) hF)
    refine ⟨ε, hε, ?_, Or.inr ?_⟩
    · intro x
      simpa [combine_eval] using hp (Sum.inr x)
    · intro i
      have hi := hp (Sum.inl i)
      dsimp [combine] at *
      linarith

/-- One admissible direction in one numerator-denominator pencil suffices for
two vanilla heads. The two resulting scores need only have the same signs. -/
theorem two_products_uniform_factor (U Z F V : CubeAffine n)
    (hF : ∀ x, 0 < F.eval x)
    (hFs : (∀ i, 0 < F.slope i) ∨ (∀ i, F.slope i < 0)) :
    ∃ r : Fin 2 → AffineFraction n,
      (∀ h, (r h).Admissible) ∧ ∀ x,
      (0 < ∑ h, (r h).eval x ↔ 0 < U.eval x * Z.eval x + F.eval x * V.eval x) := by
  obtain ⟨ε, hε, hG, hGs⟩ := exists_admissible_perturbation F Z hF hFs
  let G := combine 1 F ε Z
  let A := combine (1 / ε) U 0 U
  let B := combine 1 V (-(1 / ε)) U
  let r : Fin 2 → AffineFraction n := ![ratio A F, ratio B G]
  refine ⟨r, ?_, ?_⟩
  · intro h
    fin_cases h
    · exact ratio_admissible A F hF hFs
    · exact ratio_admissible B G hG hGs
  · intro x
    have hFx : 0 < F.eval x := hF x
    have hGx : 0 < G.eval x := hG x
    have hid : F.eval x * G.eval x * (∑ h, (r h).eval x) =
        U.eval x * Z.eval x + F.eval x * V.eval x := by
      simp only [r, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ratio_eval]
      have hGe : G.eval x = F.eval x + ε * Z.eval x := by
        simp [G, combine_eval]
      have hAe : A.eval x = U.eval x / ε := by
        simp [A, combine_eval, div_eq_mul_inv, mul_comm]
      have hBe : B.eval x = V.eval x - U.eval x / ε := by
        simp [B, combine_eval, div_eq_mul_inv, sub_eq_add_neg, mul_comm]
      rw [hAe, hBe]
      field_simp
      rw [hGe]
      ring
    rw [← mul_pos_iff_of_pos_left (mul_pos hFx hGx), hid]

/-- One admissible direction in one numerator-denominator pencil suffices for
two vanilla heads. The two resulting scores need only have the same signs. -/
theorem two_head_pencil (N D M E : CubeAffine n) (t : ℝ)
    (hD : ∀ x, 0 < D.eval x) (hE : ∀ x, 0 < E.eval x)
    (hF : ∀ x, 0 < (combine 1 D t N).eval x)
    (hFs : (∀ i, 0 < (combine 1 D t N).slope i) ∨
      (∀ i, (combine 1 D t N).slope i < 0)) :
    ∃ r : Fin 2 → AffineFraction n,
      (∀ h, (r h).Admissible) ∧ ∀ x,
      (0 < ∑ h, (r h).eval x ↔ 0 < N.eval x / D.eval x + M.eval x / E.eval x) := by
  let F := combine 1 D t N
  let Z := combine 1 E (-t) M
  obtain ⟨ε, hε, hG, hGs⟩ := exists_admissible_perturbation F Z hF hFs
  let G := combine 1 F ε Z
  let A := combine (1 / ε) N 0 N
  let B := combine 1 M (-(1 / ε)) N
  let r : Fin 2 → AffineFraction n := ![ratio A F, ratio B G]
  refine ⟨r, ?_, ?_⟩
  · intro h
    fin_cases h
    · exact ratio_admissible A F hF hFs
    · exact ratio_admissible B G hG hGs
  · intro x
    have hFx : 0 < F.eval x := hF x
    have hGx : 0 < G.eval x := hG x
    have hDx : 0 < D.eval x := hD x
    have hEx : 0 < E.eval x := hE x
    have hid : F.eval x * G.eval x * (∑ h, (r h).eval x) =
        D.eval x * E.eval x * (N.eval x / D.eval x + M.eval x / E.eval x) := by
      simp only [r, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ratio_eval]
      have hFe : F.eval x = D.eval x + t * N.eval x := by
        simp [F, combine_eval]
      have hGe : G.eval x = F.eval x + ε * (E.eval x - t * M.eval x) := by
        simp [G, Z, combine_eval, sub_eq_add_neg]
      have hAe : A.eval x = N.eval x / ε := by
        simp [A, combine_eval, div_eq_mul_inv, mul_comm]
      have hBe : B.eval x = M.eval x - N.eval x / ε := by
        simp [B, combine_eval, div_eq_mul_inv, sub_eq_add_neg, mul_comm]
      rw [hAe, hBe]
      field_simp
      rw [hGe, hFe]
      ring
    rw [← mul_pos_iff_of_pos_left (mul_pos hFx hGx), hid,
      mul_pos_iff_of_pos_left (mul_pos hDx hEx)]

end CubeAffine
end HeadComplexity
