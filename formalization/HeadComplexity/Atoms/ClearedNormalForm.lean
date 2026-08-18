import HeadComplexity.Atoms.AtomPolynomials
import HeadComplexity.Atoms.FracAtomHead
import HeadComplexity.Atoms.HeadToFracAtom

set_option linter.style.header false

/-!
# Cleared normal forms for fractional atoms

This module refines the model-to-polynomial bridge.  Clearing the positive
denominators of `H` fractional atoms does not merely produce a polynomial of
degree at most `H`: it produces a polynomial with a distinguished
sum-of-products factorization by affine numerator and denominator polynomials.

`ClearedAtomRep` remembers the full atom data and is exactly equivalent to
`fracComputable`, hence also to `computableWithHeadsN`.  `ClearedAffineRep`
forgets the atom-specific parameter constraints while retaining affine factors
and positivity of every denominator on the Boolean cube.  It is therefore a
useful relaxation for lower bounds based on rank, tensor, or factorization
obstructions.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

/-- The common positive denominator used to clear a family of atoms. -/
noncomputable def atomDenProduct (φ : Fin H → FracAtom n) :
    MvPolynomial (Fin n) ℝ :=
  ∏ h, (φ h).denPoly

/-- The polynomial obtained by clearing all atom denominators. -/
noncomputable def clearedAtomPoly (φ : Fin H → FracAtom n) (c : ℝ) :
    MvPolynomial (Fin n) ℝ :=
  C c * atomDenProduct φ +
    ∑ h, (φ h).numPoly * ∏ g ∈ Finset.univ.erase h, (φ g).denPoly

/-- An exact structured polynomial certificate for `H` fractional atoms. -/
def ClearedAtomRep (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (φ : Fin H → FracAtom n) (c : ℝ), SignRepresents (clearedAtomPoly φ c) f

theorem atomDenProduct_eval_pos (φ : Fin H → FracAtom n)
    (x : Fin n → Bool) :
    0 < MvPolynomial.eval (cubePoint x) (atomDenProduct φ) := by
  simp only [atomDenProduct, map_prod]
  exact Finset.prod_pos (fun h _ => (φ h).denPoly_pos x)

/-- Clearing denominators multiplies the fractional score by a positive factor. -/
theorem clearedAtomPoly_eval (φ : Fin H → FracAtom n) (c : ℝ)
    (x : Fin n → Bool) :
    MvPolynomial.eval (cubePoint x) (clearedAtomPoly φ c) =
      MvPolynomial.eval (cubePoint x) (atomDenProduct φ) *
        (c + ∑ h, (φ h).eval x) := by
  classical
  simp only [clearedAtomPoly, atomDenProduct, map_add, map_mul, map_sum, map_prod, eval_C]
  let D : Fin H → ℝ := fun h => MvPolynomial.eval (cubePoint x) (φ h).denPoly
  let N : Fin H → ℝ := fun h => MvPolynomial.eval (cubePoint x) (φ h).numPoly
  have hD : ∀ h, 0 < D h := fun h => (φ h).denPoly_pos x
  have hfrac : ∀ h, (φ h).eval x = N h / D h := by
    intro h
    exact (φ h).eval_eq_numPoly_div_denPoly x
  simp only [D, N] at hD hfrac ⊢
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [hfrac h]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun g => MvPolynomial.eval (cubePoint x) (φ g).denPoly) (Finset.mem_univ h)]
    field_simp [(hD h).ne']

/-- Exact equivalence between fractional computation and the cleared atom normal form. -/
theorem fracComputable_iff_clearedAtomRep
    (f : (Fin n → Bool) → Bool) :
    fracComputable n H f ↔ ClearedAtomRep n H f := by
  constructor
  · rintro ⟨φ, c, hsign⟩
    refine ⟨φ, c, fun x => ?_⟩
    rw [clearedAtomPoly_eval φ c x]
    rw [mul_pos_iff_of_pos_left (atomDenProduct_eval_pos φ x)]
    exact hsign x
  · rintro ⟨φ, c, hsign⟩
    refine ⟨φ, c, fun x => ?_⟩
    have hs := hsign x
    rw [clearedAtomPoly_eval φ c x,
      mul_pos_iff_of_pos_left (atomDenProduct_eval_pos φ x)] at hs
    exact hs

/-- Exact equivalence between attention computation and the cleared atom normal form. -/
theorem computableWithHeadsN_iff_clearedAtomRep
    (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H f ↔ ClearedAtomRep n H f := by
  constructor
  · intro h
    exact (fracComputable_iff_clearedAtomRep f).mp (fracComputable_of_computable h)
  · intro h
    exact computable_of_fracComputable ((fracComputable_iff_clearedAtomRep f).mpr h)

/-- A fractional certificate can be shifted so its score is strictly positive
on true inputs and strictly negative on false inputs. -/
theorem exists_strict_fracCertificate
    {f : (Fin n → Bool) → Bool} (hf : fracComputable n H f) :
    ∃ (phi : Fin H → FracAtom n) (c : ℝ),
      ∀ x : Fin n → Bool,
        if f x then 0 < c + ∑ h, (phi h).eval x
        else c + ∑ h, (phi h).eval x < 0 := by
  classical
  rcases hf with ⟨phi, c, hphi⟩
  let score : (Fin n → Bool) → ℝ := fun x ↦ c + ∑ h, (phi h).eval x
  let trueInputs : Finset (Fin n → Bool) :=
    Finset.univ.filter fun x ↦ f x = true
  by_cases hT : trueInputs.Nonempty
  · let margin : ℝ := trueInputs.inf' hT score / 2
    have hmargin_pos : 0 < margin := by
      apply half_pos
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact (hphi x).mpr (Finset.mem_filter.mp hx).2
    refine ⟨phi, c - margin, fun x ↦ ?_⟩
    have hrewrite : c - margin + ∑ h, (phi h).eval x = score x - margin := by
      dsimp [score]
      ring
    rw [hrewrite]
    cases hfx : f x with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hnpos : score x ≤ 0 := by
          apply le_of_not_gt
          intro hpos
          have := (hphi x).mp hpos
          simp [hfx] at this
        linarith
    | true =>
        simp only [↓reduceIte]
        have hxT : x ∈ trueInputs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩
        have hle : trueInputs.inf' hT score ≤ score x :=
          Finset.inf'_le score hxT
        dsimp [margin] at hmargin_pos ⊢
        linarith
  · refine ⟨phi, c - 1, fun x ↦ ?_⟩
    have hfalse : f x = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hx
      exact hT ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
    have hnpos : score x ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have := (hphi x).mp hpos
      simp [hfalse] at this
    have hrewrite : c - 1 + ∑ h, (phi h).eval x = score x - 1 := by
      dsimp [score]
      ring
    rw [hrewrite]
    linarith

theorem atomDenProduct_totalDegree_le (φ : Fin H → FracAtom n) :
    (atomDenProduct φ).totalDegree ≤ H := by
  unfold atomDenProduct
  simpa using (totalDegree_prod_le_card Finset.univ (fun h => (φ h).denPoly)
    (fun h => (φ h).denPoly_totalDegree_le))

/-- The exact cleared normal form has total degree at most its number of atoms. -/
theorem clearedAtomPoly_totalDegree_le (φ : Fin H → FracAtom n) (c : ℝ) :
    (clearedAtomPoly φ c).totalDegree ≤ H := by
  classical
  unfold clearedAtomPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, Nat.zero_add]
    exact atomDenProduct_totalDegree_le φ
  · refine totalDegree_finsetSum_le (fun h _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have hprod : (∏ g ∈ Finset.univ.erase h, (φ g).denPoly).totalDegree ≤ H - 1 := by
      refine (totalDegree_prod_le_card (Finset.univ.erase h)
        (fun g => (φ g).denPoly) (fun g => (φ g).denPoly_totalDegree_le)).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin]
    have hH : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact h.elim0)
    have := Nat.add_le_add (φ h).numPoly_totalDegree_le hprod
    omega

/-- A relaxation retaining affine numerators, positive affine denominators, and
the cleared factorization, but forgetting the parameter constraints of atoms. -/
structure AffineFractionFamily (n H : ℕ) where
  num : Fin H → MvPolynomial (Fin n) ℝ
  den : Fin H → MvPolynomial (Fin n) ℝ
  num_degree : ∀ h, (num h).totalDegree ≤ 1
  den_degree : ∀ h, (den h).totalDegree ≤ 1
  den_pos : ∀ h x, 0 < MvPolynomial.eval (cubePoint x) (den h)

/-- The polynomial obtained by clearing an abstract affine fraction family. -/
noncomputable def clearedAffinePoly (A : AffineFractionFamily n H) (c : ℝ) :
    MvPolynomial (Fin n) ℝ :=
  C c * ∏ h, A.den h +
    ∑ h, A.num h * ∏ g ∈ Finset.univ.erase h, A.den g

/-- A relaxed structured polynomial certificate with positive affine denominators. -/
def ClearedAffineRep (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (A : AffineFractionFamily n H) (c : ℝ),
    SignRepresents (clearedAffinePoly A c) f

theorem clearedAffinePoly_totalDegree_le (A : AffineFractionFamily n H) (c : ℝ) :
    (clearedAffinePoly A c).totalDegree ≤ H := by
  classical
  unfold clearedAffinePoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, Nat.zero_add]
    simpa using (totalDegree_prod_le_card Finset.univ A.den A.den_degree)
  · refine totalDegree_finsetSum_le (fun h _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have hprod : (∏ g ∈ Finset.univ.erase h, A.den g).totalDegree ≤ H - 1 := by
      refine (totalDegree_prod_le_card (Finset.univ.erase h) A.den A.den_degree).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin]
    have hH : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact h.elim0)
    have := Nat.add_le_add (A.num_degree h) hprod
    omega

/-- Forgetting the factorization gives the ordinary threshold-degree certificate. -/
theorem thresholdDegLE_of_clearedAffineRep
    {f : (Fin n → Bool) → Bool}
    (hf : ClearedAffineRep n H f) : ThresholdDegLE f H := by
  obtain ⟨A, c, hsign⟩ := hf
  exact ⟨clearedAffinePoly A c, clearedAffinePoly_totalDegree_le A c, hsign⟩

/-- Absorb the global bias into one numerator. -/
noncomputable def AffineFractionFamily.absorbBias
    (A : AffineFractionFamily n H) (c : ℝ) (h0 : Fin H) :
    Fin H → MvPolynomial (Fin n) ℝ :=
  Function.update A.num h0 (A.num h0 + C c * A.den h0)

theorem AffineFractionFamily.absorbBias_degree
    (A : AffineFractionFamily n H) (c : ℝ) (h0 h : Fin H) :
    (A.absorbBias c h0 h).totalDegree ≤ 1 := by
  classical
  by_cases hh : h = h0
  · subst h
    simp only [absorbBias, Function.update_self]
    refine (totalDegree_add _ _).trans (max_le (A.num_degree h0) ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, Nat.zero_add]
    exact A.den_degree h0
  · simp [absorbBias, hh, A.num_degree h]

/-- For a nonempty family, bias absorption exposes a sum of `H` products of
exactly `H` affine forms. -/
theorem clearedAffinePoly_eq_sum_absorbBias
    (A : AffineFractionFamily n H) (c : ℝ) (h0 : Fin H) :
    clearedAffinePoly A c =
      ∑ h, A.absorbBias c h0 h * ∏ g ∈ Finset.univ.erase h, A.den g := by
  classical
  let T : Fin H → MvPolynomial (Fin n) ℝ :=
    fun h => A.num h * ∏ g ∈ Finset.univ.erase h, A.den g
  rw [show (∑ h, A.absorbBias c h0 h * ∏ g ∈ Finset.univ.erase h, A.den g) =
      (A.num h0 + C c * A.den h0) * ∏ g ∈ Finset.univ.erase h0, A.den g +
        ∑ h ∈ Finset.univ.erase h0, T h by
    rw [← Finset.add_sum_erase Finset.univ
      (fun h => A.absorbBias c h0 h * ∏ g ∈ Finset.univ.erase h, A.den g)
      (Finset.mem_univ h0)]
    congr 1
    · simp [AffineFractionFamily.absorbBias]
    · refine Finset.sum_congr rfl (fun h hh => ?_)
      simp [AffineFractionFamily.absorbBias, T, Finset.ne_of_mem_erase hh]]
  unfold clearedAffinePoly
  rw [show (∑ h, A.num h * ∏ g ∈ Finset.univ.erase h, A.den g) =
      T h0 + ∑ h ∈ Finset.univ.erase h0, T h by
    rw [← Finset.add_sum_erase Finset.univ T (Finset.mem_univ h0)]]
  rw [show (∏ h, A.den h) = A.den h0 * ∏ g ∈ Finset.univ.erase h0, A.den g by
    exact (Finset.mul_prod_erase Finset.univ A.den (Finset.mem_univ h0)).symm]
  simp only [T]
  ring

/-- Forget the atom-specific parameter constraints while retaining its affine
numerator and positive affine denominator. -/
noncomputable def FracAtom.affineFamily (φ : Fin H → FracAtom n) :
    AffineFractionFamily n H where
  num := fun h => (φ h).numPoly
  den := fun h => (φ h).denPoly
  num_degree := fun h => (φ h).numPoly_totalDegree_le
  den_degree := fun h => (φ h).denPoly_totalDegree_le
  den_pos := fun h x => (φ h).denPoly_pos x

@[simp] theorem clearedAffinePoly_affineFamily
    (φ : Fin H → FracAtom n) (c : ℝ) :
    clearedAffinePoly (FracAtom.affineFamily φ) c = clearedAtomPoly φ c := by
  rfl

/-- Every exact atom certificate is a relaxed affine-factor certificate. -/
theorem clearedAffineRep_of_fracComputable
    {f : (Fin n → Bool) → Bool}
    (hf : fracComputable n H f) : ClearedAffineRep n H f := by
  obtain ⟨φ, c, hsign⟩ := (fracComputable_iff_clearedAtomRep f).mp hf
  exact ⟨FracAtom.affineFamily φ, c, by simpa using hsign⟩

/-- A factorization obstruction rules out an `H`-atom computation. -/
theorem not_fracComputable_of_no_clearedAffineRep
    {f : (Fin n → Bool) → Bool}
    (hobs : ¬ ClearedAffineRep n H f) : ¬ fracComputable n H f :=
  fun hf => hobs (clearedAffineRep_of_fracComputable hf)

/-- A factorization obstruction rules out an `H`-head attention computation. -/
theorem not_computableWithHeadsN_of_no_clearedAffineRep
    {f : (Fin n → Bool) → Bool}
    (hobs : ¬ ClearedAffineRep n H f) : ¬ computableWithHeadsN n H f :=
  fun hf => hobs (clearedAffineRep_of_fracComputable (fracComputable_of_computable hf))

end HeadComplexity
