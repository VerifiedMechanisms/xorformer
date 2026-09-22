import HeadComplexity.Atoms.CylinderApproximation
import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Results.CalibratedThresholdVote

set_option linter.style.header false

/-!
# Raw-calibrated vote support bound

The raw calibration cost of a Boolean feature is the least fixed number of
fractional atoms that approximate its real indicator to arbitrary accuracy.
Every feature on a finite Boolean cube has finite raw cost.  Its exact
multilinear expansion gives the affine-free support upper bound, and the
costs add under a strict weighted vote.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n s : ℕ}

/-- A Boolean feature is uniformly approximable with `r` raw atoms. -/
def RawApproximableWith (r : ℕ) (T : (Fin n → Bool) → Bool) : Prop :=
  UniformlyAtomsApproximable (Fin r) (fun bits ↦ boolToReal (T bits))

namespace SquarefreePolynomial

private theorem sum_equivFin_nonlinearSupport_raw
    (P : SquarefreePolynomial n) (F : Finset (Fin n) → ℝ) :
    (∑ j : Fin P.nonlinearSupport.card,
        F ((P.nonlinearSupport.equivFin).symm j).1) =
      ∑ S ∈ P.nonlinearSupport, F S := by
  rw [← P.nonlinearSupport.sum_attach, Finset.attach_eq_univ,
    ← P.nonlinearSupport.equivFin.symm.sum_comp]

private theorem uniformlyAtomsApproximable_const_add
    {r : ℕ} {s : (Fin n → Bool) → ℝ}
    (hs : UniformlyAtomsApproximable (Fin r) s) (a : ℝ) :
    UniformlyAtomsApproximable (Fin r) (fun bits ↦ a + s bits) := by
  intro ε hε
  obtain ⟨φ, c, hφ⟩ := hs ε hε
  refine ⟨φ, a + c, fun bits ↦ ?_⟩
  have heq :
      ((a + c) + ∑ i, (φ i).eval bits) - (a + s bits) =
        (c + ∑ i, (φ i).eval bits) - s bits := by ring
  rw [heq]
  exact hφ bits

/-- The value of a squarefree polynomial is uniformly approximable using its
affine-free support cost: one atom for the complete linear part, and one atom
for every nonzero nonlinear monomial. -/
theorem uniformlyAtomsApproximable_affineFreeSupportCost
    (P : SquarefreePolynomial n) :
    UniformlyAtomsApproximable (Fin P.affineFreeSupportCost) P.eval := by
  classical
  by_cases hlin : P.HasLinearPart
  · rw [affineFreeSupportCost, if_pos hlin]
    let g : Fin (P.nonlinearSupport.card + 1) → (Fin n → Bool) → ℝ :=
      Fin.cases (affineValue 0 (fun i ↦ P.coeff {i}))
        (fun j bits ↦
          let S := ((P.nonlinearSupport.equivFin).symm j).1
          P.coeff S * squarefreeMonomial S bits)
    have hg : ∀ j, UniformlyOneAtomApproximable (g j) := by
      intro j
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · exact uniformlyOneAtomApproximable_affineValue 0
          (fun i ↦ P.coeff {i})
      · exact uniformlyOneAtomApproximable_signedMonomial
          ((P.nonlinearSupport.equivFin).symm k).1
          (P.coeff ((P.nonlinearSupport.equivFin).symm k).1)
    rw [show P.eval = fun bits ↦ P.coeff ∅ + ∑ j, g j bits by
      funext bits
      rw [show (∑ j, g j bits) = affineValue 0 (fun i ↦ P.coeff {i}) bits +
          ∑ S ∈ P.nonlinearSupport,
            P.coeff S * squarefreeMonomial S bits by
        rw [Fin.sum_univ_succ]
        change affineValue 0 (fun i ↦ P.coeff {i}) bits +
          (∑ j : Fin P.nonlinearSupport.card,
            P.coeff ((P.nonlinearSupport.equivFin).symm j).1 *
              squarefreeMonomial ((P.nonlinearSupport.equivFin).symm j).1 bits) = _
        congr 1
        exact sum_equivFin_nonlinearSupport_raw P
          (fun S ↦ P.coeff S * squarefreeMonomial S bits)]
      simp [SquarefreePolynomial.eval, add_assoc]]
    exact uniformlyAtomsApproximable_const_add
      (CubeCylinder.uniformlyAtomsApproximable_fin_sum g hg) (P.coeff ∅)
  · rw [affineFreeSupportCost, if_neg hlin, Nat.add_zero]
    let g : Fin P.nonlinearSupport.card → (Fin n → Bool) → ℝ :=
      fun j bits ↦
        let S := ((P.nonlinearSupport.equivFin).symm j).1
        P.coeff S * squarefreeMonomial S bits
    have hg : ∀ j, UniformlyOneAtomApproximable (g j) := by
      intro j
      exact uniformlyOneAtomApproximable_signedMonomial
        ((P.nonlinearSupport.equivFin).symm j).1
        (P.coeff ((P.nonlinearSupport.equivFin).symm j).1)
    have hlinear_zero : ∀ i, P.coeff {i} = 0 := by
      intro i
      by_contra hi
      exact hlin ⟨i, hi⟩
    rw [show P.eval = fun bits ↦ P.coeff ∅ + ∑ j, g j bits by
      funext bits
      rw [show (∑ j, g j bits) =
          ∑ S ∈ P.nonlinearSupport,
            P.coeff S * squarefreeMonomial S bits by
        change (∑ j : Fin P.nonlinearSupport.card,
          P.coeff ((P.nonlinearSupport.equivFin).symm j).1 *
            squarefreeMonomial ((P.nonlinearSupport.equivFin).symm j).1 bits) = _
        exact sum_equivFin_nonlinearSupport_raw P
          (fun S ↦ P.coeff S * squarefreeMonomial S bits)]
      simp [SquarefreePolynomial.eval, affineValue, hlinear_zero]]
    exact uniformlyAtomsApproximable_const_add
      (CubeCylinder.uniformlyAtomsApproximable_fin_sum g hg) (P.coeff ∅)

end SquarefreePolynomial

/-- The multilinear point indicator before squarefree reduction. -/
noncomputable def booleanPointPolynomial (target : Fin n → Bool) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, if target i then X i else C 1 - X i

theorem eval_booleanPointPolynomial (target bits : Fin n → Bool) :
    MvPolynomial.eval (cubePoint bits) (booleanPointPolynomial target) =
      if bits = target then 1 else 0 := by
  classical
  rw [booleanPointPolynomial, map_prod]
  by_cases h : bits = target
  · subst bits
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    cases hi : target i <;> simp [hi, cubePoint, boolToReal]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, bits i ≠ target i := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases ht : target i <;> cases hb : bits i <;>
      simp_all [cubePoint, boolToReal]

/-- A truth-table interpolation polynomial for a Boolean feature. -/
noncomputable def exactBooleanMvPolynomial (T : (Fin n → Bool) → Bool) :
    MvPolynomial (Fin n) ℝ :=
  ∑ target, C (boolToReal (T target)) * booleanPointPolynomial target

theorem eval_exactBooleanMvPolynomial
    (T : (Fin n → Bool) → Bool) (bits : Fin n → Bool) :
    MvPolynomial.eval (cubePoint bits) (exactBooleanMvPolynomial T) =
      boolToReal (T bits) := by
  classical
  rw [exactBooleanMvPolynomial, map_sum]
  simp_rw [map_mul, eval_C, eval_booleanPointPolynomial]
  simp

/-- The exact canonical squarefree expansion of a Boolean feature. -/
noncomputable def exactBooleanSquarefreePolynomial
    (T : (Fin n → Bool) → Bool) : SquarefreePolynomial n :=
  SquarefreePolynomial.ofMvPolynomial (exactBooleanMvPolynomial T)

theorem exactBooleanSquarefreePolynomial_eval
    (T : (Fin n → Bool) → Bool) (bits : Fin n → Bool) :
    (exactBooleanSquarefreePolynomial T).eval bits = boolToReal (T bits) := by
  rw [exactBooleanSquarefreePolynomial,
    SquarefreePolynomial.ofMvPolynomial_eval,
    eval_exactBooleanMvPolynomial]

/-- The exact affine-free support cost of the canonical multilinear expansion
of `T`. -/
noncomputable def exactAffineFreeSupportCost
    (T : (Fin n → Bool) → Bool) : ℕ :=
  (exactBooleanSquarefreePolynomial T).affineFreeSupportCost

private theorem exists_rawApproximableWith
    (T : (Fin n → Bool) → Bool) :
    ∃ r, RawApproximableWith r T := by
  refine ⟨exactAffineFreeSupportCost T, ?_⟩
  change UniformlyAtomsApproximable
    (Fin (exactBooleanSquarefreePolynomial T).affineFreeSupportCost)
    (fun bits ↦ boolToReal (T bits))
  intro ε hε
  obtain ⟨φ, c, hφ⟩ :=
    (exactBooleanSquarefreePolynomial T).uniformlyAtomsApproximable_affineFreeSupportCost
      ε hε
  refine ⟨φ, c, fun bits ↦ ?_⟩
  change |(c + ∑ i, (φ i).eval bits) - boolToReal (T bits)| < ε
  rw [← exactBooleanSquarefreePolynomial_eval T bits]
  exact hφ bits

/-- Raw calibration cost.  This is the least finite atom count giving
arbitrarily accurate uniform approximations.  The finite-cube interpolation
above proves that the infinity case from the paper definition never occurs. -/
noncomputable def rawCalibrationCost (T : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_rawApproximableWith T)

/-- The minimum raw calibration cost is attained. -/
theorem rawCalibrationCost_spec (T : (Fin n → Bool) → Bool) :
    RawApproximableWith (rawCalibrationCost T) T := by
  classical
  exact Nat.find_spec (exists_rawApproximableWith T)

/-- Minimality of the raw calibration cost. -/
theorem rawCalibrationCost_le (T : (Fin n → Bool) → Bool) {r : ℕ}
    (h : RawApproximableWith r T) : rawCalibrationCost T ≤ r := by
  classical
  exact Nat.find_min' (exists_rawApproximableWith T) h

/-- Exact affine-free support controls raw calibration cost. -/
theorem rawCalibrationCost_le_exactAffineFreeSupportCost
    (T : (Fin n → Bool) → Bool) :
    rawCalibrationCost T ≤ exactAffineFreeSupportCost T := by
  apply rawCalibrationCost_le
  change UniformlyAtomsApproximable
    (Fin (exactBooleanSquarefreePolynomial T).affineFreeSupportCost)
    (fun bits ↦ boolToReal (T bits))
  intro ε hε
  obtain ⟨φ, c, hφ⟩ :=
    (exactBooleanSquarefreePolynomial T).uniformlyAtomsApproximable_affineFreeSupportCost
      ε hε
  refine ⟨φ, c, fun bits ↦ ?_⟩
  change |(c + ∑ i, (φ i).eval bits) - boolToReal (T bits)| < ε
  rw [← exactBooleanSquarefreePolynomial_eval T bits]
  exact hφ bits

/-- Raw cost is bounded by the affine-free support cost of any exact
squarefree expansion. -/
theorem rawCalibrationCost_le_of_exactPolynomial
    (T : (Fin n → Bool) → Bool) (P : SquarefreePolynomial n)
    (hP : ∀ bits, P.eval bits = boolToReal (T bits)) :
    rawCalibrationCost T ≤ P.affineFreeSupportCost := by
  apply rawCalibrationCost_le
  intro ε hε
  obtain ⟨φ, c, hφ⟩ :=
    P.uniformlyAtomsApproximable_affineFreeSupportCost ε hε
  refine ⟨φ, c, fun bits ↦ ?_⟩
  change |(c + ∑ i, (φ i).eval bits) - boolToReal (T bits)| < ε
  rw [← hP bits]
  exact hφ bits

private theorem uniformlyAtomsApproximable_scale
    {r : ℕ} {g : (Fin n → Bool) → ℝ}
    (hg : UniformlyAtomsApproximable (Fin r) g) (a : ℝ) (ha : a ≠ 0) :
    UniformlyAtomsApproximable (Fin r) (fun bits ↦ a * g bits) := by
  intro ε hε
  have habs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨φ, c, hφ⟩ := hg (ε / |a|) (div_pos hε habs)
  refine ⟨fun i ↦ (φ i).scale a, a * c, fun bits ↦ ?_⟩
  simp_rw [FracAtom.scale_eval]
  rw [← Finset.mul_sum]
  have heq :
      (a * c + a * ∑ i, (φ i).eval bits) - a * g bits =
        a * ((c + ∑ i, (φ i).eval bits) - g bits) := by ring
  rw [heq, abs_mul]
  calc
    |a| * |(c + ∑ i, (φ i).eval bits) - g bits| <
        |a| * (ε / |a|) := mul_lt_mul_of_pos_left (hφ bits) habs
    _ = ε := by field_simp

/-- Sum of raw feature costs charged only to nonzero vote weights. -/
noncomputable def rawVoteCost
    (T : Fin s → (Fin n → Bool) → Bool) (c : Fin s → ℝ) : ℕ :=
  ∑ j, if c j = 0 then 0 else rawCalibrationCost (T j)

/-- **Raw-calibrated vote support bound.** A strict weighted vote costs the
sum of the raw calibration costs of its active features. -/
theorem HStar_thresholdVote_le_rawVoteCost
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ)
    (hmargin : 0 < thresholdVoteMargin T c₀ c) :
    HStar n (thresholdVote T c₀ c) ≤ rawVoteCost T c := by
  classical
  let I : Fin s → Type := fun j ↦
    Fin (if c j = 0 then 0 else rawCalibrationCost (T j))
  let g : Fin s → (Fin n → Bool) → ℝ :=
    fun j bits ↦ c j * boolToReal (T j bits)
  have hg : ∀ j, UniformlyAtomsApproximable (I j) (g j) := by
    intro j
    by_cases hj : c j = 0
    · change UniformlyAtomsApproximable
        (Fin (if c j = 0 then 0 else rawCalibrationCost (T j)))
        (fun bits ↦ c j * boolToReal (T j bits))
      rw [if_pos hj]
      simpa [hj] using
        (CubeCylinder.uniformlyAtomsApproximable_const (n := n) 0)
    · change UniformlyAtomsApproximable
        (Fin (if c j = 0 then 0 else rawCalibrationCost (T j)))
        (fun bits ↦ c j * boolToReal (T j bits))
      rw [if_neg hj]
      exact uniformlyAtomsApproximable_scale
        (rawCalibrationCost_spec (T j)) (c j) hj
  have hstrict : StrictSignRepresentsScore
      (fun bits ↦ c₀ + ∑ j, g j bits) (thresholdVote T c₀ c) := by
    intro bits
    have hscore : c₀ + ∑ j, g j bits = thresholdVoteScore T c₀ c bits := by
      rfl
    change (0 < c₀ + ∑ j, g j bits ↔ thresholdVote T c₀ c bits = true) ∧
      c₀ + ∑ j, g j bits ≠ 0
    rw [hscore]
    constructor
    · simp [thresholdVote]
    · intro hzero
      have hle := thresholdVoteMargin_le_abs_score T c₀ c bits
      rw [hzero, abs_zero] at hle
      linarith
  have hcomp := computableWithHeadsCard_of_uniformlyAtomsApproximable
    (I := I) g hg c₀ hstrict
  apply HStar_le_of_computableWithHeadsN at hcomp
  have hcard : Fintype.card (Sigma I) = rawVoteCost T c := by
    rw [Fintype.card_sigma]
    simp [I, rawVoteCost]
  rwa [hcard] at hcomp

/-- Sum of exact affine-free support costs of active vote features. -/
noncomputable def exactAffineFreeVoteCost
    (T : Fin s → (Fin n → Bool) → Bool) (c : Fin s → ℝ) : ℕ :=
  ∑ j, if c j = 0 then 0 else exactAffineFreeSupportCost (T j)

/-- Exact multilinear sparsity fallback for a strict weighted vote. -/
theorem HStar_thresholdVote_le_exactAffineFreeVoteCost
    (T : Fin s → (Fin n → Bool) → Bool) (c₀ : ℝ) (c : Fin s → ℝ)
    (hmargin : 0 < thresholdVoteMargin T c₀ c) :
    HStar n (thresholdVote T c₀ c) ≤ exactAffineFreeVoteCost T c := by
  refine (HStar_thresholdVote_le_rawVoteCost T c₀ c hmargin).trans ?_
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : c j = 0
  · simp [hj]
  · simp [hj, rawCalibrationCost_le_exactAffineFreeSupportCost]

end HeadComplexity
