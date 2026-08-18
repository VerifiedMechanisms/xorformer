import HeadComplexity.Atoms.UniformApproximation
import HeadComplexity.Polynomial.UnivariateReduction
import HeadComplexity.Results.ThresholdDegree
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Affine-free polynomial-threshold sparsity

Squarefree polynomials are represented by coefficients indexed by coordinate
sets. Their affine-free support cost charges all nonzero linear coefficients
together as one affine head, then charges one head per nonlinear monomial.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- A squarefree real polynomial, in the canonical subset-indexed basis. -/
structure SquarefreePolynomial (n : ℕ) where
  coeff : Finset (Fin n) → ℝ

namespace SquarefreePolynomial

/-- Nonlinear support, consisting of nonzero monomials of degree at least two. -/
noncomputable def nonlinearSupport (P : SquarefreePolynomial n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ 2 ≤ S.card ∧ P.coeff S ≠ 0

/-- Nonconstant support, used for ordinary PTF sparsity. -/
noncomputable def nonconstantSupport (P : SquarefreePolynomial n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ S.Nonempty ∧ P.coeff S ≠ 0

/-- Whether the polynomial has at least one nonzero linear coefficient. -/
def HasLinearPart (P : SquarefreePolynomial n) : Prop :=
  ∃ i, P.coeff {i} ≠ 0

/-- Affine-free support cost: one for the whole linear part when present, plus
one per nonlinear monomial. -/
noncomputable def affineFreeSupportCost (P : SquarefreePolynomial n) : ℕ :=
  by
    classical
    exact P.nonlinearSupport.card + if P.HasLinearPart then 1 else 0

/-- Ordinary nonconstant-monomial support cost. -/
noncomputable def ptfSupportCost (P : SquarefreePolynomial n) : ℕ :=
  P.nonconstantSupport.card

/-- Evaluation in canonical form: constant term, full affine part, then the
nonzero nonlinear support. -/
noncomputable def eval (P : SquarefreePolynomial n) (bits : Fin n → Bool) : ℝ :=
  P.coeff ∅ + affineValue 0 (fun i ↦ P.coeff {i}) bits +
    ∑ S ∈ P.nonlinearSupport, P.coeff S * squarefreeMonomial S bits

/-- The repository's polynomial-threshold convention: positive exactly on
true inputs, with zero allowed on false inputs. -/
def SignRepresents (P : SquarefreePolynomial n)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ bits, 0 < P.eval bits ↔ f bits = true

/-- Strict sign representation by a squarefree polynomial. -/
def StrictSignRepresents (P : SquarefreePolynomial n)
    (f : (Fin n → Bool) → Bool) : Prop :=
  StrictSignRepresentsScore P.eval f

theorem StrictSignRepresents.signRepresents
    {P : SquarefreePolynomial n} {f : (Fin n → Bool) → Bool}
    (hP : P.StrictSignRepresents f) : P.SignRepresents f :=
  fun bits ↦ (hP bits).1

private theorem full_sum_partition (c q : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), c S * q S) =
      c ∅ * q ∅ + (∑ i : Fin n, c {i} * q {i}) +
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
          2 ≤ S.card ∧ c S ≠ 0), c S * q S := by
  classical
  let term : Finset (Fin n) → ℝ := fun S ↦ c S * q S
  let all : Finset (Finset (Fin n)) := Finset.univ
  have hsplitLow :
      (∑ S ∈ all.filter (fun S ↦ S.card ≤ 1), term S) =
        term ∅ + ∑ i : Fin n, term {i} := by
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (all.filter (fun S ↦ S.card ≤ 1)) (fun S ↦ S.card = 0) term
    have hzero :
        (∑ S ∈ (all.filter (fun S ↦ S.card ≤ 1)).filter
          (fun S ↦ S.card = 0), term S) = term ∅ := by
      have hset : (all.filter (fun S ↦ S.card ≤ 1)).filter
          (fun S ↦ S.card = 0) = {∅} := by
        ext S
        constructor
        · intro h
          simp only [Finset.mem_filter] at h
          exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp h.2)
        · intro h
          simp only [Finset.mem_singleton] at h
          subst S
          simp [all]
      rw [hset]
      simp
    have hone :
        (∑ S ∈ (all.filter (fun S ↦ S.card ≤ 1)).filter
          (fun S ↦ S.card ≠ 0), term S) = ∑ i : Fin n, term {i} := by
      have hset : (all.filter (fun S ↦ S.card ≤ 1)).filter
          (fun S ↦ S.card ≠ 0) =
          (Finset.univ : Finset (Fin n)).image (fun i ↦ {i}) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · rintro ⟨hcard, hne⟩
          have hcard1 : S.card = 1 := by omega
          obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard1
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          simp [all]
      rw [hset, Finset.sum_image Finset.singleton_injective.injOn]
    rw [hzero, hone] at hpartition
    exact hpartition.symm
  have hsplitHigh :
      (∑ S ∈ all.filter (fun S ↦ ¬ S.card ≤ 1), term S) =
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
          2 ≤ S.card ∧ c S ≠ 0), term S := by
    symm
    apply Finset.sum_subset
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.mem_filter]
      exact ⟨by simp [all], by omega⟩
    · intro S hS hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hnot
      push Not at hnot
      simp [term, hnot (by omega)]
  have hpartition := Finset.sum_filter_add_sum_filter_not all
    (fun S ↦ S.card ≤ 1) term
  rw [hsplitLow, hsplitHigh] at hpartition
  simpa [term, all] using hpartition.symm

/-- Canonical evaluation agrees with the full squarefree subset sum. -/
theorem fullSum_eq_eval (P : SquarefreePolynomial n) (bits : Fin n → Bool) :
    (∑ S : Finset (Fin n), P.coeff S * squarefreeMonomial S bits) = P.eval bits := by
  rw [full_sum_partition]
  simp [SquarefreePolynomial.eval, SquarefreePolynomial.nonlinearSupport,
    squarefreeMonomial, affineValue]

/-- Change only the constant coefficient. -/
noncomputable def shiftConstant (P : SquarefreePolynomial n) (ε : ℝ) :
    SquarefreePolynomial n :=
  ⟨fun S ↦ if S = ∅ then P.coeff ∅ - ε else P.coeff S⟩

@[simp] theorem shiftConstant_coeff_empty
    (P : SquarefreePolynomial n) (ε : ℝ) :
    (P.shiftConstant ε).coeff ∅ = P.coeff ∅ - ε := by
  simp [shiftConstant]

@[simp] theorem shiftConstant_coeff_of_nonempty
    (P : SquarefreePolynomial n) (ε : ℝ) {S : Finset (Fin n)}
    (hS : S.Nonempty) :
    (P.shiftConstant ε).coeff S = P.coeff S := by
  simp [shiftConstant, hS.ne_empty]

theorem shiftConstant_nonlinearSupport
    (P : SquarefreePolynomial n) (ε : ℝ) :
    (P.shiftConstant ε).nonlinearSupport = P.nonlinearSupport := by
  ext S
  simp only [nonlinearSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcard, hcoeff⟩
    exact ⟨hcard, by
      simpa [shiftConstant,
        (Finset.card_pos.mp (by omega : 0 < S.card)).ne_empty] using hcoeff⟩
  · rintro ⟨hcard, hcoeff⟩
    exact ⟨hcard, by
      simpa [shiftConstant,
        (Finset.card_pos.mp (by omega : 0 < S.card)).ne_empty] using hcoeff⟩

theorem shiftConstant_nonconstantSupport
    (P : SquarefreePolynomial n) (ε : ℝ) :
    (P.shiftConstant ε).nonconstantSupport = P.nonconstantSupport := by
  ext S
  simp only [nonconstantSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hS, hcoeff⟩
    exact ⟨hS, by simpa [shiftConstant, hS.ne_empty] using hcoeff⟩
  · rintro ⟨hS, hcoeff⟩
    exact ⟨hS, by simpa [shiftConstant, hS.ne_empty] using hcoeff⟩

theorem shiftConstant_HasLinearPart
    (P : SquarefreePolynomial n) (ε : ℝ) :
    (P.shiftConstant ε).HasLinearPart ↔ P.HasLinearPart := by
  simp [HasLinearPart, shiftConstant]

theorem shiftConstant_affineFreeSupportCost
    (P : SquarefreePolynomial n) (ε : ℝ) :
    (P.shiftConstant ε).affineFreeSupportCost = P.affineFreeSupportCost := by
  rw [affineFreeSupportCost, affineFreeSupportCost,
    shiftConstant_nonlinearSupport]
  by_cases hlin : P.HasLinearPart
  · rw [if_pos hlin, if_pos ((shiftConstant_HasLinearPart P ε).mpr hlin)]
  · rw [if_neg hlin,
      if_neg (fun h ↦ hlin ((shiftConstant_HasLinearPart P ε).mp h))]

theorem shiftConstant_ptfSupportCost
    (P : SquarefreePolynomial n) (ε : ℝ) :
    (P.shiftConstant ε).ptfSupportCost = P.ptfSupportCost := by
  simp [ptfSupportCost, shiftConstant_nonconstantSupport]

theorem shiftConstant_eval (P : SquarefreePolynomial n) (ε : ℝ)
    (bits : Fin n → Bool) :
    (P.shiftConstant ε).eval bits = P.eval bits - ε := by
  rw [eval, eval, shiftConstant_nonlinearSupport]
  simp only [shiftConstant_coeff_empty]
  have hsingle : ∀ i : Fin n,
      (P.shiftConstant ε).coeff {i} = P.coeff {i} := by
    intro i
    exact shiftConstant_coeff_of_nonempty P ε (Finset.singleton_nonempty i)
  simp_rw [hsingle]
  have hnonlinear : ∀ S ∈ P.nonlinearSupport,
      (P.shiftConstant ε).coeff S = P.coeff S := by
    intro S hS
    apply shiftConstant_coeff_of_nonempty
    have hcard := (Finset.mem_filter.mp hS).2.1
    exact Finset.card_pos.mp (by omega)
  have hsum :
      (∑ S ∈ P.nonlinearSupport,
        (P.shiftConstant ε).coeff S * squarefreeMonomial S bits) =
      ∑ S ∈ P.nonlinearSupport,
        P.coeff S * squarefreeMonomial S bits := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [hnonlinear S hS]
  rw [hsum]
  ring

private theorem score_nonpos_of_false
    {score : (Fin n → Bool) → ℝ} {f : (Fin n → Bool) → Bool}
    (h : ∀ bits, 0 < score bits ↔ f bits = true)
    {bits : Fin n → Bool} (hfalse : f bits = false) :
    score bits ≤ 0 := by
  by_contra hnot
  push Not at hnot
  have htrue := (h bits).mp hnot
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

private theorem exists_strict_shift
    (score : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → Bool)
    (h : ∀ bits, 0 < score bits ↔ f bits = true) :
    ∃ ε : ℝ, 0 < ε ∧
      StrictSignRepresentsScore (fun bits ↦ score bits - ε) f := by
  classical
  let T : Finset (Fin n → Bool) :=
    Finset.univ.filter fun bits ↦ f bits = true
  obtain ⟨ε, hεpos, hεlt⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ∀ bits, f bits = true → ε < score bits := by
    by_cases hT : T.Nonempty
    · refine ⟨T.inf' hT score / 2, ?_, ?_⟩
      · apply half_pos
        rw [Finset.lt_inf'_iff]
        intro bits hbits
        exact (h bits).mpr (Finset.mem_filter.mp hbits).2
      · intro bits htrue
        have hmem : bits ∈ T :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ bits, htrue⟩
        have hle := Finset.inf'_le score hmem
        have hpos : 0 < T.inf' hT score := by
          rw [Finset.lt_inf'_iff]
          intro y hy
          exact (h y).mpr (Finset.mem_filter.mp hy).2
        linarith
    · refine ⟨1, one_pos, ?_⟩
      intro bits htrue
      exfalso
      apply hT
      exact ⟨bits, Finset.mem_filter.mpr ⟨Finset.mem_univ bits, htrue⟩⟩
  refine ⟨ε, hεpos, fun bits ↦ ?_⟩
  constructor
  · constructor
    · intro hshift
      exact (h bits).mp (by linarith)
    · intro htrue
      linarith [hεlt bits htrue]
  · cases hbit : f bits with
    | false =>
        have hnonpos := score_nonpos_of_false h hbit
        linarith
    | true =>
        have hlt := hεlt bits hbit
        linarith

/-- Every weak polynomial-threshold certificate can be made strict by changing
only its constant coefficient, without changing either support cost. -/
theorem exists_strictification
    (P : SquarefreePolynomial n) (f : (Fin n → Bool) → Bool)
    (hP : P.SignRepresents f) :
    ∃ Q : SquarefreePolynomial n,
      Q.StrictSignRepresents f ∧
      Q.affineFreeSupportCost = P.affineFreeSupportCost ∧
      Q.ptfSupportCost = P.ptfSupportCost := by
  obtain ⟨ε, _, hstrict⟩ := exists_strict_shift P.eval f hP
  refine ⟨P.shiftConstant ε, ?_, P.shiftConstant_affineFreeSupportCost ε,
    P.shiftConstant_ptfSupportCost ε⟩
  intro bits
  rw [shiftConstant_eval]
  exact hstrict bits

/-- The degree bound for a squarefree polynomial is the largest cardinality
of a subset with nonzero coefficient. -/
def DegreeLE (P : SquarefreePolynomial n) (d : ℕ) : Prop :=
  ∀ S, P.coeff S ≠ 0 → S.card ≤ d

private theorem squarefreeMonomial_eq_indicator
    (A : Finset (Fin n)) (bits : Fin n → Bool) :
    squarefreeMonomial A bits = if A ⊆ onesSet bits then 1 else 0 := by
  by_cases hsub : A ⊆ onesSet bits
  · rw [if_pos hsub]
    unfold squarefreeMonomial
    apply Finset.prod_eq_one
    intro i hi
    have hbit := mem_onesSet.mp (hsub hi)
    simp [boolToReal, hbit]
  · rw [if_neg hsub]
    obtain ⟨i, hi, hix⟩ : ∃ i ∈ A, i ∉ onesSet bits := by
      by_contra hcon
      push Not at hcon
      exact hsub (fun i hi ↦ hcon i hi)
    apply Finset.prod_eq_zero hi
    have hfalse : bits i = false := by
      cases hbit : bits i with
      | false => rfl
      | true => exact (hix (mem_onesSet.mpr hbit)).elim
    simp [boolToReal, hfalse]

/-- Canonical squarefree reduction of an arbitrary multivariate polynomial on
the Boolean cube. Coefficients of monomials with the same support are summed. -/
noncomputable def ofMvPolynomial (Q : MvPolynomial (Fin n) ℝ) :
    SquarefreePolynomial n :=
  ⟨supportCoeffSum Q⟩

/-- Squarefree reduction preserves evaluation at every Boolean point. -/
theorem ofMvPolynomial_eval (Q : MvPolynomial (Fin n) ℝ)
    (bits : Fin n → Bool) :
    (ofMvPolynomial Q).eval bits = MvPolynomial.eval (cubePoint bits) Q := by
  classical
  rw [eval_cube_eq_subset_sum]
  have hmaps : ∀ e ∈ Q.support,
      e.support ∈ (Finset.univ : Finset (Fin n)).powerset :=
    fun e _ ↦ Finset.mem_powerset.mpr (Finset.subset_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [← fullSum_eq_eval, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro A _
  rw [squarefreeMonomial_eq_indicator]
  unfold ofMvPolynomial
  change supportCoeffSum Q A * (if A ⊆ onesSet bits then 1 else 0) = _
  rw [supportCoeffSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_filter] at he
  rw [he.2]

/-- Squarefree reduction does not increase total degree. -/
theorem ofMvPolynomial_degreeLE (Q : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hdeg : Q.totalDegree ≤ d) :
    (ofMvPolynomial Q).DegreeLE d := by
  intro A hA
  by_contra hcard
  push Not at hcard
  apply hA
  unfold ofMvPolynomial supportCoeffSum
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  have hsupport := support_card_le_totalDegree Q he.1
  rw [he.2] at hsupport
  omega

/-- Strict multivariate sign representations induce strict canonical
squarefree sign representations. -/
theorem ofMvPolynomial_strictSignRepresents
    (Q : MvPolynomial (Fin n) ℝ) (f : (Fin n → Bool) → Bool)
    (hQ : StrictSignRep Q f) :
    (ofMvPolynomial Q).StrictSignRepresents f := by
  intro bits
  rw [ofMvPolynomial_eval]
  constructor
  · constructor
    · intro hpos
      cases hbit : f bits with
      | true => rfl
      | false => linarith [(hQ bits).2 hbit]
    · exact (hQ bits).1
  · cases hbit : f bits with
    | false => exact ne_of_lt ((hQ bits).2 hbit)
    | true => exact ne_of_gt ((hQ bits).1 hbit)

/-- Every threshold-degree certificate has a faithful strict squarefree
certificate of the same degree. -/
theorem exists_squarefree_strictSignRep_of_ThresholdDegLE
    {f : (Fin n → Bool) → Bool} {d : ℕ} (h : ThresholdDegLE f d) :
    ∃ P : SquarefreePolynomial n,
      P.DegreeLE d ∧ P.StrictSignRepresents f := by
  obtain ⟨Q, hQdeg, hQ⟩ := exists_strictSignRep_of_ThresholdDegLE h
  exact ⟨ofMvPolynomial Q, ofMvPolynomial_degreeLE Q hQdeg,
    ofMvPolynomial_strictSignRepresents Q f hQ⟩

theorem nonlinearSupport_subset_nonconstantSupport (P : SquarefreePolynomial n) :
    P.nonlinearSupport ⊆ P.nonconstantSupport := by
  intro S hS
  simp only [nonlinearSupport, nonconstantSupport, Finset.mem_filter,
    Finset.mem_univ, true_and] at hS ⊢
  exact ⟨Finset.card_pos.mp (by omega), hS.2⟩

/-- Bundling all singleton monomials never costs more than charging them
separately. -/
theorem affineFreeSupportCost_le_ptfSupportCost (P : SquarefreePolynomial n) :
    P.affineFreeSupportCost ≤ P.ptfSupportCost := by
  classical
  unfold affineFreeSupportCost ptfSupportCost
  by_cases hlin : P.HasLinearPart
  · rw [if_pos hlin]
    obtain ⟨i, hi⟩ := hlin
    let singleton : Finset (Fin n) := {i}
    have hsingle_mem : singleton ∈ P.nonconstantSupport := by
      simp [singleton, nonconstantSupport, hi]
    have hsingle_not : singleton ∉ P.nonlinearSupport := by
      simp [singleton, nonlinearSupport]
    have hsubset : insert singleton P.nonlinearSupport ⊆ P.nonconstantSupport := by
      intro S hS
      rw [Finset.mem_insert] at hS
      rcases hS with rfl | hS
      · exact hsingle_mem
      · exact nonlinearSupport_subset_nonconstantSupport P hS
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hsingle_not] at hcard
    omega
  · rw [if_neg hlin]
    exact Finset.card_le_card (nonlinearSupport_subset_nonconstantSupport P)

/-- A degree bound limits the nonlinear support by the number of subsets of
sizes two through `d`. -/
theorem nonlinearSupport_card_le_sum_choose
    (P : SquarefreePolynomial n) {d : ℕ} (hdeg : P.DegreeLE d) :
    P.nonlinearSupport.card ≤ ∑ r ∈ Finset.Icc 2 d, n.choose r := by
  classical
  let candidates : Finset (Finset (Fin n)) :=
    (Finset.Icc 2 d).biUnion fun r ↦
      (Finset.univ : Finset (Fin n)).powersetCard r
  have hsubset : P.nonlinearSupport ⊆ candidates := by
    intro S hS
    simp only [nonlinearSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS
    rw [Finset.mem_biUnion]
    refine ⟨S.card, ?_, ?_⟩
    · simp [hS.1, hdeg S hS.2]
    · simp
  calc
    P.nonlinearSupport.card ≤ candidates.card := Finset.card_le_card hsubset
    _ ≤ ∑ r ∈ Finset.Icc 2 d,
        ((Finset.univ : Finset (Fin n)).powersetCard r).card := by
      exact Finset.card_biUnion_le
    _ = ∑ r ∈ Finset.Icc 2 d, n.choose r := by simp

/-- Uniform support-count bound for a squarefree polynomial of degree at most
`d`. The entire linear part costs at most one head. -/
theorem affineFreeSupportCost_le_one_add_sum_choose
    (P : SquarefreePolynomial n) {d : ℕ} (hdeg : P.DegreeLE d) :
    P.affineFreeSupportCost ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r := by
  classical
  have hnonlinear := nonlinearSupport_card_le_sum_choose P hdeg
  unfold affineFreeSupportCost
  split <;> omega

private theorem sum_equivFin_nonlinearSupport
    (P : SquarefreePolynomial n) (F : Finset (Fin n) → ℝ) :
    (∑ j : Fin P.nonlinearSupport.card,
        F ((P.nonlinearSupport.equivFin).symm j).1) =
      ∑ S ∈ P.nonlinearSupport, F S := by
  rw [← P.nonlinearSupport.sum_attach, Finset.attach_eq_univ,
    ← P.nonlinearSupport.equivFin.symm.sum_comp]

/-- Every strict squarefree sign certificate is computable with its
affine-free support cost. -/
theorem computableWithHeadsN_affineFreeSupportCost
    (P : SquarefreePolynomial n) (f : (Fin n → Bool) → Bool)
    (hP : P.StrictSignRepresents f) :
    computableWithHeadsN n P.affineFreeSupportCost f := by
  classical
  by_cases hlin : P.HasLinearPart
  · rw [affineFreeSupportCost, if_pos hlin]
    let g : Fin (P.nonlinearSupport.card + 1) → (Fin n → Bool) → ℝ :=
      Fin.cases (affineValue 0 (fun i ↦ P.coeff {i}))
        (fun j bits ↦
          let S := ((P.nonlinearSupport.equivFin).symm j).1
          P.coeff S * squarefreeMonomial S bits)
    refine computableWithHeadsN_of_uniformlyOneAtomApproximable
      (f := f) g ?_ (P.coeff ∅) ?_
    · intro h
      refine Fin.cases ?_ (fun j ↦ ?_) h
      · exact uniformlyOneAtomApproximable_affineValue 0 (fun i ↦ P.coeff {i})
      · exact uniformlyOneAtomApproximable_signedMonomial
          ((P.nonlinearSupport.equivFin).symm j).1
          (P.coeff ((P.nonlinearSupport.equivFin).symm j).1)
    · intro bits
      dsimp only
      rw [show (∑ h, g h bits) = affineValue 0 (fun i ↦ P.coeff {i}) bits +
          ∑ S ∈ P.nonlinearSupport, P.coeff S * squarefreeMonomial S bits by
        rw [Fin.sum_univ_succ]
        change affineValue 0 (fun i ↦ P.coeff {i}) bits +
          (∑ j : Fin P.nonlinearSupport.card,
            P.coeff ((P.nonlinearSupport.equivFin).symm j).1 *
              squarefreeMonomial ((P.nonlinearSupport.equivFin).symm j).1 bits) = _
        congr 1
        exact sum_equivFin_nonlinearSupport P
          (fun S ↦ P.coeff S * squarefreeMonomial S bits)]
      simpa [SquarefreePolynomial.eval, add_assoc] using hP bits
  · rw [affineFreeSupportCost, if_neg hlin, Nat.add_zero]
    let g : Fin P.nonlinearSupport.card → (Fin n → Bool) → ℝ :=
      fun j bits ↦
        let S := ((P.nonlinearSupport.equivFin).symm j).1
        P.coeff S * squarefreeMonomial S bits
    refine computableWithHeadsN_of_uniformlyOneAtomApproximable
      (f := f) g ?_ (P.coeff ∅) ?_
    · intro j
      exact uniformlyOneAtomApproximable_signedMonomial
        ((P.nonlinearSupport.equivFin).symm j).1
        (P.coeff ((P.nonlinearSupport.equivFin).symm j).1)
    · have hlinear_zero : ∀ i, P.coeff {i} = 0 := by
        intro i
        by_contra hi
        exact hlin ⟨i, hi⟩
      intro bits
      dsimp only
      rw [show (∑ j, g j bits) =
          ∑ S ∈ P.nonlinearSupport, P.coeff S * squarefreeMonomial S bits by
        change (∑ j : Fin P.nonlinearSupport.card,
          P.coeff ((P.nonlinearSupport.equivFin).symm j).1 *
            squarefreeMonomial ((P.nonlinearSupport.equivFin).symm j).1 bits) = _
        exact sum_equivFin_nonlinearSupport P
          (fun S ↦ P.coeff S * squarefreeMonomial S bits)]
      simpa [SquarefreePolynomial.eval, affineValue, hlinear_zero] using hP bits

/-- A strict squarefree certificate directly upper-bounds head complexity. -/
theorem HStar_le_affineFreeSupportCost
    (P : SquarefreePolynomial n) (f : (Fin n → Bool) → Bool)
    (hP : P.StrictSignRepresents f) :
    HStar n f ≤ P.affineFreeSupportCost :=
  HStar_le_of_computableWithHeadsN (computableWithHeadsN_affineFreeSupportCost P f hP)

end SquarefreePolynomial

private theorem exists_affineFreeSupportCost
    (f : (Fin n → Bool) → Bool) :
    ∃ k : ℕ, ∃ P : SquarefreePolynomial n,
      P.SignRepresents f ∧ P.affineFreeSupportCost = k := by
  obtain ⟨P, _, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f)
  exact ⟨P.affineFreeSupportCost, P, hP.signRepresents, rfl⟩

/-- The minimum affine-free support cost among all squarefree real
polynomial-threshold representations of `f`. This is `afs±(f)`. -/
noncomputable def affineFreeSparsity (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_affineFreeSupportCost f)

/-- The minimum affine-free sparsity is attained. -/
theorem affineFreeSparsity_spec (f : (Fin n → Bool) → Bool) :
    ∃ P : SquarefreePolynomial n,
      P.SignRepresents f ∧ P.affineFreeSupportCost = affineFreeSparsity f := by
  classical
  exact Nat.find_spec (exists_affineFreeSupportCost f)

/-- Minimality of affine-free polynomial-threshold sparsity. -/
theorem affineFreeSparsity_le (f : (Fin n → Bool) → Bool)
    (P : SquarefreePolynomial n) (hP : P.SignRepresents f) :
    affineFreeSparsity f ≤ P.affineFreeSupportCost := by
  classical
  exact Nat.find_min' (exists_affineFreeSupportCost f) ⟨P, hP, rfl⟩

private theorem exists_ptfSupportCost (f : (Fin n → Bool) → Bool) :
    ∃ k : ℕ, ∃ P : SquarefreePolynomial n,
      P.SignRepresents f ∧ P.ptfSupportCost = k := by
  obtain ⟨P, _, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f)
  exact ⟨P.ptfSupportCost, P, hP.signRepresents, rfl⟩

/-- The minimum number of nonconstant squarefree monomials in a real
polynomial-threshold representation. This is `ptfsp(f)`. -/
noncomputable def ptfSparsity (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_ptfSupportCost f)

/-- Polynomial-threshold sparsity is attained. -/
theorem ptfSparsity_spec (f : (Fin n → Bool) → Bool) :
    ∃ P : SquarefreePolynomial n,
      P.SignRepresents f ∧ P.ptfSupportCost = ptfSparsity f := by
  classical
  exact Nat.find_spec (exists_ptfSupportCost f)

/-- Minimality of polynomial-threshold sparsity. -/
theorem ptfSparsity_le (f : (Fin n → Bool) → Bool)
    (P : SquarefreePolynomial n) (hP : P.SignRepresents f) :
    ptfSparsity f ≤ P.ptfSupportCost := by
  classical
  exact Nat.find_min' (exists_ptfSupportCost f) ⟨P, hP, rfl⟩

/-- **Affine-free polynomial-threshold sparsity upper bound.** -/
theorem HStar_le_affineFreeSparsity (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ affineFreeSparsity f := by
  classical
  obtain ⟨P, hP, hcost⟩ := affineFreeSparsity_spec f
  obtain ⟨Q, hQ, hQcost, _⟩ := P.exists_strictification f hP
  calc
    HStar n f ≤ Q.affineFreeSupportCost :=
      Q.HStar_le_affineFreeSupportCost f hQ
    _ = P.affineFreeSupportCost := hQcost
    _ = affineFreeSparsity f := hcost

/-- Bundling the linear terms gives `afs±(f) ≤ ptfsp(f)`. -/
theorem affineFreeSparsity_le_ptfSparsity
    (f : (Fin n → Bool) → Bool) :
    affineFreeSparsity f ≤ ptfSparsity f := by
  obtain ⟨P, hP, hcost⟩ := ptfSparsity_spec f
  calc
    affineFreeSparsity f ≤ P.affineFreeSupportCost :=
      affineFreeSparsity_le f P hP
    _ ≤ P.ptfSupportCost := P.affineFreeSupportCost_le_ptfSupportCost
    _ = ptfSparsity f := hcost

/-- Threshold degree at most `d` gives the affine-free support-count bound. -/
theorem affineFreeSparsity_le_one_add_sum_choose_of_ThresholdDegLE
    {f : (Fin n → Bool) → Bool} {d : ℕ} (h : ThresholdDegLE f d) :
    affineFreeSparsity f ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r := by
  obtain ⟨P, hdeg, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE h
  calc
    affineFreeSparsity f ≤ P.affineFreeSupportCost :=
      affineFreeSparsity_le f P hP.signRepresents
    _ ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r :=
      P.affineFreeSupportCost_le_one_add_sum_choose hdeg

/-- The corresponding uniform head-complexity upper bound. No nonconstancy
hypothesis is needed. -/
theorem HStar_le_one_add_sum_choose_of_ThresholdDegLE
    {f : (Fin n → Bool) → Bool} {d : ℕ} (h : ThresholdDegLE f d) :
    HStar n f ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r :=
  (HStar_le_affineFreeSparsity f).trans
    (affineFreeSparsity_le_one_add_sum_choose_of_ThresholdDegLE h)

/-- Minimum-threshold-degree form of the support-count corollary. -/
theorem HStar_le_one_add_sum_choose_thresholdDeg
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤
      1 + ∑ r ∈ Finset.Icc 2 (thresholdDeg f), n.choose r :=
  HStar_le_one_add_sum_choose_of_ThresholdDegLE (thresholdDeg_spec f)

end HeadComplexity
