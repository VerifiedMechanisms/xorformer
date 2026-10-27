import HeadComplexity.Atoms.AffineMonomialApproximation
import HeadComplexity.Results.AffineFreeSparsity

set_option linter.style.header false

/-!
# Monomial star covers

A center `S` covers `S` itself and each monomial `insert i S`. All terms
assigned to one center form a single positive monomial times an affine
function, so one attention head suffices for the entire group.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- A monomial is in the upward radius-one star of `S`. -/
def MonomialStar (S T : Finset (Fin n)) : Prop :=
  S = T ∨ ∃ i, i ∉ S ∧ insert i S = T

/-- A finite family of centers covers every active nonconstant monomial. -/
def SquarefreePolynomial.HasStarCover (P : SquarefreePolynomial n)
    (centers : Finset (Finset (Fin n))) : Prop :=
  ∀ T ∈ P.nonconstantSupport, ∃ S ∈ centers, MonomialStar S T

private theorem affineValue_sum {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (cs : ι → Fin n → ℝ) (bits : Fin n → Bool) :
    affineValue (∑ t, c t) (fun i ↦ ∑ t, cs t i) bits =
      ∑ t, affineValue (c t) (cs t) bits := by
  simp only [affineValue, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem star_term_affine
    (S T : Finset (Fin n)) (h : MonomialStar S T) (a : ℝ) :
    ∃ (c : ℝ) (cs : Fin n → ℝ), ∀ bits,
      a * squarefreeMonomial T bits =
        squarefreeMonomial S bits * affineValue c cs bits := by
  classical
  rcases h with rfl | ⟨i, hi, rfl⟩
  · exact ⟨a, 0, fun bits ↦ by simp [affineValue]; ring⟩
  · refine ⟨0, fun j ↦ if j = i then a else 0, fun bits ↦ ?_⟩
    simp [squarefreeMonomial, Finset.prod_insert hi, affineValue]
    ring

namespace SquarefreePolynomial

/-- Splitting off the constant leaves precisely the active nonconstant
monomials, without counting any zero coefficient. -/
theorem constant_add_nonconstantSupport_sum (P : SquarefreePolynomial n)
    (bits : Fin n → Bool) :
    P.coeff ∅ + ∑ T ∈ P.nonconstantSupport,
      P.coeff T * squarefreeMonomial T bits = P.eval bits := by
  classical
  rw [← P.fullSum_eq_eval]
  have hsub : P.nonconstantSupport ⊆ Finset.univ.erase ∅ := by
    intro T hT
    simp only [nonconstantSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hT
    simp [hT.1.ne_empty]
  have hsum := Finset.sum_subset hsub
    (f := fun T ↦ P.coeff T * squarefreeMonomial T bits)
    (by
      intro T hT hnot
      have hne : T ≠ ∅ := (Finset.mem_erase.mp hT).1
      have hzero : P.coeff T = 0 := by
        simpa [nonconstantSupport, Finset.nonempty_iff_ne_empty, hne] using hnot
      simp [hzero])
  rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ ∅)]
  simp [squarefreeMonomial, add_comm]

/-- Every monomial star cover compiles to actual attention heads, with one
head for each center and a free global constant. -/
theorem computableWithHeadsN_of_starCover
    (P : SquarefreePolynomial n) (f : (Fin n → Bool) → Bool)
    (hP : P.StrictSignRepresents f)
    (centers : Finset (Finset (Fin n))) (hcover : P.HasStarCover centers) :
    computableWithHeadsN n centers.card f := by
  classical
  let I := ↥P.nonconstantSupport
  let e := centers.equivFin
  have hfactor : ∀ t : I, ∃ (j : Fin centers.card) (c : ℝ) (cs : Fin n → ℝ),
      ∀ bits, P.coeff t.1 * squarefreeMonomial t.1 bits =
        squarefreeMonomial (e.symm j).1 bits * affineValue c cs bits := by
    intro t
    obtain ⟨S, hS, hstar⟩ := hcover t.1 t.2
    obtain ⟨c, cs, hcs⟩ := star_term_affine S t.1 hstar (P.coeff t.1)
    refine ⟨e ⟨S, hS⟩, c, cs, ?_⟩
    simpa using hcs
  choose assignment localConst localCoeff hfactor using hfactor
  let c : Fin centers.card → ℝ :=
    fun j ↦ ∑ t : I, if assignment t = j then localConst t else 0
  let cs : Fin centers.card → Fin n → ℝ :=
    fun j i ↦ ∑ t : I, if assignment t = j then localCoeff t i else 0
  let g : Fin centers.card → (Fin n → Bool) → ℝ :=
    fun j bits ↦ squarefreeMonomial (e.symm j).1 bits * affineValue (c j) (cs j) bits
  have hg : ∀ j, UniformlyOneAtomApproximable (g j) := fun j ↦
    uniformlyOneAtomApproximable_monomial_mul_affineValue (e.symm j).1 (c j) (cs j)
  apply computableWithHeadsN_of_uniformlyOneAtomApproximable g hg (P.coeff ∅)
  have hsum : ∀ bits, (∑ j, g j bits) =
      ∑ T ∈ P.nonconstantSupport, P.coeff T * squarefreeMonomial T bits := by
    intro bits
    have hblock : ∀ j, affineValue (c j) (cs j) bits =
        ∑ t : I, if assignment t = j then
          affineValue (localConst t) (localCoeff t) bits else 0 := by
      intro j
      dsimp [c, cs]
      rw [affineValue_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp [affineValue]
    simp only [g, hblock, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ t : I, ∑ j, squarefreeMonomial (e.symm j).1 bits *
          (if assignment t = j then affineValue (localConst t) (localCoeff t) bits
            else 0)) =
          ∑ t : I, P.coeff t.1 * squarefreeMonomial t.1 bits := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hfactor t bits]
        simp
      _ = ∑ T ∈ P.nonconstantSupport,
          P.coeff T * squarefreeMonomial T bits := by
        rw [← P.nonconstantSupport.sum_attach, Finset.attach_eq_univ]
  intro bits
  change ((0 < P.coeff ∅ + ∑ j, g j bits ↔ f bits = true) ∧
    P.coeff ∅ + ∑ j, g j bits ≠ 0)
  rw [hsum, P.constant_add_nonconstantSupport_sum]
  exact hP bits

/-- The number of centers in any active monomial star cover upper-bounds
head complexity. -/
theorem HStar_le_of_starCover
    (P : SquarefreePolynomial n) (f : (Fin n → Bool) → Bool)
    (hP : P.StrictSignRepresents f)
    (centers : Finset (Finset (Fin n))) (hcover : P.HasStarCover centers) :
    HStar n f ≤ centers.card :=
  HStar_le_of_computableWithHeadsN (P.computableWithHeadsN_of_starCover f hP centers hcover)

end SquarefreePolynomial

/-- The possible centers that cover a monomial: itself and its single
coordinate deletions. -/
def monomialPredecessors {n : ℕ} (T : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  insert T (T.image fun i ↦ T.erase i)

theorem mem_monomialPredecessors_iff {n : ℕ} (S T : Finset (Fin n)) :
    S ∈ monomialPredecessors T ↔ MonomialStar S T := by
  classical
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨i, Finset.notMem_erase i T, Finset.insert_erase hi⟩
  · rintro (h | ⟨i, hi, h⟩)
    · exact Finset.mem_insert.mpr (Or.inl h)
    · apply Finset.mem_insert.mpr
      right
      refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
      · rw [← h]
        exact Finset.mem_insert_self i S
      · rw [← h]
        simp [hi]

theorem card_monomialPredecessors {n : ℕ} (T : Finset (Fin n)) :
    (monomialPredecessors T).card = T.card + 1 := by
  classical
  have hnot : T ∉ T.image (fun i ↦ T.erase i) := by
    intro h
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
    have : i ∈ T.erase i := heq.symm ▸ hi
    exact Finset.notMem_erase i T this
  have hinj : Set.InjOn (fun i ↦ T.erase i) T := by
    intro i hi j hj heq
    dsimp only at heq
    by_contra hne
    have hj' : j ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm hne, hj⟩
    rw [heq] at hj'
    exact Finset.notMem_erase j T hj'
  simp only [monomialPredecessors, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injOn hinj]

end HeadComplexity
