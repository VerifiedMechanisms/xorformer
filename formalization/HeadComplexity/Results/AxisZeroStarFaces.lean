import HeadComplexity.Results.AxisZeroFaces
import HeadComplexity.Results.UniversalLinearSaving

set_option linter.style.header false

/-!
# Star cover costs for arbitrary real positive-face corrections

Grouping free-coordinate monomials before multiplying by the fixed-face
monomial preserves their upward star structure. Consequently an arbitrary
real residual on an m-dimensional positive face costs only
`monomialStarCoverNumber m` atoms, including its constant coefficient.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Finset
open scoped BigOperators

private theorem starFace_affineValue_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (cs : ι → Fin n → ℝ) (bits : Fin n → Bool) :
    affineValue (∑ t, c t) (fun i ↦ ∑ t, cs t i) bits =
      ∑ t, affineValue (c t) (cs t) bits := by
  simp only [affineValue, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem starFace_term_affine {n : ℕ}
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

/-- Weighted monomials assigned to `K` upward stars are uniformly
approximable by `K` actual atoms, including their constant terms. -/
theorem uniformlyAtomsApproximable_of_monomial_star_assignment
    {n K : ℕ} {ι : Type*} [Fintype ι]
    (support : ι → Finset (Fin n)) (coeff : ι → ℝ)
    (centers : Fin K → Finset (Fin n)) (assignment : ι → Fin K)
    (hstar : ∀ t, MonomialStar (centers (assignment t)) (support t)) :
    UniformlyAtomsApproximable (Fin K)
      (fun bits ↦ ∑ t, coeff t * squarefreeMonomial (support t) bits) := by
  classical
  have hfactor : ∀ t : ι, ∃ (c : ℝ) (cs : Fin n → ℝ), ∀ bits,
      coeff t * squarefreeMonomial (support t) bits =
        squarefreeMonomial (centers (assignment t)) bits * affineValue c cs bits :=
    fun t ↦ starFace_term_affine _ _ (hstar t) _
  choose localConst localCoeff hfactor using hfactor
  let c : Fin K → ℝ := fun j ↦ ∑ t, if assignment t = j then localConst t else 0
  let cs : Fin K → Fin n → ℝ :=
    fun j i ↦ ∑ t, if assignment t = j then localCoeff t i else 0
  let g : Fin K → (Fin n → Bool) → ℝ :=
    fun j bits ↦ squarefreeMonomial (centers j) bits * affineValue (c j) (cs j) bits
  have hg : ∀ j, UniformlyOneAtomApproximable (g j) := fun j ↦
    uniformlyOneAtomApproximable_monomial_mul_affineValue (centers j) (c j) (cs j)
  have hsum (bits : Fin n → Bool) :
      (∑ j, g j bits) = ∑ t, coeff t * squarefreeMonomial (support t) bits := by
    have hblock (j : Fin K) : affineValue (c j) (cs j) bits =
        ∑ t, if assignment t = j then
          affineValue (localConst t) (localCoeff t) bits else 0 := by
      dsimp [c, cs]
      rw [starFace_affineValue_sum]
      apply Finset.sum_congr rfl
      intro t _
      split <;> simp [affineValue]
    simp only [g, hblock, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [hfactor t bits]
    simp
  have happ := CubeCylinder.uniformlyAtomsApproximable_fin_sum g hg
  simpa only [hsum] using happ

private theorem positive_face_map_star {n m : ℕ}
    (S : Finset (Fin n)) (free : Fin m ↪ Fin n)
    (hdisj : Disjoint S (Finset.univ.map free))
    {U V : Finset (Fin m)} (h : StarCoverRecursion.Star U V) :
    MonomialStar (S ∪ U.map free) (S ∪ V.map free) := by
  classical
  rcases h with rfl | ⟨i, hi, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨free i, ?_, ?_⟩
    · simp only [Finset.mem_union, Finset.mem_map, free.injective.eq_iff,
        exists_eq_right]
      push Not
      constructor
      · intro his
        exact (Finset.disjoint_left.mp hdisj his)
          (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · exact hi
    · ext j
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_map]
      aesop

/-- Every real positive-face residual has the full free-coordinate star
cost instead of the number of monomials. -/
theorem positive_face_uniformlyAtomsApproximable_star {n m : ℕ}
    (S : Finset (Fin n)) (free : Fin m ↪ Fin n)
    (hdisj : Disjoint S (Finset.univ.map free))
    (g : (Fin m → Bool) → ℝ) :
    UniformlyAtomsApproximable (Fin (monomialStarCoverNumber m))
      (fun bits ↦ squarefreeMonomial S bits * g (fun i ↦ bits (free i))) := by
  classical
  obtain ⟨c, hc⟩ := positive_face_expansion S free hdisj g
  obtain ⟨C, hcard, hC⟩ := monomialStarCoverNumber_spec m
  let e := C.equivFin
  have hex (U : Finset (Fin m)) : ∃ j : Fin C.card,
      MonomialStar (S ∪ (e.symm j).1.map free) (S ∪ U.map free) := by
    obtain ⟨V, hV, hstar⟩ := hC U
    refine ⟨e ⟨V, hV⟩, ?_⟩
    simpa using positive_face_map_star S free hdisj hstar
  choose assignment hstar using hex
  have happ := uniformlyAtomsApproximable_of_monomial_star_assignment
    (fun U : Finset (Fin m) ↦ S ∪ U.map free) c
    (fun j : Fin C.card ↦ S ∪ (e.symm j).1.map free) assignment hstar
  rw [hcard] at happ
  simpa only [hc] using happ

/-- Arbitrary real residuals on positive faces have the star-cover budget. -/
theorem positive_face_correction_approximable_star {n m : ℕ} (rho : CoordFace m n)
    (G T : (Fin n → Bool) → ℝ) :
    UniformlyAtomsApproximable (Fin (monomialStarCoverNumber m))
      (fun bits ↦ squarefreeMonomial rho.fixedSet bits *
        (T (rho.apply (fun j ↦ bits (rho.free j))) -
          G (rho.apply (fun j ↦ bits (rho.free j))))) := by
  classical
  refine positive_face_uniformlyAtomsApproximable_star rho.fixedSet rho.free ?_
    (fun x ↦ T (rho.apply x) - G (rho.apply x))
  simpa [CoordFace.fixedSet, CoordFace.freeSet, Finset.map_eq_image]
    using (Finset.sdiff_disjoint : Disjoint (Finset.univ \ rho.freeSet) rho.freeSet)

/-- Two exceptional positive faces can be repaired at the sum of their star-cover costs.
The initial score need only have correct strict signs outside their union.
The second correction is identically zero on the already repaired first
face, including their intersection, before uniform atom approximation. -/
theorem repair_two_positive_faces_star {n H a b : ℕ}
    (rho : CoordFace a n) (tau : CoordFace b n)
    (hrho : ∀ i, rho.base i = true) (htau : ∀ i, tau.base i = true)
    (φ : Fin H → FracAtom n) (bias : ℝ) (f : (Fin n → Bool) → Bool)
    (houtside : ∀ bits, ¬OnPositiveFace rho bits → ¬OnPositiveFace tau bits →
      (0 < bias + ∑ h, (φ h).eval bits ↔ f bits = true) ∧
        bias + ∑ h, (φ h).eval bits ≠ 0) :
    computableWithHeadsN n (H + monomialStarCoverNumber a + monomialStarCoverNumber b) f := by
  classical
  let G : (Fin n → Bool) → ℝ := fun bits ↦ bias + ∑ h, (φ h).eval bits
  let T : (Fin n → Bool) → ℝ := fun bits ↦ if f bits then 1 else -1
  let R : (Fin n → Bool) → ℝ := fun bits ↦ squarefreeMonomial rho.fixedSet bits *
    (T (rho.apply (fun j ↦ bits (rho.free j))) -
      G (rho.apply (fun j ↦ bits (rho.free j))))
  let G₁ : (Fin n → Bool) → ℝ := fun bits ↦ G bits + R bits
  let S : (Fin n → Bool) → ℝ := fun bits ↦ squarefreeMonomial tau.fixedSet bits *
    (T (tau.apply (fun j ↦ bits (tau.free j))) -
      G₁ (tau.apply (fun j ↦ bits (tau.free j))))
  have hfirst (bits : Fin n → Bool) :
      G₁ bits = if OnPositiveFace rho bits then T bits else G bits :=
    positive_face_repair_eval rho hrho G T bits
  have hsecond (bits : Fin n → Bool) :
      G₁ bits + S bits = if OnPositiveFace tau bits then T bits else G₁ bits :=
    positive_face_repair_eval tau htau G₁ T bits
  have hstrict : StrictSignRepresentsScore (fun bits ↦ G₁ bits + S bits) f := by
    intro bits
    change (0 < G₁ bits + S bits ↔ f bits = true) ∧ G₁ bits + S bits ≠ 0
    rw [hsecond, hfirst]
    by_cases ht : OnPositiveFace tau bits
    · simp only [ht, ite_true]
      cases hf : f bits <;> simp [T, hf]
    · simp only [ht, ite_false]
      by_cases hr : OnPositiveFace rho bits
      · simp only [hr, ite_true]
        cases hf : f bits <;> simp [T, hf]
      · simp only [hr, ite_false]
        exact houtside bits hr ht
  let sizes : Fin 3 → ℕ := ![H, monomialStarCoverNumber a, monomialStarCoverNumber b]
  let terms : Fin 3 → (Fin n → Bool) → ℝ := ![fun bits ↦ ∑ h, (φ h).eval bits, R, S]
  have happ : ∀ j, UniformlyAtomsApproximable (Fin (sizes j)) (terms j) := by
    intro j
    fin_cases j
    · intro ε hε
      refine ⟨φ, 0, ?_⟩
      intro bits
      change |(0 + ∑ h : Fin H, (φ h).eval bits) -
        (∑ h : Fin H, (φ h).eval bits)| < ε
      simpa using hε
    · exact positive_face_correction_approximable_star rho G T
    · exact positive_face_correction_approximable_star tau G₁ T
  have hsum : StrictSignRepresentsScore (fun bits ↦ bias + ∑ j, terms j bits) f := by
    convert hstrict using 1
    funext bits
    simp [terms, Fin.sum_univ_three, G₁, G]
    ring
  have hcomp := computableWithHeadsCard_of_uniformlyAtomsApproximable terms happ bias hsum
  have hcard : Fintype.card ((j : Fin 3) × Fin (sizes j)) =
      H + monomialStarCoverNumber a + monomialStarCoverNumber b := by
    simp [Fintype.card_sigma, sizes, Fin.sum_univ_three]
  rwa [hcard] at hcomp

/-- The exceptional-face correction budget in the unchanged `HStar` invariant. -/
theorem HStar_le_repair_two_positive_faces_star {n H a b : ℕ}
    (rho : CoordFace a n) (tau : CoordFace b n)
    (hrho : ∀ i, rho.base i = true) (htau : ∀ i, tau.base i = true)
    (φ : Fin H → FracAtom n) (bias : ℝ) (f : (Fin n → Bool) → Bool)
    (houtside : ∀ bits, ¬OnPositiveFace rho bits → ¬OnPositiveFace tau bits →
      (0 < bias + ∑ h, (φ h).eval bits ↔ f bits = true) ∧
        bias + ∑ h, (φ h).eval bits ≠ 0) :
    HStar n f ≤ H + monomialStarCoverNumber a + monomialStarCoverNumber b :=
  HStar_le_of_computableWithHeadsN
    (repair_two_positive_faces_star rho tau hrho htau φ bias f houtside)


end AxisZeroGluing
end HeadComplexity
