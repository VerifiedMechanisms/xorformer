import HeadComplexity.Results.RawCalibratedVote
import HeadComplexity.BooleanCube.CoordinateFace

set_option linter.style.header false

/-!
# Real-valued corrections on positive coordinate faces

Any real function on the free coordinates of a positive coordinate face is
uniformly approximable, after zero extension, with one original-model atom
per squarefree monomial. This includes arbitrary residual corrections to an
already constructed score, not merely Boolean functions.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Finset MvPolynomial
open scoped BigOperators

/-- Real-valued truth tables have exact squarefree expansions. -/
theorem real_cube_expansion {m : ℕ} (g : (Fin m → Bool) → ℝ) :
    ∃ c : Finset (Fin m) → ℝ, ∀ bits,
      (∑ S, c S * squarefreeMonomial S bits) = g bits := by
  classical
  let Q : MvPolynomial (Fin m) ℝ :=
    ∑ target, C (g target) * booleanPointPolynomial target
  let P := SquarefreePolynomial.ofMvPolynomial Q
  refine ⟨P.coeff, ?_⟩
  intro bits
  rw [SquarefreePolynomial.fullSum_eq_eval, SquarefreePolynomial.ofMvPolynomial_eval]
  simp only [Q, map_sum, map_mul, eval_C, eval_booleanPointPolynomial]
  simp

/-- Multiplication by the fixed positive face maps every free-coordinate
monomial to one ambient monomial. No extra coordinates or heads are needed. -/
theorem positive_face_expansion {n m : ℕ} (S : Finset (Fin n))
    (free : Fin m ↪ Fin n) (hdisj : Disjoint S (Finset.univ.map free))
    (g : (Fin m → Bool) → ℝ) :
    ∃ c : Finset (Fin m) → ℝ, ∀ bits,
      (∑ U, c U * squarefreeMonomial (S ∪ U.map free) bits) =
        squarefreeMonomial S bits * g (fun i ↦ bits (free i)) := by
  classical
  obtain ⟨c, hc⟩ := real_cube_expansion g
  refine ⟨c, ?_⟩
  intro bits
  have hmono (U : Finset (Fin m)) :
      squarefreeMonomial (S ∪ U.map free) bits =
        squarefreeMonomial S bits * squarefreeMonomial U (fun i ↦ bits (free i)) := by
    have hd : Disjoint S (U.map free) :=
      hdisj.mono_right (Finset.map_subset_map.mpr (Finset.subset_univ U))
    simp [squarefreeMonomial, Finset.prod_union hd]
  simp_rw [hmono]
  rw [← hc (fun i ↦ bits (free i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

/-- An arbitrary real correction supported on a positive face with `m` free
coordinates uses at most `2^m` actual atoms, to any prescribed uniform error. -/
theorem positive_face_uniformlyAtomsApproximable {n m : ℕ}
    (S : Finset (Fin n)) (free : Fin m ↪ Fin n)
    (hdisj : Disjoint S (Finset.univ.map free))
    (g : (Fin m → Bool) → ℝ) :
    UniformlyAtomsApproximable (Fin (2 ^ m))
      (fun bits ↦ squarefreeMonomial S bits * g (fun i ↦ bits (free i))) := by
  classical
  obtain ⟨c, hc⟩ := positive_face_expansion S free hdisj g
  let e : Finset (Fin m) ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq (by simp)
  let terms : Fin (2 ^ m) → (Fin n → Bool) → ℝ := fun h bits ↦
    c (e.symm h) * squarefreeMonomial (S ∪ (e.symm h).map free) bits
  have hterms : ∀ h, UniformlyOneAtomApproximable (terms h) := by
    intro h
    exact uniformlyOneAtomApproximable_signedMonomial _ _
  have heval (bits : Fin n → Bool) : (∑ h, terms h bits) =
      squarefreeMonomial S bits * g (fun i ↦ bits (free i)) := by
    calc
      (∑ h, terms h bits) = ∑ U, c U * squarefreeMonomial (S ∪ U.map free) bits :=
        e.symm.sum_comp (fun U ↦ c U * squarefreeMonomial (S ∪ U.map free) bits)
      _ = _ := hc bits
  have happ := CubeCylinder.uniformlyAtomsApproximable_fin_sum terms hterms
  simpa only [heval] using happ

/-- Membership in the coordinate face with all fixed coordinates equal to one. -/
def OnPositiveFace {n m : ℕ} (rho : CoordFace m n) (bits : Fin n → Bool) : Prop :=
  ∀ i ∈ rho.fixedSet, bits i = true

open Classical in
/-- The positive monomial is the exact indicator of its coordinate face. -/
theorem positive_face_monomial {n m : ℕ} (rho : CoordFace m n) (bits : Fin n → Bool) :
    squarefreeMonomial rho.fixedSet bits = if OnPositiveFace rho bits then 1 else 0 := by
  classical
  by_cases h : OnPositiveFace rho bits
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun i hi ↦ by simp [boolToReal, h i hi]
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hfalse⟩ : ∃ i ∈ rho.fixedSet, bits i ≠ true := by
      simpa [OnPositiveFace] using h
    apply Finset.prod_eq_zero hi
    cases hbit : bits i
    · simp [boolToReal]
    · exact (hfalse hbit).elim

/-- Retraction to a positive coordinate face fixes every point already on it. -/
theorem positive_face_retract {n m : ℕ} (rho : CoordFace m n)
    (hbase : ∀ i, rho.base i = true) (bits : Fin n → Bool)
    (hface : OnPositiveFace rho bits) :
    rho.apply (fun j ↦ bits (rho.free j)) = bits := by
  classical
  funext i
  by_cases hi : ∃ j, rho.free j = i
  · obtain ⟨j, rfl⟩ := hi
    exact rho.apply_free _ j
  · have hfixed : i ∈ rho.fixedSet := by
      simp [CoordFace.fixedSet, CoordFace.mem_freeSet, hi]
    rw [rho.apply_fixed _ hfixed, hbase i, hface i hfixed]

open Classical in
/-- Exact target values on a repaired face, and exact zero change off it. -/
theorem positive_face_repair_eval {n m : ℕ} (rho : CoordFace m n)
    (hbase : ∀ i, rho.base i = true) (G T : (Fin n → Bool) → ℝ)
    (bits : Fin n → Bool) :
    G bits + squarefreeMonomial rho.fixedSet bits *
      (T (rho.apply (fun j ↦ bits (rho.free j))) -
        G (rho.apply (fun j ↦ bits (rho.free j)))) =
      if OnPositiveFace rho bits then T bits else G bits := by
  classical
  rw [positive_face_monomial]
  by_cases h : OnPositiveFace rho bits
  · simp [h, positive_face_retract rho hbase bits h]
  · simp [h]

/-- Arbitrary residual values on a positive face are approximable with one head
per free-coordinate subset. This is the exact cost used by face repairs. -/
theorem positive_face_correction_approximable {n m : ℕ} (rho : CoordFace m n)
    (G T : (Fin n → Bool) → ℝ) :
    UniformlyAtomsApproximable (Fin (2 ^ m))
      (fun bits ↦ squarefreeMonomial rho.fixedSet bits *
        (T (rho.apply (fun j ↦ bits (rho.free j))) -
          G (rho.apply (fun j ↦ bits (rho.free j))))) := by
  classical
  refine positive_face_uniformlyAtomsApproximable rho.fixedSet rho.free ?_
    (fun x ↦ T (rho.apply x) - G (rho.apply x))
  simpa [CoordFace.fixedSet, CoordFace.freeSet, Finset.map_eq_image]
    using (Finset.sdiff_disjoint : Disjoint (Finset.univ \ rho.freeSet) rho.freeSet)

/-- Two exceptional positive faces can be repaired at cost `2^a + 2^b`.
The initial score need only have correct strict signs outside their union.
The second correction is identically zero on the already repaired first
face, including their intersection, before uniform atom approximation. -/
theorem repair_two_positive_faces {n H a b : ℕ}
    (rho : CoordFace a n) (tau : CoordFace b n)
    (hrho : ∀ i, rho.base i = true) (htau : ∀ i, tau.base i = true)
    (φ : Fin H → FracAtom n) (bias : ℝ) (f : (Fin n → Bool) → Bool)
    (houtside : ∀ bits, ¬OnPositiveFace rho bits → ¬OnPositiveFace tau bits →
      (0 < bias + ∑ h, (φ h).eval bits ↔ f bits = true) ∧
        bias + ∑ h, (φ h).eval bits ≠ 0) :
    computableWithHeadsN n (H + 2 ^ a + 2 ^ b) f := by
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
  let sizes : Fin 3 → ℕ := ![H, 2 ^ a, 2 ^ b]
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
    · exact positive_face_correction_approximable rho G T
    · exact positive_face_correction_approximable tau G₁ T
  have hsum : StrictSignRepresentsScore (fun bits ↦ bias + ∑ j, terms j bits) f := by
    convert hstrict using 1
    funext bits
    simp [terms, Fin.sum_univ_three, G₁, G]
    ring
  have hcomp := computableWithHeadsCard_of_uniformlyAtomsApproximable terms happ bias hsum
  have hcard : Fintype.card ((j : Fin 3) × Fin (sizes j)) = H + 2 ^ a + 2 ^ b := by
    simp [Fintype.card_sigma, sizes, Fin.sum_univ_three]
  rwa [hcard] at hcomp

/-- The exceptional-face correction budget in the unchanged `HStar` invariant. -/
theorem HStar_le_repair_two_positive_faces {n H a b : ℕ}
    (rho : CoordFace a n) (tau : CoordFace b n)
    (hrho : ∀ i, rho.base i = true) (htau : ∀ i, tau.base i = true)
    (φ : Fin H → FracAtom n) (bias : ℝ) (f : (Fin n → Bool) → Bool)
    (houtside : ∀ bits, ¬OnPositiveFace rho bits → ¬OnPositiveFace tau bits →
      (0 < bias + ∑ h, (φ h).eval bits ↔ f bits = true) ∧
        bias + ∑ h, (φ h).eval bits ≠ 0) :
    HStar n f ≤ H + 2 ^ a + 2 ^ b :=
  HStar_le_of_computableWithHeadsN
    (repair_two_positive_faces rho tau hrho htau φ bias f houtside)

end AxisZeroGluing
end HeadComplexity
