import HeadComplexity.Atoms.UniformApproximation
import HeadComplexity.Atoms.WalshApproximation

set_option linter.style.header false

/-!
# Uniform approximation by finite blocks of atoms

This module lifts the one-atom approximation interface to components whose
head counts may vary.  A dependent sum flattens all component atoms, and a
finite strict margin transfers the sign pattern to the approximation.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- A cube score can be approximated uniformly by a fixed finite type of
fractional atoms, together with a free constant term. -/
def UniformlyAtomsApproximable (ι : Type*) [Fintype ι]
    (g : (Fin n → Bool) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (φ : ι → FracAtom n) (c : ℝ),
      ∀ bits, |(c + ∑ i, (φ i).eval bits) - g bits| < ε

/-- The one-atom interface is the `Fin 1` case of the block interface. -/
theorem UniformlyOneAtomApproximable.toUniformlyAtomsApproximable
    {g : (Fin n → Bool) → ℝ} (hg : UniformlyOneAtomApproximable g) :
    UniformlyAtomsApproximable (Fin 1) g := by
  intro ε hε
  obtain ⟨φ, hφ⟩ := hg ε hε
  refine ⟨fun _ ↦ φ, 0, fun bits ↦ ?_⟩
  simpa using hφ bits

/-- A signed Walsh character on `S` is uniformly approximable by exactly
`|S|` atoms. -/
theorem uniformlyAtomsApproximable_walshCharacter
    (S : Finset (Fin n)) (coefficient : ℝ) :
    UniformlyAtomsApproximable (Fin S.card)
      (fun bits ↦ coefficient * walshCharacter S bits) := by
  intro ε hε
  exact exists_walsh_atoms_uniform S coefficient ε hε

/-- A finite family of variable-size atom blocks computes every strict sign
pattern represented by the sum of their target scores. -/
theorem computableWithHeadsCard_of_uniformlyAtomsApproximable
    {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]
    {f : (Fin n → Bool) → Bool}
    (g : J → (Fin n → Bool) → ℝ)
    (hg : ∀ j, UniformlyAtomsApproximable (I j) (g j))
    (bias : ℝ)
    (hstrict : StrictSignRepresentsScore (fun bits ↦ bias + ∑ j, g j bits) f) :
    computableWithHeadsN n (Fintype.card (Sigma I)) f := by
  classical
  let score : (Fin n → Bool) → ℝ := fun bits ↦ bias + ∑ j, g j bits
  obtain ⟨nearest, -, hmin⟩ :=
    (Finset.univ : Finset (Fin n → Bool)).exists_min_image
      (fun bits ↦ |score bits|) Finset.univ_nonempty
  let margin : ℝ := |score nearest|
  have hmargin : 0 < margin := abs_pos.mpr (hstrict nearest).2
  let ε : ℝ := margin / (Fintype.card J + 1 : ℝ)
  have hden : (0 : ℝ) < Fintype.card J + 1 := by positivity
  have hε : 0 < ε := div_pos hmargin hden
  choose φ c hφ using fun j ↦ hg j ε hε
  let ψ : Sigma I → FracAtom n := fun s ↦ φ s.1 s.2
  let e : Sigma I ≃ Fin (Fintype.card (Sigma I)) := Fintype.equivFin _
  apply computable_of_fracComputable
  refine ⟨fun h ↦ ψ (e.symm h), bias + ∑ j, c j, fun bits ↦ ?_⟩
  let approx : ℝ := bias + ∑ j, (c j + ∑ i, (φ j i).eval bits)
  have hreindex :
      (∑ h : Fin (Fintype.card (Sigma I)), (ψ (e.symm h)).eval bits) =
        ∑ j, ∑ i, (φ j i).eval bits := by
    calc
      (∑ h : Fin (Fintype.card (Sigma I)), (ψ (e.symm h)).eval bits) =
          ∑ s : Sigma I, (ψ s).eval bits := by
            simpa using e.symm.sum_comp (fun s ↦ (ψ s).eval bits)
      _ = ∑ j, ∑ i, (φ j i).eval bits := by
        simpa [ψ] using Fintype.sum_sigma (fun s : Sigma I ↦ (ψ s).eval bits)
  have hactual :
      bias + ∑ j, c j +
          ∑ h : Fin (Fintype.card (Sigma I)), (ψ (e.symm h)).eval bits = approx := by
    rw [hreindex]
    dsimp [approx]
    rw [Finset.sum_add_distrib]
    ring
  rw [hactual]
  have hpoint_margin : margin ≤ |score bits| :=
    hmin bits (Finset.mem_univ bits)
  have hdiff : approx - score bits =
      ∑ j, ((c j + ∑ i, (φ j i).eval bits) - g j bits) := by
    dsimp [approx, score]
    rw [Finset.sum_sub_distrib]
    ring
  have habs_diff : |approx - score bits| ≤
      ∑ j, |(c j + ∑ i, (φ j i).eval bits) - g j bits| := by
    rw [hdiff]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum_le :
      (∑ j, |(c j + ∑ i, (φ j i).eval bits) - g j bits|) ≤
        Fintype.card J * ε := by
    calc
      (∑ j, |(c j + ∑ i, (φ j i).eval bits) - g j bits|) ≤
          ∑ _j : J, ε := Finset.sum_le_sum fun j _ ↦ (hφ j bits).le
      _ = Fintype.card J * ε := by simp
  have hbudget : (Fintype.card J : ℝ) * ε < margin := by
    have hcard : (Fintype.card J : ℝ) < Fintype.card J + 1 := by norm_num
    have hratio := (div_lt_one hden).mpr hcard
    dsimp [ε]
    calc
      (Fintype.card J : ℝ) *
          (margin / (Fintype.card J + 1 : ℝ)) =
          margin * ((Fintype.card J : ℝ) /
            (Fintype.card J + 1 : ℝ)) := by ring
      _ < margin * 1 := mul_lt_mul_of_pos_left hratio hmargin
      _ = margin := mul_one margin
  have herr : |approx - score bits| < margin :=
    habs_diff.trans_lt (hsum_le.trans_lt hbudget)
  constructor
  · intro happ
    by_contra hftrue
    have hffalse : f bits = false := by
      cases hfb : f bits
      · rfl
      · exact (hftrue hfb).elim
    have hnpos : ¬0 < score bits := by
      intro hspos
      exact Bool.false_ne_true (hffalse.symm.trans ((hstrict bits).1.mp hspos))
    have hsneg : score bits < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnpos) (hstrict bits).2
    have hscore_le : score bits ≤ -margin := by
      have hm := hpoint_margin
      rw [abs_of_neg hsneg] at hm
      linarith
    have hupper : approx - score bits < margin := (abs_lt.mp herr).2
    linarith
  · intro hftrue
    have hspos : 0 < score bits := (hstrict bits).1.mpr hftrue
    have hmargin_le_score : margin ≤ score bits := by
      have hm := hpoint_margin
      rwa [abs_of_pos hspos] at hm
    have hlower : -margin < approx - score bits := (abs_lt.mp herr).1
    linarith

end HeadComplexity
