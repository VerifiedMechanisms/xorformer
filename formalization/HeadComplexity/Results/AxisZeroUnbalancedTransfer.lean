import HeadComplexity.Results.AxisZeroTransfer
import HeadComplexity.Results.AxisZeroStarFaces

set_option linter.style.header false

/-!
# Product-cover transfer with star costs on exceptional faces

These new theorems retain the original local compiler hypothesis and model.
They replace the exponential face correction by the smaller already proved
monomial star-cover budget, enabling highly unbalanced block dimensions.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Finset
open scoped BigOperators

/-- Complete finite cover transfer, including both exceptional faces, in the
unchanged `HStar` invariant. The only unproved input is the explicitly stated
local compiler hypothesis. -/
theorem HStar_le_product_cover_of_compiler_star_faces {a b M : ℕ}
    (hcompiler : HasReverseAxisCompiler a b M)
    (D : Finset (Finset (Fin a))) (E : Finset (Finset (Fin b)))
    (hD : OpenDownwardCovers D) (hE : OpenDownwardCovers E)
    (f : (Fin (a + b) → Bool) → Bool) :
    HStar (a + b) f ≤ (D ×ˢ E).card * M +
      monomialStarCoverNumber a + monomialStarCoverNumber b := by
  classical
  let P := D ×ˢ E
  obtain ⟨center, _hmem, hcover, horder⟩ :=
    enumerate_descending P (fun ST ↦ ST.1.card + ST.2.card)
  let S (i : ℕ) := (center i).1
  let T (i : ℕ) := (center i).2
  have hex (i : ℕ) : ∃ H ≤ M, ∃ L : ReverseAxisData a b H,
      ∀ k l, 0 < outputSign (f (centerBits ((S i).erase k) ((T i).erase l))) *
        L.score (localGrid k l) :=
    hcompiler (fun k l ↦ f (centerBits ((S i).erase k) ((T i).erase l)))
  choose H hH L hsign using hex
  obtain ⟨φ, hφ⟩ := glue_reverse_axis_modules P.card H S T L f horder
    (fun i _ ↦ hsign i)
  let I := ((i : Fin P.card) × Fin (H i.val))
  let equiv : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ψ : Fin (Fintype.card I) → FracAtom (a + b) := fun h ↦ φ (equiv h)
  have hsum (bits : Fin (a + b) → Bool) :
      (∑ h, (ψ h).eval bits) = ∑ h, (φ h).eval bits :=
    equiv.sum_comp (fun h ↦ (φ h).eval bits)
  have houtside (bits : Fin (a + b) → Bool)
      (hleft : ¬OnPositiveFace (leftFullFace a b) bits)
      (hright : ¬OnPositiveFace (rightFullFace a b) bits) :
      (0 < 0 + ∑ h, (ψ h).eval bits ↔ f bits = true) ∧
        0 + ∑ h, (ψ h).eval bits ≠ 0 := by
    have hX : leftOnes bits ≠ Finset.univ :=
      fun h ↦ hleft (on_leftFullFace_of_leftOnes bits h)
    have hY : rightOnes bits ≠ Finset.univ :=
      fun h ↦ hright (on_rightFullFace_of_rightOnes bits h)
    obtain ⟨ST, hST, hS, hT⟩ :=
      product_openDownwardCover D E hD hE (leftOnes bits) (rightOnes bits) hX hY
    obtain ⟨i, hi, hcenter⟩ := hcover ST hST
    have hcell : bits ∈ starCell (S i) (T i) := by
      simp only [starCell, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [S, T]
      rw [hcenter]
      exact ⟨hS, hT⟩
    have hpos := hφ bits ⟨i, hi, hcell⟩
    simpa only [zero_add, hsum] using strict_of_outputSign hpos
  have hrepair := HStar_le_repair_two_positive_faces_star
    (leftFullFace a b) (rightFullFace a b) (fun _ ↦ rfl) (fun _ ↦ rfl)
    ψ 0 f houtside
  have hcount : Fintype.card I ≤ P.card * M := by
    rw [show Fintype.card I = ∑ i ∈ Finset.range P.card, H i from glued_head_count _ _]
    calc
      ∑ i ∈ Finset.range P.card, H i ≤ ∑ _i ∈ Finset.range P.card, M :=
        Finset.sum_le_sum (fun i _ ↦ hH i)
      _ = P.card * M := by simp
  dsimp [P] at hrepair hcount ⊢
  omega

/-- Explicit full head budget from a local reverse compiler: the audited
product cover contributes at most `484 * 2^(a+b)/(a*b)` modules, and the
exceptional faces cost the sum of their monomial star-cover numbers. -/
theorem HStar_real_le_of_reverse_axis_compiler_star_faces {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcompiler : HasReverseAxisCompiler a b M)
    (f : (Fin (a + b) → Bool) → Bool) :
    (HStar (a + b) f : ℝ) ≤
      484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
      monomialStarCoverNumber a + monomialStarCoverNumber b := by
  obtain ⟨D, E, hD, hE, hcount⟩ := exists_product_openDownwardCover a b ha hb
  have hfinite := HStar_le_product_cover_of_compiler_star_faces hcompiler D E hD hE f
  have hcast : (HStar (a + b) f : ℝ) ≤
      ((D ×ˢ E).card : ℝ) * M +
        (monomialStarCoverNumber a : ℝ) + (monomialStarCoverNumber b : ℝ) := by
    exact_mod_cast hfinite
  calc
    (HStar (a + b) f : ℝ) ≤
        ((D ×ˢ E).card : ℝ) * M +
        (monomialStarCoverNumber a : ℝ) + (monomialStarCoverNumber b : ℝ) := hcast
    _ ≤ (484 * (2 : ℝ) ^ (a + b) / ((a : ℝ) * b)) * M +
      monomialStarCoverNumber a + monomialStarCoverNumber b := by
      gcongr
    _ = 484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
      monomialStarCoverNumber a + monomialStarCoverNumber b := by ring

/-- Worst-case form of the complete conditional transfer, using the original
definition of `worstCaseHeadComplexity`. A saving requires a proved sublinear
instance of `HasReverseAxisCompiler`. -/
theorem worstCaseHeadComplexity_real_le_of_reverse_axis_compiler_star_faces {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcompiler : HasReverseAxisCompiler a b M) :
    (worstCaseHeadComplexity (a + b) : ℝ) ≤
      484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
      monomialStarCoverNumber a + monomialStarCoverNumber b := by
  let B : ℝ := 484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
      monomialStarCoverNumber a + monomialStarCoverNumber b
  have hnat : worstCaseHeadComplexity (a + b) ≤ ⌊B⌋₊ := by
    apply Finset.sup_le
    intro f _
    exact Nat.le_floor (HStar_real_le_of_reverse_axis_compiler_star_faces ha hb hcompiler f)
  exact (by exact_mod_cast hnat : (worstCaseHeadComplexity (a + b) : ℝ) ≤ (⌊B⌋₊ : ℝ)).trans
    (Nat.floor_le (by dsimp [B]; positivity))


/-- Explicit numerical version of the star-face budget. Both free dimensions
may be unbalanced; the old exponential face terms are divided by dimension. -/
theorem worstCaseHeadComplexity_real_le_of_reverse_axis_compiler_star_faces_eleven
    {a b M : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcompiler : HasReverseAxisCompiler a b M) :
    (worstCaseHeadComplexity (a + b) : ℝ) ≤
      484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
        11 * (2 : ℝ) ^ a / a + 11 * (2 : ℝ) ^ b / b := by
  exact (worstCaseHeadComplexity_real_le_of_reverse_axis_compiler_star_faces
    ha hb hcompiler).trans
      (add_le_add (add_le_add_right
        (monomialStarCoverNumber_real_le_eleven a ha) _)
        (monomialStarCoverNumber_real_le_eleven b hb))


end AxisZeroGluing
end HeadComplexity
