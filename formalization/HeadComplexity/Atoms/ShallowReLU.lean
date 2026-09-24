import HeadComplexity.Model.MLP
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.HeadToFracAtom
import HeadComplexity.Results.LowComplexity
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Shallow ReLU scores and the common-denominator reduction

The affine skip term is free; `m` counts only hidden ReLU units. The forward
reduction uses the existing scalar numerator and denominator lemmas row by row.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

/-- Boolean classification by a shallow ReLU score with an affine skip term. -/
def shallowReLUComputable (n m : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (b₀ : ℝ) (b : Fin n → ℝ) (a₀ : Fin m → ℝ)
    (a : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
    ∀ x, (0 < affineValue b₀ b x + ∑ j, c j * relu (affineValue (a₀ j) (a j) x)) ↔
      f x = true

/-- Least width of a shallow ReLU classifier with an affine skip term. -/
noncomputable def ShallowReLUWidth (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact if h : ∃ m, shallowReLUComputable n m f then Nat.find h else 0

/-- Unused hidden units can be padded with zero output weights. -/
theorem shallowReLUComputable_mono {n m k : ℕ} {f : (Fin n → Bool) → Bool}
    (hmk : m ≤ k) (hf : shallowReLUComputable n m f) : shallowReLUComputable n k f := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmk
  obtain ⟨b₀, b, a₀, a, c, h⟩ := hf
  refine ⟨b₀, b, Fin.addCases a₀ (fun _ : Fin r => 0),
    Fin.addCases a (fun _ : Fin r => fun _ => 0), Fin.addCases c (fun _ : Fin r => 0), ?_⟩
  intro x
  simpa [Fin.sum_univ_add] using h x

/-- Every affine readout of the query residual has the head's common positive
denominator and an affine numerator. -/
theorem Head.exists_affine_residual_readout {n d : ℕ} (H : Head n d)
    (w : Vec d) (t : ℝ) :
    ∃ (c : ℝ) (cs : Fin n → ℝ), ∀ x,
      ⟪w, H.residual x⟫_ℝ + t = affineValue c cs x / H.denominator x := by
  obtain ⟨N, hN, hNx⟩ := H.exists_numPoly w
  obtain ⟨D, hD, hDx⟩ := H.exists_denomPoly
  let k := ⟪w, H.queryVec⟫_ℝ + t
  refine ⟨N.coeff 0 + k * D.coeff 0,
    fun i => N.coeff (Finsupp.single i 1) + k * D.coeff (Finsupp.single i 1), ?_⟩
  intro x
  have hn : affineValue (N.coeff 0) (fun i => N.coeff (Finsupp.single i 1)) x =
      ⟪w, H.numerator x⟫_ℝ :=
    (eval_cubePoint_affine N hN x).symm.trans (hNx x)
  have hd : affineValue (D.coeff 0) (fun i => D.coeff (Finsupp.single i 1)) x =
      H.denominator x := (eval_cubePoint_affine D hD x).symm.trans (hDx x)
  rw [affineValue_add, affineValue_smul, hn, hd]
  simp only [Head.residual, inner_add_right, H.x_none_eq_queryVec, Head.attnUpdate,
    inner_smul_right]
  dsimp [k]
  field_simp [H.denominator_ne_zero x]
  ring

/-- Lemmas 2.1 to 2.4 of the write-up: clearing the common positive denominator
turns one head plus a residual ReLU MLP into a shallow classifier of the same width. -/
theorem shallowReLUComputable_of_oneHeadMLP {n m : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : computableWithOneHeadMLP n m f) :
    shallowReLUComputable n m f := by
  classical
  obtain ⟨d, H, M, w, τ, hsign⟩ := hf
  obtain ⟨b₀, b, hb⟩ := H.exists_affine_residual_readout w (⟪w, M.b2⟫_ℝ - τ)
  have hh := fun j : Fin m => H.exists_affine_residual_readout
    (LinearMap.adjoint M.W1 (EuclideanSpace.single j 1)) (M.b1 j)
  choose a₀ a ha using hh
  let c := LinearMap.adjoint M.W2 w
  refine ⟨b₀, b, a₀, a, fun j => c j, fun x => ?_⟩
  have hpre (j : Fin m) : (M.W1 (H.residual x) + M.b1) j =
      affineValue (a₀ j) (a j) x / H.denominator x := by
    simpa [LinearMap.adjoint_inner_left, EuclideanSpace.inner_single_left] using ha j x
  have hscore : ⟪w, M.eval (H.residual x)⟫_ℝ - τ =
      (affineValue b₀ b x + ∑ j, c j * relu (affineValue (a₀ j) (a j) x)) /
        H.denominator x := by
    simp only [ResidualMLP.eval, inner_add_right]
    rw [← LinearMap.adjoint_inner_left, vecN_inner (LinearMap.adjoint M.W2 w)]
    simp only [reluVec_apply, hpre, relu_div _ _ (H.denominator_pos x)]
    rw [show ⟪w, H.residual x⟫_ℝ +
        (∑ j, c j * (relu (affineValue (a₀ j) (a j) x) / H.denominator x)) +
        ⟪w, M.b2⟫_ℝ - τ =
        (⟪w, H.residual x⟫_ℝ + (⟪w, M.b2⟫_ℝ - τ)) +
        ∑ j, c j * (relu (affineValue (a₀ j) (a j) x) / H.denominator x) by ring]
    rw [hb x]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, ← add_div]
  rw [← div_pos_iff_of_pos_right (H.denominator_pos x), ← hscore, sub_pos]
  exact hsign x

end HeadComplexity
