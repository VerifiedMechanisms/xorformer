import HeadComplexity.Analysis.RoPEFrequencies
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-! # Exact real interpolation by finite rotary features

A complex Vandermonde inverse supplies weights at distinct unit-circle nodes.
Absorbing the query phase and taking real parts yields real cosine and sine
weights. No interpolation or rank hypothesis is assumed beyond node injectivity.
-/

namespace HeadComplexity.RoPEInterpolation

noncomputable section
open scoped BigOperators

/-- Distinct complex phase nodes interpolate an arbitrary finite real sequence,
with any real shift in the position argument. -/
theorem interpolate_square {m : ℕ} (ω : Fin m → ℝ)
    (hinj : Function.Injective (fun r ↦ Complex.exp ((ω r : ℂ) * Complex.I)))
    (ℓ : Fin m → ℝ) (q : ℝ) :
    ∃ u v : Fin m → ℝ, ∀ i : Fin m,
      (∑ r, (Real.cos (((i.val : ℝ) - q) * ω r) * u r +
        Real.sin (((i.val : ℝ) - q) * ω r) * v r)) = ℓ i := by
  classical
  let nodes : Fin m → ℂ := fun r ↦ Complex.exp ((ω r : ℂ) * Complex.I)
  let V : Matrix (Fin m) (Fin m) ℂ := (Matrix.vandermonde nodes).transpose
  have hdet : V.det ≠ 0 := by
    change (Matrix.vandermonde nodes).transpose.det ≠ 0
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hsurj : Function.Surjective V.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨c, hc⟩ := hsurj (fun i ↦ (ℓ i : ℂ))
  have hc' (i : Fin m) : (∑ r, (nodes r)^i.val * c r) = (ℓ i : ℂ) := by
    exact congrFun hc i
  let w : Fin m → ℂ := fun r ↦ Complex.exp ((q * ω r : ℝ) * Complex.I) * c r
  have hphase (i r : Fin m) :
      Complex.exp ((((i.val : ℝ) - q) * ω r : ℝ) * Complex.I) * w r =
        (nodes r)^i.val * c r := by
    dsimp [w, nodes]
    rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  refine ⟨fun r ↦ (w r).re, fun r ↦ -(w r).im, ?_⟩
  intro i
  have hcomplex : (∑ r,
      Complex.exp ((((i.val : ℝ) - q) * ω r : ℝ) * Complex.I) * w r) =
        (ℓ i : ℂ) := by
    simpa only [hphase] using hc' i
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.re_sum, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, mul_neg, sub_eq_add_neg] using hreal

/-- Extra frequency blocks may be padded by prescribing any values at the extra
positions. In particular, at least as many distinct nodes as input positions
suffice. -/
theorem interpolate_of_nodes_injective {n m : ℕ} (hn : n ≤ m)
    (ω : Fin m → ℝ)
    (hinj : Function.Injective (fun r ↦ Complex.exp ((ω r : ℂ) * Complex.I)))
    (ℓ : Fin n → ℝ) (q : ℝ) :
    ∃ u v : Fin m → ℝ, ∀ i : Fin n,
      (∑ r, (Real.cos (((i.val : ℝ) - q) * ω r) * u r +
        Real.sin (((i.val : ℝ) - q) * ω r) * v r)) = ℓ i := by
  classical
  let extended : Fin m → ℝ := fun i ↦ if hi : i.val < n then ℓ ⟨i.val, hi⟩ else 0
  obtain ⟨u, v, huv⟩ := interpolate_square ω hinj extended q
  refine ⟨u, v, fun i ↦ ?_⟩
  simpa [extended, i.isLt] using huv (Fin.castLE hn i)

/-- The standard RoPE schedule realizes arbitrary finite logits at any fixed
query position, using `m` rotary frequency pairs. -/
theorem interpolate_standard {n m : ℕ} (hn : n ≤ m) (hm : 0 < m)
    (ℓ : Fin n → ℝ) (q : ℝ) :
    ∃ u v : Fin m → ℝ, ∀ i : Fin n,
      (∑ r, (Real.cos (((i.val : ℝ) - q) * RoPEFrequencies.frequency m r) * u r +
        Real.sin (((i.val : ℝ) - q) * RoPEFrequencies.frequency m r) * v r)) = ℓ i := by
  exact interpolate_of_nodes_injective hn (RoPEFrequencies.frequency m)
    (RoPEFrequencies.node_injective hm) ℓ q

/-- A concrete finite width choice convenient for a shared token embedding
construction. -/
theorem interpolate_standard_add_two {n : ℕ} (ℓ : Fin n → ℝ) (q : ℝ) :
    ∃ u v : Fin (n + 2) → ℝ, ∀ i : Fin n,
      (∑ r, (Real.cos (((i.val : ℝ) - q) * RoPEFrequencies.frequency (n + 2) r) * u r +
        Real.sin (((i.val : ℝ) - q) * RoPEFrequencies.frequency (n + 2) r) * v r)) = ℓ i := by
  exact interpolate_standard (by omega) (by omega) ℓ q

end
end HeadComplexity.RoPEInterpolation
