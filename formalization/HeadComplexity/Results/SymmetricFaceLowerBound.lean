import HeadComplexity.Atoms.Restriction
import HeadComplexity.Polynomial.UnivariateReduction
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Restriction corollary of symmetric sign-change exactness

Head complexity cannot increase when inputs are restricted to a coordinate
face. Consequently, an arbitrary Boolean function inherits the sign-change
lower bound of every symmetric function appearing on one of its faces.

This machine-checks the coordinate-face instance of the existing restriction
monotonicity and symmetric sign-change results. It is a reusable corollary of
those results, not a separate mathematical theorem claim.

The final certificate theorem applies to globally nonsymmetric functions. It
packages a face, its symmetric profile, and a numerical sign-change bound into
one reusable hypothesis.
-/

namespace HeadComplexity

variable {m n H : ℕ}

/-- Restricting input coordinates cannot increase `HStar`. -/
theorem HStar_restrict_le (rho : CoordFace m n) (f : (Fin n → Bool) → Bool) :
    HStar m (fun x => f (rho.apply x)) ≤ HStar n f := by
  classical
  unfold HStar
  rw [dif_pos ⟨HStar n f, computableWithHeadsN.restrict rho (HStar_computable f)⟩]
  exact Nat.find_min' _ (computableWithHeadsN.restrict rho (HStar_computable f))

/-- If the restriction of an `H`-head function to a coordinate face is
symmetric, the profile has at most `H` sign changes. -/
theorem signChanges_le_of_symmetric_face {f : (Fin n → Bool) → Bool}
    (rho : CoordFace m n) (F : ℕ → Bool)
    (hf : computableWithHeadsN n H f)
    (hsym : ∀ x, f (rho.apply x) = symmetricFn F x) :
    signChanges m F ≤ H := by
  apply signChanges_le_of_computableWithHeadsN
  rw [← funext hsym]
  exact computableWithHeadsN.restrict rho hf

/-- Every symmetric coordinate face of an arbitrary Boolean function gives an
`HStar` lower bound. The ambient function itself need not be symmetric. -/
theorem signChanges_le_HStar_of_symmetric_face (f : (Fin n → Bool) → Bool)
    (rho : CoordFace m n) (F : ℕ → Bool)
    (hsym : ∀ x, f (rho.apply x) = symmetricFn F x) :
    signChanges m F ≤ HStar n f :=
  signChanges_le_of_symmetric_face rho F (HStar_computable f) hsym

/-- A checkable certificate that an arbitrary Boolean function contains a
symmetric coordinate face with at least `k` sign changes. -/
def HasSymmetricFaceBound (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (rho : CoordFace m n) (F : ℕ → Bool),
    k ≤ signChanges m F ∧ ∀ x, f (rho.apply x) = symmetricFn F x

/-- A symmetric-face certificate lower-bounds the head complexity of any
Boolean function, including globally nonsymmetric functions. -/
theorem HasSymmetricFaceBound.le_HStar {f : (Fin n → Bool) → Bool} {k : ℕ}
    (h : HasSymmetricFaceBound f k) : k ≤ HStar n f := by
  rcases h with ⟨m, rho, F, hk, hsym⟩
  exact hk.trans (signChanges_le_HStar_of_symmetric_face f rho F hsym)

/-- Result-facing form of the general symmetric-face lower bound. -/
theorem HStar_lower_bound_of_symmetric_face {f : (Fin n → Bool) → Bool} {k : ℕ}
    (h : HasSymmetricFaceBound f k) : k ≤ HStar n f :=
  h.le_HStar

end HeadComplexity
