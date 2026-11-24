import HeadComplexity.Polynomial.ThreeHeadTripartiteCross

set_option linter.style.header false

/-!
# Exact parity extraction from a three-head affine score

The alternating sum on a three-dimensional affine Boolean face extracts its
cubic coefficient. All numerator and denominator intercepts cancel exactly.
-/

namespace HeadComplexity.ThreeHeadCubicFace

noncomputable section

open scoped BigOperators
open ThreeHeadTripartiteCross

def cleared (c : ℝ) (N D : Fin 3 → ℝ) : ℝ :=
  c * D 0 * D 1 * D 2 + N 0 * D 1 * D 2 + N 1 * D 0 * D 2 + N 2 * D 0 * D 1

theorem cleared_eq (c : ℝ) (N D : Fin 3 → ℝ) (hD : ∀ h, D h ≠ 0) :
    cleared c N D = (D 0 * D 1 * D 2) * (c + ∑ h, N h / D h) := by
  have h0 := hD 0
  have h1 := hD 1
  have h2 := hD 2
  simp [cleared, Fin.sum_univ_succ]
  field_simp
  ring

def face (c : ℝ) (n d AX AY AZ BX BY BZ : Fin 3 → ℝ) (u v w : ℝ) : ℝ :=
  cleared c (fun h ↦ n h + u * AX h + v * AY h + w * AZ h)
    (fun h ↦ d h + u * BX h + v * BY h + w * BZ h)

def alternating (F : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  F 1 1 1 - F 1 1 0 - F 1 0 1 - F 0 1 1 + F 1 0 0 + F 0 1 0 + F 0 0 1 - F 0 0 0

set_option maxHeartbeats 2000000 in
-- Expand all eight cubic evaluations before collecting the mixed coefficient.
theorem alternating_face (c : ℝ) (n d AX AY AZ BX BY BZ : Fin 3 → ℝ) :
    alternating (face c n d AX AY AZ BX BY BZ) = coefficient c AX AY AZ BX BY BZ := by
  simp [alternating, face, cleared, coefficient, middleFactor, pairFactor,
    other₀, other₁, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
-- The centered convention has eight expanded cubic evaluations as well.
/-- The centered sign-cube convention multiplies the same coefficient by eight. -/
theorem centered_alternating_face (c : ℝ) (n d AX AY AZ BX BY BZ : Fin 3 → ℝ) :
    let F := face c n d AX AY AZ BX BY BZ
    F 1 1 1 - F 1 1 (-1) - F 1 (-1) 1 - F (-1) 1 1 +
      F 1 (-1) (-1) + F (-1) 1 (-1) + F (-1) (-1) 1 - F (-1) (-1) (-1) =
        8 * coefficient c AX AY AZ BX BY BZ := by
  simp [face, cleared, coefficient, middleFactor, pairFactor,
    other₀, other₁, Fin.sum_univ_succ]
  ring

end
end HeadComplexity.ThreeHeadCubicFace
