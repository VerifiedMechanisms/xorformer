import HeadComplexity.Results.LargeDomainGridRouting

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- A vertex is adjacent to a grid interval with the displayed integer index. -/
def gridAdjacent (v t : ℕ) : Prop := v = t ∨ v = t + 1

/-- A coarse gate survives at the input selecting both intervals adjacent to
an interior vertex in every coordinate precisely when it is adjacent to all
of those selected intervals. -/
def gridDoubleCompatible {a m : ℕ}
    (v w : Fin a → Fin (m + 1)) : Prop :=
  ∀ i, gridAdjacent (w i).val ((v i).val - 1) ∧
    gridAdjacent (w i).val (v i).val

theorem grid_double_compatible_iff {a m : ℕ}
    (v w : Fin a → Fin (m + 1)) (hv : ∀ i, 0 < (v i).val) :
    gridDoubleCompatible v w ↔ w = v := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have hi := h i
    have hvi := hv i
    simp only [gridAdjacent] at hi
    omega
  · rintro rfl i
    constructor
    · right
      have := hv i
      omega
    · exact Or.inl rfl

/-- At the all-double input belonging to an interior vertex, the entire
coarse gated family reduces to that single vertex's contribution. -/
theorem grid_double_score_eq {a m : ℕ}
    (v : Fin a → Fin (m + 1)) (hv : ∀ i, 0 < (v i).val)
    (R : (Fin a → Fin (m + 1)) → ℝ) :
    (∑ w, if gridDoubleCompatible v w then R w else 0) = R v := by
  classical
  simp only [grid_double_compatible_iff v _ hv]
  simp

/-- Lower-layer vanishing of the unmodified gated tangent forces the product
of its column amplitude and query coefficient to vanish at every interior
vertex. This is a support obstruction, not an impossibility theorem for
arbitrary sums of original-model heads. -/
theorem grid_double_zero_forces_residue {a m : ℕ}
    (v : Fin a → Fin (m + 1)) (hv : ∀ i, 0 < (v i).val)
    (c q D : (Fin a → Fin (m + 1)) → ℝ)
    (hD : D v ≠ 0)
    (hzero : (∑ w, if gridDoubleCompatible v w then
      c w * q w / D w ^ 2 else 0) = 0) : c v * q v = 0 := by
  classical
  rw [grid_double_score_eq v hv] at hzero
  exact (div_eq_zero_iff.mp hzero).resolve_right (pow_ne_zero _ hD)

end HeadComplexity.LargeDomain
