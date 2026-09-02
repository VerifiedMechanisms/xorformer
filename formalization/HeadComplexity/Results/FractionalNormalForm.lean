import HeadComplexity.Atoms.FracAtomHead
import HeadComplexity.Atoms.HeadToFracAtom
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Theorem 10 — `H*(f) = L_frac(f)` (capstone).

Combining the two directions (`fracComputable_of_computable` and
`computable_of_fracComputable`) gives, for every `H`, that computability with `H`
heads is equivalent to representability by `H` linear-fractional atoms; hence the
two least-counts coincide.
-/

namespace HeadComplexity

variable {n : ℕ}

/-- Per-head-count equivalence: `H` heads ⟺ `H` atoms. -/
theorem computableWithHeadsN_iff_fracComputable (H : ℕ) (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H f ↔ fracComputable n H f :=
  ⟨fracComputable_of_computable, computable_of_fracComputable⟩

/-- Theorem 10 for the literal model from `model.md`: shared-embedding
computability with `H` heads is equivalent to `H` fractional atoms. -/
theorem computableWithSharedHeadsN_iff_fracComputable
    (H : ℕ) (f : (Fin n → Bool) → Bool) :
    computableWithSharedHeadsN n H f ↔ fracComputable n H f :=
  (computableWithHeadsN_iff_computableWithSharedHeadsN n H f).symm.trans
    (computableWithHeadsN_iff_fracComputable H f)

/-- **Theorem 10.** The head complexity equals the linear-fractional complexity. -/
theorem HStar_eq_Lfrac (f : (Fin n → Bool) → Bool) : HStar n f = Lfrac n f := by
  classical
  have hiff := computableWithHeadsN_iff_fracComputable (n := n) (f := f)
  have hexC : ∃ k, computableWithHeadsN n k f := exists_computable f
  have hexF : ∃ H, fracComputable n H f := hexC.imp fun k => (hiff k).mp
  unfold HStar Lfrac
  rw [dif_pos hexC, dif_pos hexF]
  refine le_antisymm ?_ ?_
  · exact Nat.find_min' hexC ((hiff _).mpr (Nat.find_spec hexF))
  · exact Nat.find_min' hexF ((hiff _).mp (Nat.find_spec hexC))

/-- Theorem 10 stated with the least head count of the literal shared-embedding
model from `model.md`. -/
theorem SharedHStar_eq_Lfrac (f : (Fin n → Bool) → Bool) :
    SharedHStar n f = Lfrac n f :=
  (SharedHStar_eq_HStar n f).trans (HStar_eq_Lfrac f)

end HeadComplexity
