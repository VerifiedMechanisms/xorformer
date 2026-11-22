import HeadComplexity.Atoms.CoordinateZeroFinite

set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace HeadComplexity.CoordinateZeroFiber
open scoped BigOperators

theorem bit_low_half (k : ℕ) (j : Fin 256) (i : Fin 8) :
    bit (256 * k + j.val) i.val = bit j.val i.val := by
  fin_cases i <;> norm_num [bit] <;> omega

theorem bit_high_half (k : ℕ) (j : Fin 256) (i : Fin 8) :
    bit (256 * k + j.val) (8 + i.val) = bit k i.val := by
  fin_cases i <;> norm_num [bit] <;> omega

def lowDot (a : Fin 16 → ℤ) (j : ℕ) : ℤ :=
  ∑ i : Fin 8, a (Fin.castAdd 8 i) * bit j i.val

def highDot (a : Fin 16 → ℤ) (k : ℕ) : ℤ :=
  ∑ i : Fin 8, a (Fin.natAdd 8 i) * bit k i.val

theorem dot_split (a : Fin 16 → ℤ) (k : ℕ) (j : Fin 256) :
    dot a (256 * k + j.val) = lowDot a j.val + highDot a k := by
  unfold dot lowDot highDot
  rw [Fin.sum_univ_add (a := 8) (b := 8)]
  simp only [Fin.val_castAdd, Fin.val_natAdd, bit_low_half, bit_high_half]

theorem den_split (h : Fin 3) (k : ℕ) (j : Fin 256) :
    den h (256 * k + j.val) =
      1 + lowDot (denominatorSlopes h) j.val + highDot (denominatorSlopes h) k := by
  rw [den, dot_split]
  ring

theorem num_split (h : Fin 3) (k : ℕ) (j : Fin 256) :
    num h (256 * k + j.val) =
      lowDot (numeratorScaledSlopes h) j.val + highDot (numeratorScaledSlopes h) k := by
  exact dot_split (numeratorScaledSlopes h) k j

#print axioms dot_split

end HeadComplexity.CoordinateZeroFiber
