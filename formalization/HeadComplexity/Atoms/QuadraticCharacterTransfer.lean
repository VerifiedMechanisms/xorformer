import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! A finite obstruction to replacing real signs by quadratic characters.
All real affine numerators below are strictly positive. Their quadratic
characters nevertheless realize every sign table on eight inputs. -/
namespace HeadComplexity.QuadraticCharacterTransfer

instance : Fact (Nat.Prime 1367) := ⟨by norm_num⟩

def seeds : Fin 256 → ℕ :=
  ![637, 499, 635, 498, 412, 330, 278, 316, 411, 421, 371, 35, 246, 558, 439, 184,
    844, 212, 290, 8, 208, 340, 34, 663, 217, 276, 15, 97, 438, 429, 240, 183,
    564, 38, 211, 432, 405, 271, 7, 129, 135, 202, 369, 105, 33, 67, 399, 169,
    263, 216, 139, 303, 14, 4, 161, 96, 824, 154, 45, 713, 197, 239, 126, 182,
    563, 318, 37, 441, 10, 210, 646, 431, 40, 404, 204, 288, 141, 6, 605, 128,
    320, 134, 206, 201, 878, 77, 104, 23, 102, 32, 66, 61, 21, 83, 168, 364,
    415, 262, 215, 100, 274, 108, 30, 157, 13, 144, 26, 3, 160, 59, 56, 476,
    250, 19, 71, 49, 44, 81, 382, 53, 222, 166, 446, 238, 125, 233, 312, 181,
    500, 589, 331, 279, 422, 36, 247, 185, 213, 9, 209, 488, 218, 16, 430, 241,
    39, 433, 272, 578, 136, 106, 68, 170, 264, 140, 5, 162, 155, 46, 198, 127,
    319, 374, 11, 932, 41, 205, 142, 200, 376, 877, 78, 24, 103, 62, 22, 1,
    503, 101, 109, 31, 145, 65, 60, 57, 20, 50, 82, 54, 167, 447, 234, 354,
    501, 280, 1076, 186, 214, 342, 17, 242, 434, 273, 107, 69, 301, 29, 47, 193,
    425, 12, 42, 143, 377, 25, 63, 2, 394, 159, 115, 58, 51, 55, 509, 235,
    281, 187, 465, 18, 435, 70, 164, 48, 426, 43, 80, 86, 395, 381, 52, 236,
    188, 221, 123, 165, 309, 529, 506, 177, 189, 124, 310, 178, 352, 179, 180, 361]

def labels (i : Fin 256) (t : Fin 8) : Bool :=
  decide (i.val / 2 ^ t.val % 2 = 1)

def fastPow (z : ℕ) : ℕ :=
  let z2 := z * z % 1367
  let z4 := z2 * z2 % 1367
  let z8 := z4 * z4 % 1367
  let z16 := z8 * z8 % 1367
  let z32 := z16 * z16 % 1367
  let z64 := z32 * z32 % 1367
  let z128 := z64 * z64 % 1367
  let z256 := z128 * z128 % 1367
  let z512 := z256 * z256 % 1367
  (((((z512 * z128 % 1367) * z32 % 1367) * z8 % 1367) * z2 % 1367) * z) % 1367

theorem fastPow_eq (z : ℕ) : (fastPow z : ZMod 1367) = (z : ZMod 1367) ^ 683 := by
  dsimp [fastPow]
  simp only [ZMod.natCast_mod, Nat.cast_mul]
  ring

theorem seeds_positive : ∀ i, 0 < seeds i := by
  decide +kernel

theorem labels_surjective (f : Fin 8 → Bool) : ∃ i, labels i = f := by
  let bits : Fin 8 → Fin 2 := fun t => if f t then 1 else 0
  let i : Fin 256 := finFunctionFinEquiv bits
  refine ⟨i, funext fun t => ?_⟩
  have hd := congrArg (fun g : Fin 8 → Fin 2 => (g t).val)
    (finFunctionFinEquiv.symm_apply_apply bits)
  change i.val / 2 ^ t.val % 2 = (bits t).val at hd
  unfold labels
  rw [hd]
  cases hf : f t <;> simp [bits, hf]

theorem seeds_small : ∀ i, seeds i ≤ 1076 := by
  decide +kernel

theorem inputs_nonzero (i : Fin 256) (t : Fin 8) :
    ((seeds i + t.val : ℕ) : ZMod 1367) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  apply Nat.not_dvd_of_pos_of_lt
  · have := seeds_positive i
    omega
  · have := seeds_small i
    omega

theorem modular_signs : ∀ (i : Fin 256) (t : Fin 8), fastPow (seeds i + t.val) =
    if labels i t then 1 else 1366 := by
  decide +kernel

theorem character_signs (i : Fin 256) (t : Fin 8) :
    legendreSym 1367 (seeds i + t.val : ℕ) = if labels i t then 1 else -1 := by
  have hnonzero : (((seeds i + t.val : ℕ) : ℤ) : ZMod 1367) ≠ 0 := by
    simpa only [Int.cast_natCast] using inputs_nonzero i t
  have hp := legendreSym.eq_pow 1367 (seeds i + t.val : ℕ)
  have hm := congrArg (fun a : ℕ => (a : ZMod 1367)) (modular_signs i t)
  rw [fastPow_eq] at hm
  push_cast at hm
  have h1366 : (1366 : ZMod 1367) = -1 := by decide +kernel
  rw [h1366] at hm
  norm_num only [Int.cast_natCast] at hp
  push_cast at hp
  rcases legendreSym.eq_one_or_neg_one 1367 hnonzero with h | h
  · push_cast at h ⊢
    rw [h] at hp ⊢
    cases hl : labels i t
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      have hz : (1 : ZMod 1367) = -1 := hp.trans hm
      exact False.elim ((by decide +kernel : (1 : ZMod 1367) ≠ -1) hz)
    · simp
  · push_cast at h ⊢
    rw [h] at hp ⊢
    cases hl : labels i t
    · simp
    · simp only [hl, ↓reduceIte] at hm ⊢
      have hz : (-1 : ZMod 1367) = 1 := hp.trans hm
      exact False.elim ((by decide +kernel : (1 : ZMod 1367) ≠ -1) hz.symm)

theorem eight_character_tests_shattered (f : Fin 8 → Bool) :
    ∃ a : ℕ, 0 < a ∧ ∀ t : Fin 8,
      (0 : ℝ) < (a : ℝ) + t.val ∧
      legendreSym 1367 (a + t.val : ℕ) = if f t then 1 else -1 := by
  obtain ⟨i, hi⟩ := labels_surjective f
  refine ⟨seeds i, seeds_positive i, fun t => ⟨?_, ?_⟩⟩
  · exact add_pos_of_pos_of_nonneg (by exact_mod_cast seeds_positive i) (Nat.cast_nonneg _)
  · simpa only [hi] using character_signs i t

#print axioms eight_character_tests_shattered
end HeadComplexity.QuadraticCharacterTransfer
