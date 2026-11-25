import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.SameFaceScoreFiber
open Finset
open scoped BigOperators

/-- A genuine head whose score is exactly one on one whole coordinate face.
The denominator coefficients remain free on that face. -/
def atom {n : ℕ} (b : ℝ) (w : Fin n → ℝ) (j : Fin n) (T : ℝ)
    (hb : 0 < b) (hw : ∀ i, 0 < w i) : FracAtom n :=
  FracAtom.ofPositiveAffineRatio b (fun i => w i - if i = j then T else 0)
    b w hb hw

theorem atom_eval {n : ℕ} (b : ℝ) (w : Fin n → ℝ) (j : Fin n) (T : ℝ)
    (hb : 0 < b) (hw : ∀ i, 0 < w i) (x : Fin n → Bool) :
    (atom b w j T hb hw).eval x =
      (affineValue b w x - T * boolToReal (x j)) / affineValue b w x := by
  classical
  rw [atom, FracAtom.ofPositiveAffineRatio_eval]
  congr 1
  unfold affineValue
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp
  ring

theorem atom_eq_one_on_zeroFace {n : ℕ} (b : ℝ) (w : Fin n → ℝ)
    (j : Fin n) (T : ℝ) (hb : 0 < b) (hw : ∀ i, 0 < w i)
    (x : Fin n → Bool) (hx : x j = false) :
    (atom b w j T hb hw).eval x = 1 := by
  rw [atom_eval]
  have hB : 0 < affineValue b w x := by
    unfold affineValue
    have hs : 0 ≤ ∑ i, w i * boolToReal (x i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (by cases x i <;> norm_num [boolToReal])
    linarith
  simp [hx, boolToReal, hB.ne']

theorem exists_distinct_extensions_with_identical_face :
    ∃ φ ψ : FracAtom 3,
      (∀ x : Fin 3 → Bool, x 2 = false → φ.eval x = 1 ∧ ψ.eval x = 1) ∧
      φ.eval ![true, false, true] < 0 ∧
      0 < ψ.eval ![true, false, true] := by
  let w : Fin 3 → ℝ := ![1,1,1]
  let v : Fin 3 → ℝ := ![2,1,1]
  have hw : ∀ i, 0 < w i := by intro i; fin_cases i <;> norm_num [w]
  have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> norm_num [v]
  let φ := atom 1 w 2 (7/2) (by norm_num) hw
  let ψ := atom 1 v 2 (7/2) (by norm_num) hv
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨atom_eq_one_on_zeroFace 1 w 2 (7/2) (by norm_num) hw x hx,
      atom_eq_one_on_zeroFace 1 v 2 (7/2) (by norm_num) hv x hx⟩
  · dsimp [φ]
    rw [atom_eval]
    norm_num [affineValue, w, Fin.sum_univ_succ, boolToReal]
  · dsimp [ψ]
    rw [atom_eval]
    norm_num [affineValue, v, Fin.sum_univ_succ, boolToReal]

end HeadComplexity.SameFaceScoreFiber
