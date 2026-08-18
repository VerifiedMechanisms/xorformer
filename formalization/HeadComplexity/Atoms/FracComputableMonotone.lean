import HeadComplexity.Atoms.FracAtomHead
import HeadComplexity.Atoms.HeadToFracAtom

set_option linter.style.header false

/-!
# Padding fractional certificates

A fractional certificate can be enlarged by appending atoms with identically
zero output.  This records the monotonicity in the head-count parameter that
is needed to turn a fixed-size obstruction into an `HStar` lower bound.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace FracAtom

variable {n K H : ℕ}

/-- A valid fractional atom with identically zero output. -/
noncomputable def zero (n : ℕ) : FracAtom n where
  η := 0
  δ := 0
  γ := 1
  α := 1
  ρ := fun _ ↦ 1
  m := fun _ ↦ 0
  hγ := by norm_num
  hα := by norm_num
  hρ := fun _ ↦ by norm_num

@[simp] theorem zero_eval (x : Fin n → Bool) : (zero n).eval x = 0 := by
  unfold zero eval wt
  simp

/-- Append zero atoms along the standard initial-segment embedding. -/
noncomputable def pad (phi : Fin K → FracAtom n) : Fin H → FracAtom n :=
  fun h ↦ if hh : h.val < K then phi ⟨h.val, hh⟩ else zero n

@[simp] theorem pad_eval_of_lt (phi : Fin K → FracAtom n)
    (h : Fin H) (hh : h.val < K) (x : Fin n → Bool) :
    (pad phi h).eval x = (phi ⟨h.val, hh⟩).eval x := by
  simp [pad, hh]

@[simp] theorem pad_eval_of_le (phi : Fin K → FracAtom n)
    (h : Fin H) (hh : K ≤ h.val) (x : Fin n → Bool) :
    (pad phi h).eval x = 0 := by
  simp [pad, not_lt.mpr hh]

theorem sum_pad_eval (phi : Fin K → FracAtom n) (hKH : K ≤ H)
    (x : Fin n → Bool) :
    ∑ h : Fin H, (pad phi h).eval x = ∑ k, (phi k).eval x := by
  classical
  symm
  let e : Fin K ↪ Fin H :=
    ⟨Fin.castLE hKH, Fin.castLE_injective hKH⟩
  calc
    ∑ k, (phi k).eval x =
        ∑ h ∈ Finset.univ.image e, (pad phi h).eval x := by
      rw [Finset.sum_image e.injective.injOn]
      apply Finset.sum_congr rfl
      intro k _
      simp [e, pad]
    _ = ∑ h, (pad phi h).eval x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro h _ hnot
      have hle : K ≤ h.val := by
        apply Nat.le_of_not_gt
        intro hlt
        apply hnot
        apply Finset.mem_image.mpr
        refine ⟨⟨h.val, hlt⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        rfl
      exact pad_eval_of_le phi h hle x

end FracAtom

/-- Fractional computability is monotone in the number of atoms. -/
theorem fracComputable_mono {n K H : ℕ}
    {f : (Fin n → Bool) → Bool} (hKH : K ≤ H)
    (hf : fracComputable n K f) : fracComputable n H f := by
  classical
  rcases hf with ⟨phi, c, hsign⟩
  refine ⟨FracAtom.pad phi, c, fun x ↦ ?_⟩
  rw [FracAtom.sum_pad_eval phi hKH x]
  exact hsign x

/-- Head computability is monotone in the number of heads. -/
theorem computableWithHeadsN_mono {n K H : ℕ}
    {f : (Fin n → Bool) → Bool} (hKH : K ≤ H)
    (hf : computableWithHeadsN n K f) : computableWithHeadsN n H f :=
  computable_of_fracComputable
    (fracComputable_mono hKH (fracComputable_of_computable hf))

end HeadComplexity
