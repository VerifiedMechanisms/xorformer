import HeadComplexity.Atoms.FracAtomSymmetry
import HeadComplexity.Results.ExactFamilies
import HeadComplexity.Results.FractionalNormalForm
import HeadComplexity.Results.SymmetricFaceLowerBound

set_option linter.style.header false

/-!
# Structural invariances of head complexity

The fractional normal form makes the exact cube symmetries from theorem 28
transparent.  Coordinate permutations and simultaneous input complementation
act directly on atoms.  Output complementation negates the atoms after a
finite-margin shift, needed because the classifier convention permits zero on
false inputs.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- A finite fractional representation has a positive margin on its true
inputs.  The assertion also covers the vacuous all-false case. -/
private theorem exists_positive_true_margin
    {f : (Fin n → Bool) → Bool} (score : (Fin n → Bool) → ℝ)
    (hscore : ∀ x, (0 < score x ↔ f x = true)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ x, f x = true → epsilon < score x := by
  classical
  let T : Finset (Fin n → Bool) := Finset.univ.filter fun x ↦ f x = true
  by_cases hT : T.Nonempty
  · refine ⟨T.inf' hT score / 2, ?_, ?_⟩
    · apply half_pos
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact (hscore x).mpr (Finset.mem_filter.mp hx).2
    · intro x hx
      have hxT : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
      have hle := Finset.inf'_le score hxT
      have hpos : 0 < T.inf' hT score := by
        rw [Finset.lt_inf'_iff]
        intro y hy
        exact (hscore y).mpr (Finset.mem_filter.mp hy).2
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    exact (hT ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩).elim

/-- Complementing the represented Boolean output preserves every fixed atom
count. -/
theorem fracComputable.complement {f : (Fin n → Bool) → Bool}
    (hf : fracComputable n H f) :
    fracComputable n H (fun x ↦ !(f x)) := by
  classical
  rcases hf with ⟨phi, c, hphi⟩
  let score : (Fin n → Bool) → ℝ := fun x ↦ c + ∑ h, (phi h).eval x
  obtain ⟨epsilon, hepsilon, hmargin⟩ :=
    exists_positive_true_margin score hphi
  refine ⟨fun h ↦ (phi h).neg, epsilon - c, ?_⟩
  intro x
  have hsum : (∑ h, (phi h).neg.eval x) = -(∑ h, (phi h).eval x) := by
    simp
  rw [hsum]
  have hrewrite : epsilon - c + -(∑ h, (phi h).eval x) = epsilon - score x := by
    dsimp [score]
    ring
  rw [hrewrite]
  cases hfx : f x with
  | false =>
      have hnpos : score x ≤ 0 := by
        by_contra h
        push Not at h
        have := (hphi x).mp h
        simp [hfx] at this
      simp [hfx]
      linarith
  | true =>
      have hlt := hmargin x hfx
      simp [hfx]
      linarith

/-- Coordinate relabeling preserves fixed-count atom representability in both
directions. -/
theorem fracComputable_permute_iff (sigma : Equiv.Perm (Fin n))
    (f : (Fin n → Bool) → Bool) :
    fracComputable n H (fun x ↦ f (permuteBits sigma x)) ↔
      fracComputable n H f := by
  constructor
  · intro hf
    have h := hf.permute sigma.symm
    have hfun :
        (fun x ↦ f (permuteBits sigma (permuteBits sigma.symm x))) = f := by
      funext x
      exact congrArg f (by
        simpa only [Equiv.symm_symm] using
          (permuteBits_symm (sigma := sigma.symm) x))
    rw [hfun] at h
    exact h
  · exact fracComputable.permute sigma

/-- Simultaneous input complementation preserves fixed-count atom
representability in both directions. -/
theorem fracComputable_flip_iff (f : (Fin n → Bool) → Bool) :
    fracComputable n H (fun x ↦ f (flipBits x)) ↔ fracComputable n H f := by
  constructor
  · intro hf
    have h := hf.flip
    simpa using h
  · exact fracComputable.flip

/-- Output complementation preserves fixed-count atom representability in both
directions. -/
theorem fracComputable_complement_iff (f : (Fin n → Bool) → Bool) :
    fracComputable n H (fun x ↦ !(f x)) ↔ fracComputable n H f := by
  constructor
  · intro hf
    have h := hf.complement
    simpa using h
  · exact fracComputable.complement

/-- Coordinate relabeling preserves computability with exactly `H` heads. -/
theorem computableWithHeadsN_permute_iff (sigma : Equiv.Perm (Fin n))
    (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H (fun x ↦ f (permuteBits sigma x)) ↔
      computableWithHeadsN n H f := by
  rw [computableWithHeadsN_iff_fracComputable,
    computableWithHeadsN_iff_fracComputable]
  exact fracComputable_permute_iff sigma f

/-- Simultaneous input complementation preserves computability with exactly
`H` heads. -/
theorem computableWithHeadsN_flip_iff (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H (fun x ↦ f (flipBits x)) ↔
      computableWithHeadsN n H f := by
  rw [computableWithHeadsN_iff_fracComputable,
    computableWithHeadsN_iff_fracComputable]
  exact fracComputable_flip_iff f

/-- Output complementation preserves computability with exactly `H` heads. -/
theorem computableWithHeadsN_complement_iff (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H (fun x ↦ !(f x)) ↔
      computableWithHeadsN n H f := by
  rw [computableWithHeadsN_iff_fracComputable,
    computableWithHeadsN_iff_fracComputable]
  exact fracComputable_complement_iff f

/-- Head complexity is invariant under coordinate permutations. -/
theorem HStar_permute (sigma : Equiv.Perm (Fin n))
    (f : (Fin n → Bool) → Bool) :
    HStar n (fun x ↦ f (permuteBits sigma x)) = HStar n f := by
  apply Nat.le_antisymm
  · exact HStar_le_of_computableWithHeadsN
      ((computableWithHeadsN_permute_iff sigma f).mpr (HStar_computable f))
  · exact HStar_le_of_computableWithHeadsN
      ((computableWithHeadsN_permute_iff sigma f).mp
        (HStar_computable (fun x ↦ f (permuteBits sigma x))))

/-- Head complexity is invariant under simultaneous complementation of all
input bits. -/
theorem HStar_flip (f : (Fin n → Bool) → Bool) :
    HStar n (fun x ↦ f (flipBits x)) = HStar n f := by
  apply Nat.le_antisymm
  · exact HStar_le_of_computableWithHeadsN
      ((computableWithHeadsN_flip_iff f).mpr (HStar_computable f))
  · exact HStar_le_of_computableWithHeadsN
      ((computableWithHeadsN_flip_iff f).mp
        (HStar_computable (fun x ↦ f (flipBits x))))

/-- Head complexity is invariant under Boolean output complementation. -/
theorem HStar_complement (f : (Fin n → Bool) → Bool) :
    HStar n (fun x ↦ !(f x)) = HStar n f := by
  apply Nat.le_antisymm
  · exact HStar_le_of_computableWithHeadsN
      ((computableWithHeadsN_complement_iff f).mpr (HStar_computable f))
  · exact HStar_le_of_computableWithHeadsN
      ((computableWithHeadsN_complement_iff f).mp
        (HStar_computable (fun x ↦ !(f x))))

/-- A parity restriction on `m` free coordinates forces at least `m` heads. -/
theorem parity_face_le_HStar {m : ℕ} (rho : CoordFace m n)
    (f : (Fin n → Bool) → Bool)
    (hface : ∀ x, f (rho.apply x) = PARITY m x) :
    m ≤ HStar n f := by
  have hfun : (fun x ↦ f (rho.apply x)) = PARITY m := funext hface
  rw [← HStar_parity m, ← hfun]
  exact HStar_restrict_le rho f

/-- A complemented parity restriction has the same lower-bound force. -/
theorem complement_parity_face_le_HStar {m : ℕ} (rho : CoordFace m n)
    (f : (Fin n → Bool) → Bool)
    (hface : ∀ x, f (rho.apply x) = !(PARITY m x)) :
    m ≤ HStar n f := by
  have hfun : (fun x ↦ f (rho.apply x)) = (fun x ↦ !(PARITY m x)) :=
    funext hface
  rw [← HStar_parity m, ← HStar_complement (PARITY m), ← hfun]
  exact HStar_restrict_le rho f

end HeadComplexity
