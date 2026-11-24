import HeadComplexity.Results.ApproximateGradedShellTransfer
import HeadComplexity.Results.JointCellWeightedCover

set_option linter.style.header false

/-!
Sparse subsets of deletion shells can be assembled if their limiting scores
vanish on the rest of the same shell. Proper layers need only vanish in the
limit as well. This condition is essential and is not supplied by a scalar
decoder on its intended queries alone.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- A sparse shell module may have arbitrary values on later layers, but
must vanish on the unused part of its own layer. -/
theorem glue_reverse_approx_supported_shell_modules {n : ℕ} (N : ℕ)
    (H d : ℕ → ℕ) (C : ℕ → Finset (Fin n))
    (P : ℕ → Finset (Fin n → Bool))
    (L : (i : ℕ) → ReverseApproxGradedData n (d i) (H i))
    (f : (Fin n → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hsubset : ∀ i < N, P i ⊆ gradedShell (C i) (d i))
    (hlocal : ∀ i < N, ∀ x ∈ P i,
      0 < outputSign (f x) * (L i).limit (centerDeletion (gradedCenter (C i)) x))
    (hzero : ∀ i < N, ∀ x ∈ gradedShell (C i) (d i), x ∉ P i →
      (L i).limit (centerDeletion (gradedCenter (C i)) x) = 0) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom n,
      ∀ x, (∃ i < N, x ∈ P i) →
        0 < outputSign (f x) * ∑ h, (φ h).eval x := by
  classical
  let F (i : ℕ) (x : Fin n → Bool) := if x ∈ gradedDownset (C i) then
    (L i).limit (centerDeletion (gradedCenter (C i)) x) else 0
  apply glue_headScoreClosure N H P F (fun x ↦ outputSign (f x))
    (fun i _ ↦ (L i).centered_closure (C i))
  · intro i hi x hx
    simpa only [F, gradedShell_subset_downset (C i) (d i) (hsubset i hi hx),
      ite_true] using hlocal i hi x hx
  · intro i hi j hj x hx
    by_cases hd : x ∈ gradedDownset (C i)
    · dsimp only [F]
      rw [ite_eq_left hd]
      rcases gradedShell_descending_geometry (hsubset j (hj.trans hi) hx) hd
        (horder i hi j hj) with hz | hc
      · rw [(L i).zero_below _ hz]
        simp
      · by_cases hp : x ∈ P i
        · exact (hlocal i hi x hp).le
        · rw [hzero i hi x hc hp]
          simp
    · simp only [F, hd, ite_false, mul_zero, le_refl]

/-- The sum of all module costs includes both selected sparse cells and
any singleton exceptions inserted into the descending sequence. -/
theorem HStar_le_approx_supported_shell_cover {n : ℕ} (N : ℕ)
    (H d : ℕ → ℕ) (C : ℕ → Finset (Fin n))
    (P : ℕ → Finset (Fin n → Bool))
    (L : (i : ℕ) → ReverseApproxGradedData n (d i) (H i))
    (f : (Fin n → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hsubset : ∀ i < N, P i ⊆ gradedShell (C i) (d i))
    (hlocal : ∀ i < N, ∀ x ∈ P i,
      0 < outputSign (f x) * (L i).limit (centerDeletion (gradedCenter (C i)) x))
    (hzero : ∀ i < N, ∀ x ∈ gradedShell (C i) (d i), x ∉ P i →
      (L i).limit (centerDeletion (gradedCenter (C i)) x) = 0)
    (hcover : ∀ x, ∃ i < N, x ∈ P i) :
    HStar n f ≤ ∑ i ∈ Finset.range N, H i := by
  classical
  obtain ⟨φ, hφ⟩ := glue_reverse_approx_supported_shell_modules N H d C P L f
    horder hsubset hlocal hzero
  let I := ((i : Fin N) × Fin (H i.val))
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfrac : fracComputable n (Fintype.card I) f := by
    refine ⟨fun h ↦ φ (e h), 0, fun x ↦ ?_⟩
    have heq := e.sum_comp (fun h ↦ (φ h).eval x)
    have hs := (strict_of_outputSign (hφ x (hcover x))).1
    simpa only [zero_add, heq] using hs
  have hbound := HStar_le_of_computableWithHeadsN (computable_of_fracComputable hfrac)
  simpa only [I, glued_head_count] using hbound

/-- The sparse-shell transfer is stated against the unchanged original
worst-case complexity. Its local compiler and same-shell support conditions
remain explicit hypotheses. -/
theorem worstCaseHeadComplexity_le_approx_supported_shell_cover {n : ℕ}
    (N : ℕ) (H d : ℕ → ℕ) (C : ℕ → Finset (Fin n))
    (P : ℕ → Finset (Fin n → Bool))
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hsubset : ∀ i < N, P i ⊆ gradedShell (C i) (d i))
    (hcover : ∀ x, ∃ i < N, x ∈ P i)
    (hcompiler : ∀ f : (Fin n → Bool) → Bool,
      ∃ L : (i : ℕ) → ReverseApproxGradedData n (d i) (H i),
        (∀ i < N, ∀ x ∈ P i,
          0 < outputSign (f x) * (L i).limit
            (centerDeletion (gradedCenter (C i)) x)) ∧
        (∀ i < N, ∀ x ∈ gradedShell (C i) (d i), x ∉ P i →
          (L i).limit (centerDeletion (gradedCenter (C i)) x) = 0)) :
    worstCaseHeadComplexity n ≤ ∑ i ∈ Finset.range N, H i := by
  apply Finset.sup_le
  intro f _
  obtain ⟨L, hL, hz⟩ := hcompiler f
  exact HStar_le_approx_supported_shell_cover N H d C P L f horder hsubset hL hz hcover

end HeadComplexity.AxisZeroGluing
