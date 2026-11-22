import HeadComplexity.Atoms.ExactHammingProfile
import HeadComplexity.Polynomial.OrderedSignChanges

set_option linter.style.header false

/-!
# Parameter-line oscillation in the admissible head model

Even with one Boolean input, a positive affine line of denominator parameters
can have arbitrarily many output sign changes as the number of heads grows.
This rules out a degree bound independent of the number of heads for polynomial
sign predicates in the original parameters. It is not a lower bound on the
worst-case head complexity of Boolean functions.
-/

namespace HeadComplexity.ParameterLineOscillation

open Finset Polynomial
open scoped BigOperators

noncomputable def shift (H : ℕ) (h : Fin H) : ℝ := (H : ℝ) + (h : ℕ)

theorem shift_pos {H : ℕ} (hH : 0 < H) (h : Fin H) : 0 < shift H h := by
  dsimp [shift]
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast hH) (Nat.cast_nonneg _)

/-- Exact alternating scores occur at `t = 1, ..., H + 1`, with every
denominator strictly positive on the whole positive parameter ray. -/
theorem exists_alternating_parameter_line (H : ℕ) :
    ∃ (b : Fin H → ℝ) (c : ℝ), ∀ k : Fin (H + 1),
      c + ∑ h, b h / (((k : ℕ) : ℝ) + 1 + shift H h) =
        if Odd (k : ℕ) then 1 else -1 := by
  obtain ⟨b, c, hb⟩ := exists_exact_hamming_reciprocals
    (fun k : Fin (H + 1) ↦ if Odd (k : ℕ) then (1 : ℝ) else -1)
  refine ⟨b, c, fun k ↦ ?_⟩
  convert hb k using 1
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  simp only [shift, exactProfileShift]
  ring

/-- Every polynomial agreeing with the signs of this line at the indicated
nodes has degree at least `H`, including the non-strict false convention. -/
theorem exists_parameter_line_forcing_degree (H : ℕ) :
    ∃ (b : Fin H → ℝ) (c : ℝ),
      (∀ k : Fin (H + 1),
        c + ∑ h, b h / (((k : ℕ) : ℝ) + 1 + shift H h) =
          if Odd (k : ℕ) then 1 else -1) ∧
      ∀ p : ℝ[X],
        (∀ k : Fin (H + 1),
          (0 < p.eval (((k : ℕ) : ℝ) + 1)) ↔
          0 < c + ∑ h, b h / (((k : ℕ) : ℝ) + 1 + shift H h)) →
        H ≤ p.natDegree := by
  obtain ⟨b, c, hb⟩ := exists_alternating_parameter_line H
  refine ⟨b, c, hb, fun p hp ↦ ?_⟩
  let nodes : Fin (H + 1) → ℝ := fun k ↦ ((k : ℕ) : ℝ) + 1
  have hnodes : StrictMono nodes := by
    intro i j hij
    dsimp [nodes]
    have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    linarith
  have hdeg := ordered_signChanges_le_of_sign_iff p nodes hnodes
    (fun k ↦ decide (Odd k)) (by
      intro k hk
      let i : Fin (H + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
      have hi := hp i
      rw [hb i] at hi
      by_cases ho : Odd k
      · norm_num [nodes, orderedNodeIndex, i, ho] at hi ⊢
        exact hi
      · norm_num [nodes, orderedNodeIndex, i, ho] at hi ⊢
        exact hi)
  simpa only [signChanges_parity] using hdeg

/-- A scalar head with positive slope `t` realizes each summand on the single
Boolean input. The denominator coefficients depend affinely on `t`. -/
noncomputable def atom {H : ℕ} (hH : 0 < H) (b : Fin H → ℝ)
    (t : ℝ) (ht : 0 < t) (h : Fin H) : FracAtom 1 :=
  FracAtom.ofPositiveAffineRatio (b h) (fun _ ↦ 0)
    (shift H h) (fun _ ↦ t) (shift_pos hH h) (fun _ ↦ ht)

theorem atom_eval_true {H : ℕ} (hH : 0 < H) (b : Fin H → ℝ)
    (t : ℝ) (ht : 0 < t) (h : Fin H) :
    (atom hH b t ht h).eval (fun _ ↦ true) = b h / (t + shift H h) := by
  rw [atom, FracAtom.ofPositiveAffineRatio_eval]
  simp [affineValue, boolToReal, add_comm]

/-- The degree obstruction applies to actual admissible one-bit heads. -/
theorem admissible_heads_force_parameter_degree {H : ℕ} (hH : 0 < H) :
    ∃ (b : Fin H → ℝ) (c : ℝ), ∀ p : ℝ[X],
      (∀ (t : ℝ) (ht : 0 < t),
        (0 < p.eval t) ↔ 0 < c + ∑ h, (atom hH b t ht h).eval (fun _ ↦ true)) →
      H ≤ p.natDegree := by
  obtain ⟨b, c, _, hb⟩ := exists_parameter_line_forcing_degree H
  refine ⟨b, c, fun p hp ↦ hb p ?_⟩
  intro k
  have ht : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
  simpa only [atom_eval_true] using hp (((k : ℕ) : ℝ) + 1) ht

end HeadComplexity.ParameterLineOscillation
