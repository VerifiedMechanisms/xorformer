import HeadComplexity.Research.MarginSensitiveCapacity

set_option linter.style.header false

/-!
Finite coefficient-order charts for positive affine denominators. Selecting
the last present coefficient in an ascending order conditions the denominator
by `n + 1`. The orientation and order count is exactly `(2 * (n + 1)!) ^ H`.
-/

noncomputable section

namespace HeadComplexity.CoefficientOrderChart

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- The constant coefficient is always present, while a slope is present
exactly when its input bit is true. -/
def Present (x : Fin n → Bool) : Option (Fin n) → Prop
  | none => True
  | some i => x i = true

instance (x : Fin n → Bool) (i : Option (Fin n)) : Decidable (Present x i) := by
  cases i <;> unfold Present <;> infer_instance

/-- Positions of the present coefficients in a fixed permutation. -/
def positions (σ : Equiv.Perm (Fin (n + 1))) (x : Fin n → Bool) :
    Finset (Fin (n + 1)) := by
  classical
  exact univ.filter fun k => Present x (finSuccEquiv n (σ k))

theorem positions_nonempty (σ : Equiv.Perm (Fin (n + 1))) (x : Fin n → Bool) :
    (positions σ x).Nonempty := by
  classical
  refine ⟨σ.symm 0, ?_⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  simp only [Equiv.apply_symm_apply, finSuccEquiv_zero, Present]

/-- The final present position in the ascending coefficient order. -/
def selected (σ : Equiv.Perm (Fin (n + 1))) (x : Fin n → Bool) : Option (Fin n) :=
  finSuccEquiv n (σ ((positions σ x).max' (positions_nonempty σ x)))

theorem selected_present (σ : Equiv.Perm (Fin (n + 1))) (x : Fin n → Bool) :
    Present x (selected σ x) := by
  classical
  have h := (positions σ x).max'_mem (positions_nonempty σ x)
  exact (mem_filter.mp h).2

/-- The selected coefficient is maximal among all present coefficients. -/
theorem le_selected_of_monotone
    (b : Option (Fin n) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (hmono : Monotone fun k => b (finSuccEquiv n (σ k)))
    (x : Fin n → Bool) (i : Option (Fin n)) (hi : Present x i) :
    b i ≤ b (selected σ x) := by
  classical
  let k := σ.symm ((finSuccEquiv n).symm i)
  have hk : k ∈ positions σ x := by simp [k, positions, hi]
  have hle := hmono (le_max' (positions σ x) k hk)
  simpa [selected, k] using hle

/-- Affine denominator evaluation from its constant and slope coefficients. -/
def affineValue (b : Option (Fin n) → ℝ) (x : Fin n → Bool) : ℝ :=
  b none + ∑ i, boolToReal (x i) * b (some i)

theorem sum_present_eq_affineValue
    (b : Option (Fin n) → ℝ) (x : Fin n → Bool) :
    (∑ i : Option (Fin n), if Present x i then b i else 0) = affineValue b x := by
  classical
  rw [Fintype.sum_option]
  simp only [Present, ↓reduceIte, affineValue]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases h : x i = true <;> simp [h, boolToReal]

/-- Every nonnegative coefficient vector with positive constant admits a
chart that conditions every cube denominator by `n + 1`, simultaneously. -/
theorem exists_conditioning_order (b : Option (Fin n) → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hb0 : 0 < b none) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ x : Fin n → Bool,
      0 < b (selected σ x) ∧
      b (selected σ x) ≤ affineValue b x ∧
      affineValue b x ≤ (n + 1 : ℕ) * b (selected σ x) := by
  classical
  let σ := Tuple.sort (fun k : Fin (n + 1) => b (finSuccEquiv n k))
  have hmono : Monotone (fun k => b (finSuccEquiv n (σ k))) := by
    intro i j hij
    exact Tuple.monotone_sort (fun k : Fin (n + 1) => b (finSuccEquiv n k)) hij
  refine ⟨σ, fun x => ?_⟩
  have hpos : 0 < b (selected σ x) :=
    hb0.trans_le (le_selected_of_monotone b σ hmono x none trivial)
  let v : Option (Fin n) → ℝ := fun i => if Present x i then b i else 0
  have hnonneg : ∀ i, 0 ≤ v i := by
    intro i
    dsimp [v]
    split_ifs
    · exact hb i
    · exact le_rfl
  have hmax : ∀ i, v i ≤ v (selected σ x) := by
    intro i
    simp only [v, selected_present, ↓reduceIte]
    split_ifs with hi
    · exact le_selected_of_monotone b σ hmono x i hi
    · exact hpos.le
  have hs := ConditionedReciprocalApproximation.selected_max_sum_bounds
    v (selected σ x) hnonneg hmax
  have hv : v (selected σ x) = b (selected σ x) := by simp [v, selected_present]
  have hsum : ∑ i, v i = affineValue b x := sum_present_eq_affineValue b x
  rw [hv, hsum] at hs
  refine ⟨hpos, hs.1, ?_⟩
  simpa using hs.2

/-- One global orientation and one coefficient order for each head. -/
abbrev Index (n H : ℕ) := Fin H → Bool × Equiv.Perm (Fin (n + 1))

theorem card_index : Fintype.card (Index n H) = (2 * (n + 1).factorial) ^ H := by
  simp [Index, Fintype.card_perm]

/-- Reflect all bits if the head has negative denominator orientation. -/
def coordinates (flip : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if flip then !(x i) else x i

/-- Coefficient orders supply actual fixed polynomial charts. -/
def toChart (ι : Index n H) : MarginSensitiveCapacity.Chart n H where
  coordinates h x := coordinates (ι h).1 x
  selected h x := selected (ι h).2 (coordinates (ι h).1 x)

/-- The full finite chart factor in the margin-sensitive polynomial count.
This is a count of the enlarged polynomial union, with Warren explicit. -/
theorem card_orderedPatterns_le_warren (hWarren : WarrenStrictSignPatternBound)
    (m : ℝ) (d : ℕ) (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((MarginSensitiveCapacity.chartPatterns (toChart (n := n) (H := H)) m d).ncard : ℝ) ≤
      ((2 * (n + 1).factorial : ℕ) : ℝ) ^ H *
        (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) := by
  have h := MarginSensitiveCapacity.card_chartPatterns_le_warren hWarren
    (toChart (n := n) (H := H)) m d hparameters
  rw [card_index] at h
  exact_mod_cast h

#print axioms exists_conditioning_order
#print axioms card_index
#print axioms card_orderedPatterns_le_warren

end HeadComplexity.CoefficientOrderChart
