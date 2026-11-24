import HeadComplexity.Results.ReverseGridAxisRepair

set_option linter.style.header false

/-!
# Projective changes of separated grid denominators

The identities in this file preserve grid scores up to a row term and
a column term. The whole-cube extension needs the stated sum budget;
positive grid denominators alone do not establish that budget.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

noncomputable def mobius (α β γ δ x : ℝ) : ℝ := (α * x + β) / (γ * x + δ)

/-- The difference identity records every required nonzero factor. -/
theorem mobius_sub (α β γ δ p d : ℝ)
    (hp : γ * p + δ ≠ 0) (hd : γ * d + δ ≠ 0) :
    mobius α β γ δ d - mobius α β γ δ p =
      (α * δ - β * γ) * (d - p) / ((γ * d + δ) * (γ * p + δ)) := by
  unfold mobius
  have hd' : d * γ + δ ≠ 0 := by simpa [mul_comm] using hd
  field_simp [hp, hd, hd']
  ring

/-- A simultaneous projective change of a row pole and a column pole
preserves a separated affine numerator, modulo row and column terms. -/
theorem mobius_separated_ratio (α β γ δ p d a b : ℝ)
    (hp : γ * p + δ ≠ 0) (hd : γ * d + δ ≠ 0)
    (hdet : α * δ - β * γ ≠ 0) (hdp : d - p ≠ 0) :
    (((α * δ - β * γ) * a / (γ * p + δ) ^ 2) +
        ((α * δ - β * γ) * b / (γ * d + δ) ^ 2)) /
      (mobius α β γ δ d - mobius α β γ δ p) =
        (a + b) / (d - p) + γ * a / (γ * p + δ) - γ * b / (γ * d + δ) := by
  rw [mobius_sub α β γ δ p d hp hd]
  field_simp [hp, hd, hdet, hdp]
  ring

/-- The exact lower endpoint of the natural weak reverse extension. -/
noncomputable def separatedReverseSlack {r s : ℕ}
    (p : Fin r → ℝ) (d : Fin s → ℝ) (lo hi : ℝ) : ℝ :=
  hi - lo - (∑ i, (p i - lo)) - ∑ j, (hi - d j)

/-- A separated grid denominator extends to the entire Boolean cube
when the aggregate slope cost is strictly below its constant term. -/
theorem exists_weak_reverse_separated {r s : ℕ}
    (p a : Fin r → ℝ) (d b : Fin s → ℝ) (lo hi : ℝ)
    (hlo : ∀ i, lo ≤ p i) (hhi : ∀ j, d j ≤ hi)
    (hslack : 0 < separatedReverseSlack p d lo hi) :
    ∃ R : WeakReverseRatio (r + s),
      ∀ i j, R.value (localGrid i j) = (a i + b j) / (d j - p i) := by
  classical
  let R : WeakReverseRatio (r + s) :=
    { a₀ := 0
      a := Fin.addCases a b
      b₀ := hi - lo
      b := Fin.addCases (fun i ↦ lo - p i) (fun j ↦ d j - hi)
      nonpositive := by
        intro k
        refine Fin.addCases ?_ ?_ k <;> intro i <;> simp only [Fin.addCases_left,
          Fin.addCases_right]
        · exact sub_nonpos.mpr (hlo i)
        · exact sub_nonpos.mpr (hhi i)
      positive := by
        intro bits
        have hl (i : Fin r) : lo - p i ≤
            (lo - p i) * boolToReal (bits (Fin.castAdd s i)) := by
          cases bits (Fin.castAdd s i) <;> simp [boolToReal, hlo i]
        have hr (j : Fin s) : d j - hi ≤
            (d j - hi) * boolToReal (bits (Fin.natAdd r j)) := by
          cases bits (Fin.natAdd r j) <;> simp [boolToReal, hhi j]
        have hls := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hl i)
        have hrs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hr j)
        have hs : separatedReverseSlack p d lo hi =
            hi - lo + (∑ i, (lo - p i)) + ∑ j, (d j - hi) := by
          simp only [separatedReverseSlack, Finset.sum_sub_distrib]
          ring
        rw [hs] at hslack
        simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
        linarith }
  refine ⟨R, ?_⟩
  intro i j
  change affineValue 0 (Fin.addCases a b) (localGrid i j) /
    affineValue (hi - lo) (Fin.addCases (fun i ↦ lo - p i) (fun j ↦ d j - hi))
      (localGrid i j) = _
  simp [affineValue, localGrid, Fin.sum_univ_add, boolToReal]
  congr 1
  ring

/-- Strict slopes cost no extra head, by the checked weight-two repair. -/
theorem exists_strict_reverse_separated {r s : ℕ}
    (p a : Fin r → ℝ) (d b : Fin s → ℝ) (lo hi : ℝ)
    (hlo : ∀ i, lo ≤ p i) (hhi : ∀ j, d j ≤ hi)
    (hslack : 0 < separatedReverseSlack p d lo hi) :
    ∃ R : StrictReverseRatio (r + s),
      ∀ i j, R.value (localGrid i j) = (a i + b j) / (d j - p i) := by
  obtain ⟨R, hR⟩ := exists_weak_reverse_separated p a d b lo hi hlo hhi hslack
  obtain ⟨Q, hQ⟩ := weak_reverse_ratio_strictify R
  exact ⟨Q, fun i j ↦ (hQ i j).trans (hR i j)⟩

/-- For actual extremal poles the sum budget is necessary for every weak
reverse affine extension with those exact grid denominator values. -/
theorem separatedReverseSlack_pos_of_extension {r s : ℕ}
    (p : Fin r → ℝ) (d : Fin s → ℝ) (i₀ : Fin r) (j₀ : Fin s)
    (c : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ)
    (hu : ∀ i, u i ≤ 0) (hv : ∀ j, v j ≤ 0)
    (hfull : 0 < c + (∑ i, u i) + ∑ j, v j)
    (hgrid : ∀ i j, c + u i + v j = d j - p i) :
    0 < separatedReverseSlack p d (p i₀) (d j₀) := by
  have he : c + u i₀ + v j₀ = d j₀ - p i₀ := hgrid i₀ j₀
  have hur (i : Fin r) : u i = (p i₀ - p i) + u i₀ := by
    have h := hgrid i j₀
    linarith
  have hvr (j : Fin s) : v j = (d j - d j₀) + v j₀ := by
    have h := hgrid i₀ j
    linarith
  have hs : c + (∑ i, u i) + ∑ j, v j =
      separatedReverseSlack p d (p i₀) (d j₀) +
        ((r : ℝ) - 1) * u i₀ + ((s : ℝ) - 1) * v j₀ := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ hur i),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) ↦ hvr j)]
    simp only [separatedReverseSlack, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hr : (1 : ℝ) ≤ r := by
    have := i₀.isLt
    exact_mod_cast (show 1 ≤ r by omega)
  have hs' : (1 : ℝ) ≤ s := by
    have := j₀.isLt
    exact_mod_cast (show 1 ≤ s by omega)
  have hru := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr) (hu i₀)
  have hsv := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs') (hv j₀)
  rw [hs] at hfull
  linarith

/-- Exact finite-grid criterion. Nonpositive slopes and positivity at the
all-ones vertex are equivalent to full-cube positivity for this extension. -/
theorem separated_reverse_extension_iff {r s : ℕ}
    (p : Fin r → ℝ) (d : Fin s → ℝ) (i₀ : Fin r) (j₀ : Fin s)
    (hp : ∀ i, p i₀ ≤ p i) (hd : ∀ j, d j ≤ d j₀) :
    (∃ (c : ℝ) (u : Fin r → ℝ) (v : Fin s → ℝ),
      (∀ i, u i ≤ 0) ∧ (∀ j, v j ≤ 0) ∧
      0 < c + (∑ i, u i) + (∑ j, v j) ∧
      ∀ i j, c + u i + v j = d j - p i) ↔
    0 < separatedReverseSlack p d (p i₀) (d j₀) := by
  constructor
  · rintro ⟨c, u, v, hu, hv, hf, hg⟩
    exact separatedReverseSlack_pos_of_extension p d i₀ j₀ c u v hu hv hf hg
  · intro h
    refine ⟨d j₀ - p i₀, (fun i ↦ p i₀ - p i), (fun j ↦ d j - d j₀),
      (fun i ↦ sub_nonpos.mpr (hp i)), (fun j ↦ sub_nonpos.mpr (hd j)), ?_, ?_⟩
    · convert h using 1
      simp only [separatedReverseSlack, Finset.sum_sub_distrib]
      ring
    · intro i j
      ring

/-- Every independent head transformation is corrected jointly by one
affine head. The final axis repair costs `3H + 6`, preserving every grid
value exactly. The full-cube sum budgets remain explicit hypotheses. -/
theorem exists_mobius_reverse_axis {r s H : ℕ}
    (p a : Fin H → Fin r → ℝ) (d b : Fin H → Fin s → ℝ)
    (α β γ δ lo hi : Fin H → ℝ)
    (hp : ∀ h i, γ h * p h i + δ h ≠ 0)
    (hd : ∀ h j, γ h * d h j + δ h ≠ 0)
    (hdet : ∀ h, α h * δ h - β h * γ h ≠ 0)
    (hdp : ∀ h i j, d h j - p h i ≠ 0)
    (hlo : ∀ h i, lo h ≤ mobius (α h) (β h) (γ h) (δ h) (p h i))
    (hhi : ∀ h j, mobius (α h) (β h) (γ h) (δ h) (d h j) ≤ hi h)
    (hslack : ∀ h, 0 < separatedReverseSlack
      (fun i ↦ mobius (α h) (β h) (γ h) (δ h) (p h i))
      (fun j ↦ mobius (α h) (β h) (γ h) (δ h) (d h j)) (lo h) (hi h)) :
    ∃ G : ReverseAxisData r s (3 * (H + 1) + 3),
      ∀ i j, G.score (localGrid i j) =
        ∑ h, (a h i + b h j) / (d h j - p h i) := by
  classical
  let ap := fun h i ↦ (α h * δ h - β h * γ h) * a h i / (γ h * p h i + δ h) ^ 2
  let bp := fun h j ↦ (α h * δ h - β h * γ h) * b h j / (γ h * d h j + δ h) ^ 2
  choose R hR using fun h ↦ exists_weak_reverse_separated
    (fun i ↦ mobius (α h) (β h) (γ h) (δ h) (p h i)) (ap h)
    (fun j ↦ mobius (α h) (β h) (γ h) (δ h) (d h j)) (bp h)
    (lo h) (hi h) (hlo h) (hhi h) (hslack h)
  let row := fun i ↦ -(∑ h, γ h * a h i / (γ h * p h i + δ h))
  let col := fun j ↦ ∑ h, γ h * b h j / (γ h * d h j + δ h)
  let C : WeakReverseRatio (r + s) :=
    { a₀ := 0, b₀ := 1, a := Fin.addCases row col, b := fun _ ↦ 0
      nonpositive := by simp
      positive := by intro bits; simp [affineValue] }
  have hC (i : Fin r) (j : Fin s) :
      C.value (localGrid i j) = row i + col j := by
    simp [C, WeakReverseRatio.value, affineValue, localGrid, Fin.sum_univ_add, boolToReal]
  let L : WeakReverseGridData r s (H + 1) :=
    { bias := 0, head := Fin.cases C R }
  have hL (i : Fin r) (j : Fin s) :
      L.score (localGrid i j) = ∑ h, (a h i + b h j) / (d h j - p h i) := by
    change 0 + (∑ h : Fin (H + 1),
      ((Fin.cases C R : Fin (H + 1) → WeakReverseRatio (r + s)) h).value
        (localGrid i j)) = _
    rw [zero_add, Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, hC, hR]
    have heq (h : Fin H) := mobius_separated_ratio (α h) (β h) (γ h) (δ h)
      (p h i) (d h j) (a h i) (b h j) (hp h i) (hd h j) (hdet h) (hdp h i j)
    dsimp [ap, bp]
    simp_rw [heq]
    simp only [row, col, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  obtain ⟨G, hG⟩ := exists_reverse_axis_repair_of_weak L
  exact ⟨G, fun i j ↦ (hG i j).trans (hL i j)⟩

end AxisZeroGluing
end HeadComplexity
