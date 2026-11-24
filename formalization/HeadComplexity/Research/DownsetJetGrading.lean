import Mathlib

/-!
A finite downset has a positive superadditive grading, bounded by one half.
This explicit grading uses the maximum degree of an extension of each index.
The stronger primitive-ray product estimate is currently a written proof in
`artifacts/power-saving-20261124-followup/downset_jet_weighted_capacity.md`.
-/

namespace HeadComplexity.DownsetJetGrading

open scoped BigOperators

variable {r : ℕ}

def indexDegree (a : Fin r → ℕ) : ℕ := ∑ i, a i

def IsDownset (T : Finset (Fin r → ℕ)) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → b ∈ T → a ∈ T

noncomputable def extensionHeight (T : Finset (Fin r → ℕ))
    (a : Fin r → ℕ) : ℕ :=
  T.sup fun b => if a ≤ b then indexDegree b else 0

noncomputable def grading (T : Finset (Fin r → ℕ))
    (a : Fin r → ℕ) : ℝ :=
  (indexDegree a : ℝ) / (2 * (extensionHeight T a : ℝ))

@[simp] theorem indexDegree_zero : indexDegree (0 : Fin r → ℕ) = 0 := by
  simp [indexDegree]

@[simp] theorem indexDegree_add (a b : Fin r → ℕ) :
    indexDegree (a + b) = indexDegree a + indexDegree b := by
  simp [indexDegree, Finset.sum_add_distrib]

theorem indexDegree_pos {a : Fin r → ℕ} (ha : a ≠ 0) :
    0 < indexDegree a := by
  apply Nat.pos_of_ne_zero
  intro h
  apply ha
  funext i
  have hi : a i ≤ indexDegree a :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  simpa [h] using hi

theorem indexDegree_le_extensionHeight {T : Finset (Fin r → ℕ)}
    {a : Fin r → ℕ} (ha : a ∈ T) : indexDegree a ≤ extensionHeight T a := by
  classical
  apply Finset.le_sup_of_le ha
  simp

theorem extensionHeight_antitone (T : Finset (Fin r → ℕ)) :
    Antitone (extensionHeight T) := by
  classical
  intro a b hab
  apply Finset.sup_mono_fun
  intro c hc
  by_cases hbc : b ≤ c
  · simp [hbc, hab.trans hbc]
  · simp [hbc]

@[simp] theorem grading_zero (T : Finset (Fin r → ℕ)) :
    grading T 0 = 0 := by
  simp [grading]

theorem grading_pos {T : Finset (Fin r → ℕ)} {a : Fin r → ℕ}
    (ha : a ∈ T) (ha0 : a ≠ 0) : 0 < grading T a := by
  have hdeg := indexDegree_pos ha0
  have hheight := lt_of_lt_of_le hdeg (indexDegree_le_extensionHeight ha)
  exact div_pos (by exact_mod_cast hdeg) (by positivity)

theorem grading_le_half {T : Finset (Fin r → ℕ)} {a : Fin r → ℕ}
    (ha : a ∈ T) : grading T a ≤ 1 / 2 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hdeg := indexDegree_pos ha0
  have hh := indexDegree_le_extensionHeight ha
  have hheight : (0 : ℝ) < extensionHeight T a := by exact_mod_cast lt_of_lt_of_le hdeg hh
  unfold grading
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * extensionHeight T a)).2
  have hh' : (indexDegree a : ℝ) ≤ extensionHeight T a := by exact_mod_cast hh
  nlinarith

theorem grading_superadditive {T : Finset (Fin r → ℕ)} (hT : IsDownset T)
    {a b : Fin r → ℕ} (hab : a + b ∈ T) :
    grading T a + grading T b ≤ grading T (a + b) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  have ha_le : a ≤ a + b := by intro i; exact Nat.le_add_right _ _
  have hb_le : b ≤ a + b := by intro i; exact Nat.le_add_left _ _
  have ha : a ∈ T := hT ha_le hab
  have hb : b ∈ T := hT hb_le hab
  have hab0 : a + b ≠ 0 := by
    intro hz
    have hh := congrArg indexDegree hz
    simp only [indexDegree_add, indexDegree_zero] at hh
    have := indexDegree_pos ha0
    omega
  have hsum : (0 : ℝ) < extensionHeight T (a + b) := by
    exact_mod_cast lt_of_lt_of_le (indexDegree_pos hab0)
      (indexDegree_le_extensionHeight hab)
  have hA : (extensionHeight T (a + b) : ℝ) ≤ extensionHeight T a := by
    exact_mod_cast extensionHeight_antitone T ha_le
  have hB : (extensionHeight T (a + b) : ℝ) ≤ extensionHeight T b := by
    exact_mod_cast extensionHeight_antitone T hb_le
  have hfirst : (indexDegree a : ℝ) / (2 * extensionHeight T a) ≤
      (indexDegree a : ℝ) / (2 * extensionHeight T (a + b)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hsecond : (indexDegree b : ℝ) / (2 * extensionHeight T b) ≤
      (indexDegree b : ℝ) / (2 * extensionHeight T (a + b)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  unfold grading
  rw [indexDegree_add, Nat.cast_add, add_div]
  exact add_le_add hfirst hsecond

end HeadComplexity.DownsetJetGrading
