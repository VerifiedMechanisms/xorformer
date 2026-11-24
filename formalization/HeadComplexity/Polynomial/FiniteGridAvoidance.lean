import Mathlib.Tactic

set_option linter.style.header false

/-!
# Quantitative simultaneous avoidance on a five-point grid

A slab of width less than one grid spacing contains at most one point on each
coordinate fiber. Three such slabs cannot cover a five-point product grid.
-/

namespace HeadComplexity.FiniteGridAvoidance
noncomputable section
open scoped BigOperators

def gridValue (r : Fin 5) : ℝ := ((r : ℝ) - 2) / 2

theorem gridValue_abs_le (r : Fin 5) : |gridValue r| ≤ 1 := by
  fin_cases r <;> norm_num [gridValue]

theorem gridValue_separated {r s : Fin 5} (h : r ≠ s) :
    (1 : ℝ) / 2 ≤ |gridValue r - gridValue s| := by
  fin_cases r <;> fin_cases s <;> norm_num [gridValue] at *

def gridLinear {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Fin 5) : ℝ :=
  ∑ i, a i * gridValue (x i)

def bad {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) : Finset (Fin n → Fin 5) :=
  Finset.univ.filter (fun x ↦ |gridLinear a x| < δ / 12)

theorem linear_difference_one_coordinate {n : ℕ} (a : Fin n → ℝ)
    (x y : Fin n → Fin 5) (j : Fin n) (h : ∀ i, i ≠ j → x i = y i) :
    gridLinear a x - gridLinear a y = a j * (gridValue (x j) - gridValue (y j)) := by
  rw [gridLinear, gridLinear, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · ring
  · intro i _ hij
    rw [h i hij]
    ring
  · simp

theorem bad_restriction_injective {n : ℕ} (a : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (j : Fin n) (hj : δ ≤ |a j|) :
    Function.Injective (fun x : ↥(bad a δ) ↦
      (fun i : {i : Fin n // i ≠ j} ↦ x.val i.val)) := by
  classical
  intro x y hxy
  have hx : |gridLinear a x.val| < δ / 12 := (Finset.mem_filter.mp x.property).2
  have hy : |gridLinear a y.val| < δ / 12 := (Finset.mem_filter.mp y.property).2
  have hout : ∀ i, i ≠ j → x.val i = y.val i := by
    intro i hi
    exact congrFun hxy ⟨i, hi⟩
  have hjxy : x.val j = y.val j := by
    by_contra hne
    have hsep := gridValue_separated hne
    have hlarge : δ / 2 ≤ |gridLinear a x.val - gridLinear a y.val| := by
      rw [linear_difference_one_coordinate a x.val y.val j hout, abs_mul]
      have ha : 0 ≤ |a j| := abs_nonneg _
      have hz : 0 ≤ |gridValue (x.val j) - gridValue (y.val j)| := abs_nonneg _
      nlinarith
    have hsmall : |gridLinear a x.val - gridLinear a y.val| ≤
        |gridLinear a x.val| + |gridLinear a y.val| := by
      simpa using abs_sub_le (gridLinear a x.val) 0 (gridLinear a y.val)
    linarith
  apply Subtype.ext
  funext i
  by_cases hi : i = j
  · simpa [hi] using hjxy
  · exact hout i hi

theorem bad_card_le {n : ℕ} (a : Fin (n + 1) → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (j : Fin (n + 1)) (hj : δ ≤ |a j|) :
    (bad a δ).card ≤ 5 ^ n := by
  classical
  have hc : Fintype.card {i : Fin (n + 1) // i ≠ j} = n := by
    simp [Fintype.card_subtype_compl]
  have h := Fintype.card_le_of_injective _ (bad_restriction_injective a δ hδ j hj)
  simpa [Fintype.card_fun, hc] using h

theorem exists_grid_avoids_three {n : ℕ} (a : Fin 3 → Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (ha : ∀ h, ∃ j, δ ≤ |a h j|) :
    ∃ x : Fin (n + 1) → Fin 5, ∀ h, δ / 12 ≤ |gridLinear (a h) x| := by
  classical
  have hc (h : Fin 3) : (bad (a h) δ).card ≤ 5 ^ n := by
    obtain ⟨j, hj⟩ := ha h
    exact bad_card_le (a h) δ hδ j hj
  let U := bad (a 0) δ ∪ bad (a 1) δ ∪ bad (a 2) δ
  have hcard : U.card < (Finset.univ : Finset (Fin (n + 1) → Fin 5)).card := by
    have h01 := Finset.card_union_le (bad (a 0) δ) (bad (a 1) δ)
    have h012 := Finset.card_union_le (bad (a 0) δ ∪ bad (a 1) δ) (bad (a 2) δ)
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    have hp : 0 < 5 ^ n := pow_pos (by omega) _
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_succ]
    dsimp only [U]
    omega
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨x, fun h ↦ ?_⟩
  have hn : x ∉ bad (a h) δ := by
    fin_cases h <;> simp_all [U]
  simpa [bad, not_lt] using hn

/-- The quantitative conclusion in real coordinates, with explicit membership
in the five-point grid and the unit cube. -/
theorem exists_cube_point_avoids_three {n : ℕ} (a : Fin 3 → Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (ha : ∀ h, ∃ j, δ ≤ |a h j|) :
    ∃ z : Fin (n + 1) → ℝ,
      (∀ i, ∃ r : Fin 5, z i = gridValue r) ∧
      (∀ i, |z i| ≤ 1) ∧
      ∀ h, δ / 12 ≤ |∑ i, a h i * z i| := by
  obtain ⟨x, hx⟩ := exists_grid_avoids_three a δ hδ ha
  refine ⟨fun i ↦ gridValue (x i), ?_, ?_, ?_⟩
  · exact fun i ↦ ⟨x i, rfl⟩
  · exact fun i ↦ gridValue_abs_le (x i)
  · exact hx

/-- The fourteen-coordinate instance used in the quantitative cubic gap. -/
theorem exists_fourteen_cube_point (a : Fin 3 → Fin 14 → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (ha : ∀ h, ∃ j, δ ≤ |a h j|) :
    ∃ z : Fin 14 → ℝ, (∀ i, |z i| ≤ 1) ∧
      ∀ h, δ / 12 ≤ |∑ i, a h i * z i| := by
  obtain ⟨z, _, hz, ha⟩ := exists_cube_point_avoids_three a δ hδ ha
  exact ⟨z, hz, ha⟩

end
end HeadComplexity.FiniteGridAvoidance
