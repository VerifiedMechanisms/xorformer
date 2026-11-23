import HeadComplexity.Results.AxisZeroTransfer

set_option linter.style.header false

/-!
# Balanced row numerators with common reverse row slopes

This constructs actual `ReverseAxisData` and actual admissible atoms from
balanced row numerators. It certifies the exact matching/permutation readout
platform, but asserts no superlinear shattering or sublinear local compiler.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

private theorem balancedRows_negative_affine_pos {n : ℕ}
    (C : ℝ) (b : Fin n → ℝ) (hb : ∀ k, b k < 0)
    (hC : (∑ k, -b k) < C) (bits : Fin n → Bool) :
    0 < affineValue C b bits := by
  have hsum : (∑ k, b k) ≤ ∑ k, b k * boolToReal (bits k) := by
    apply Finset.sum_le_sum
    intro k _
    cases bits k <;> simp [boolToReal, (hb k).le]
  simp only [Finset.sum_neg_distrib] at hC
  unfold affineValue
  linarith

private theorem balancedRows_num_eval {r s : ℕ}
    (a : Fin r → ℝ) (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue 0 (Fin.addCases a (fun _ ↦ 0)) (Fin.addCases z w) =
      ∑ i, a i * boolToReal (z i) := by
  simp [affineValue, Fin.sum_univ_add]

private theorem balancedRows_den_eval {r s : ℕ}
    (C : ℝ) (ε : Fin r → ℝ) (u : Fin s → ℝ)
    (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue C (Fin.addCases (fun i ↦ -ε i) (fun j ↦ -u j))
      (Fin.addCases z w) =
      C - (∑ i, ε i * boolToReal (z i)) - ∑ j, u j * boolToReal (w j) := by
  simp [affineValue, Fin.sum_univ_add]
  ring

/-- Common strictly negative row slopes and balanced row-only numerators
give an axis-zero reverse module with exactly the prescribed number of heads. -/
noncomputable def balancedRowsAxisData {r s H : ℕ}
    (C : ℝ) (ε : Fin r → ℝ) (u : Fin H → Fin s → ℝ)
    (a : Fin H → Fin r → ℝ)
    (hε : ∀ i, 0 < ε i) (hu : ∀ h j, 0 < u h j)
    (hC : ∀ h, (∑ i, ε i) + (∑ j, u h j) < C)
    (ha : ∀ i, ∑ h, a h i = 0) : ReverseAxisData r s H := by
  let A : Fin H → Fin (r + s) → ℝ :=
    fun h ↦ Fin.addCases (a h) (fun _ ↦ 0)
  let B : Fin H → Fin (r + s) → ℝ :=
    fun h ↦ Fin.addCases (fun i ↦ -ε i) (fun j ↦ -u h j)
  have hnegative : ∀ h k, B h k < 0 := by
    intro h k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa [B] using neg_neg_of_pos (hε i)
    · simpa [B] using neg_neg_of_pos (hu h j)
  have hmargin : ∀ h, (∑ k, -B h k) < C := by
    intro h
    simpa [B, Fin.sum_univ_add, add_comm] using hC h
  refine
    { a₀ := fun _ ↦ 0
      b₀ := fun _ ↦ C
      a := A
      b := B
      positive := fun h bits ↦ balancedRows_negative_affine_pos C (B h)
        (hnegative h) (hmargin h) bits
      negative := hnegative
      zero_left := ?_
      zero_right := ?_ }
  · intro w
    simp [A, balancedRows_num_eval, boolToReal]
  · intro z
    have hzero : (∑ h, ∑ i, a h i * boolToReal (z i)) = 0 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, ha]
      simp
    change (∑ h, affineValue 0 (Fin.addCases (a h) (fun _ ↦ 0))
      (Fin.addCases z (fun _ : Fin s ↦ false)) /
      affineValue C (Fin.addCases (fun i ↦ -ε i) (fun j ↦ -u h j))
      (Fin.addCases z (fun _ : Fin s ↦ false))) = 0
    simp_rw [balancedRows_num_eval, balancedRows_den_eval]
    simp only [show boolToReal false = 0 from rfl, mul_zero,
      Finset.sum_const_zero, sub_zero]
    rw [← Finset.sum_div, hzero, zero_div]

/-- Exact value on every Boolean input; no approximation is used. -/
theorem balancedRowsAxisData_score {r s H : ℕ}
    (C : ℝ) (ε : Fin r → ℝ) (u : Fin H → Fin s → ℝ)
    (a : Fin H → Fin r → ℝ)
    (hε : ∀ i, 0 < ε i) (hu : ∀ h j, 0 < u h j)
    (hC : ∀ h, (∑ i, ε i) + (∑ j, u h j) < C)
    (ha : ∀ i, ∑ h, a h i = 0)
    (z : Fin r → Bool) (w : Fin s → Bool) :
    (balancedRowsAxisData C ε u a hε hu hC ha).score (Fin.addCases z w) =
      ∑ h, (∑ i, a h i * boolToReal (z i)) /
        (C - (∑ i, ε i * boolToReal (z i)) - ∑ j, u h j * boolToReal (w j)) := by
  change (∑ h, affineValue 0 (Fin.addCases (a h) (fun _ ↦ 0)) (Fin.addCases z w) /
    affineValue C (Fin.addCases (fun i ↦ -ε i) (fun j ↦ -u h j))
      (Fin.addCases z w)) = _
  simp_rw [balancedRows_num_eval, balancedRows_den_eval]

/-- The matching/permutation platform has the exact intended Cauchy grid values. -/
theorem balancedRowsAxisData_grid {r s H : ℕ}
    (C : ℝ) (ε : Fin r → ℝ) (u : Fin H → Fin s → ℝ)
    (a : Fin H → Fin r → ℝ)
    (hε : ∀ i, 0 < ε i) (hu : ∀ h j, 0 < u h j)
    (hC : ∀ h, (∑ i, ε i) + (∑ j, u h j) < C)
    (ha : ∀ i, ∑ h, a h i = 0) (i : Fin r) (j : Fin s) :
    (balancedRowsAxisData C ε u a hε hu hC ha).score (localGrid i j) =
      ∑ h, a h i / (C - ε i - u h j) := by
  unfold localGrid
  rw [balancedRowsAxisData_score]
  simp [boolToReal]

/-- The balanced family also has a witness by original admissible atoms,
with the same head count and unchanged input dimension. -/
theorem exists_balancedRows_atoms {r s H : ℕ}
    (C : ℝ) (ε : Fin r → ℝ) (u : Fin H → Fin s → ℝ)
    (a : Fin H → Fin r → ℝ)
    (hε : ∀ i, 0 < ε i) (hu : ∀ h j, 0 < u h j)
    (hC : ∀ h, (∑ i, ε i) + (∑ j, u h j) < C)
    (ha : ∀ i, ∑ h, a h i = 0) :
    ∃ φ : Fin H → FracAtom (r + s), ∀ bits,
      (∑ h, (φ h).eval bits) =
        (balancedRowsAxisData C ε u a hε hu hC ha).score bits := by
  let L := balancedRowsAxisData C ε u a hε hu hC ha
  have hc : ∀ h : Fin H, 0 < C := by
    intro h
    have he : 0 ≤ ∑ i, ε i := Finset.sum_nonneg fun i _ ↦ (hε i).le
    have hu' : 0 ≤ ∑ j, u h j := Finset.sum_nonneg fun j _ ↦ (hu h j).le
    linarith [hC h]
  have hm : ∀ h, (∑ k, -(L.b h k)) < L.b₀ h := by
    intro h
    change (∑ k, -(Fin.addCases (fun i ↦ -ε i) (fun j ↦ -u h j) k)) < C
    simpa [Fin.sum_univ_add, add_comm] using hC h
  let φ : Fin H → FracAtom (r + s) := fun h ↦
    FracAtom.ofNegativeAffineRatio (L.a₀ h) (L.a h) (L.b₀ h) (L.b h)
      (hc h) (L.negative h) (hm h)
  refine ⟨φ, fun bits ↦ ?_⟩
  unfold ReverseAxisData.score
  apply Finset.sum_congr rfl
  intro h _
  exact FracAtom.ofNegativeAffineRatio_eval _ _ _ _ _ _ _ bits

/-- Pair two copies of a pole set. Balanced numerator sums give exact axes,
while the two copies may assign their column poles independently. -/
theorem exists_pairedCauchy_reverseAxisData {r s G : ℕ}
    (C M : ℝ) (ε : Fin r → ℝ) (ξ : Fin G → ℝ)
    (π : Fin s → Fin G → Fin G)
    (f g : Fin G → Fin r → ℝ)
    (hε : ∀ i, 0 < ε i) (hξ : ∀ h, 0 < ξ h)
    (hbound : ∀ h, ξ h ≤ M)
    (hC : (∑ i, ε i) + (s : ℝ) * M < C)
    (hbalance : ∀ i, ∑ h, f h i = ∑ h, g h i) :
    ∃ L : ReverseAxisData r s (G + G), ∀ i j,
      L.score (localGrid i j) =
        (∑ h, f h i / (C - ε i - ξ h)) -
          ∑ h, g h i / (C - ε i - ξ (π j h)) := by
  let u : Fin (G + G) → Fin s → ℝ :=
    Fin.addCases (fun h _ ↦ ξ h) (fun h j ↦ ξ (π j h))
  let a : Fin (G + G) → Fin r → ℝ :=
    Fin.addCases f (fun h i ↦ -g h i)
  have hu : ∀ h j, 0 < u h j := by
    intro h j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) h
    · simpa [u, -Fin.natAdd_eq_addNat] using hξ k
    · simpa [u, -Fin.natAdd_eq_addNat] using hξ (π j k)
  have hm : ∀ h, (∑ i, ε i) + (∑ j, u h j) < C := by
    intro h
    have hsum : (∑ j, u h j) ≤ (s : ℝ) * M := by
      calc
        _ ≤ ∑ _j : Fin s, M := by
          apply Finset.sum_le_sum
          intro j _
          refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) h
          · simpa [u, -Fin.natAdd_eq_addNat] using hbound k
          · simpa [u, -Fin.natAdd_eq_addNat] using hbound (π j k)
        _ = _ := by simp
    linarith
  have ha : ∀ i, ∑ h, a h i = 0 := by
    intro i
    simp [a, Fin.sum_univ_add, Finset.sum_neg_distrib, hbalance i, -Fin.natAdd_eq_addNat]
  refine ⟨balancedRowsAxisData C ε u a hε hu hm ha, fun i j ↦ ?_⟩
  rw [balancedRowsAxisData_grid]
  simp [a, u, Fin.sum_univ_add, neg_div, Finset.sum_neg_distrib,
    sub_eq_add_neg, -Fin.natAdd_eq_addNat]

private theorem exists_two_weighted_sums {G : ℕ}
    (weights : Fin G → ℝ) (p q : Fin G) (hpq : weights p ≠ weights q)
    (S B : ℝ) :
    ∃ f : Fin G → ℝ, (∑ h, f h) = S ∧ (∑ h, weights h * f h) = B := by
  classical
  let t := (B - S * weights q) / (weights p - weights q)
  let f : Fin G → ℝ := fun h ↦
    (if h = p then t else 0) + (if h = q then S - t else 0)
  refine ⟨f, ?_, ?_⟩
  · simp [f, Finset.sum_add_distrib]
  · have hden : weights p - weights q ≠ 0 := sub_ne_zero.mpr hpq
    simp only [f, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    dsimp [t]
    field_simp
    ring

/-- Every strict exterior Cauchy permutation readout with arbitrary row bias
is represented exactly by `2G` reverse heads, with full Boolean axis zeros.
The theorem does not claim that these readouts shatter a superlinear grid. -/
theorem exists_permutationCauchy_reverseAxisData {r s G : ℕ}
    (C M : ℝ) (ε : Fin r → ℝ) (ξ : Fin G → ℝ)
    (π : Fin s → Fin G → Fin G)
    (a : Fin r → Fin G → ℝ) (bias : Fin r → ℝ)
    (hε : ∀ i, 0 < ε i) (hξ : ∀ h, 0 < ξ h)
    (hbound : ∀ h, ξ h ≤ M)
    (hC : (∑ i, ε i) + (s : ℝ) * M < C)
    (p q : Fin G) (hpq : ξ p ≠ ξ q) :
    ∃ L : ReverseAxisData r s (G + G), ∀ i j,
      L.score (localGrid i j) = bias i +
        ∑ h, a i h / (C - ε i - ξ (π j h)) := by
  have hweights (i : Fin r) :
      (1 / (C - ε i - ξ p)) ≠ (1 / (C - ε i - ξ q)) := by
    intro heq
    have heq' : C - ε i - ξ p = C - ε i - ξ q :=
      inv_injective (by simpa only [one_div] using heq)
    exact hpq (by linarith)
  have hex (i : Fin r) : ∃ f : Fin G → ℝ,
      (∑ h, f h) = -(∑ h, a i h) ∧
      (∑ h, f h / (C - ε i - ξ h)) = bias i := by
    obtain ⟨f, hf, hw⟩ := exists_two_weighted_sums
      (fun h ↦ 1 / (C - ε i - ξ h)) p q (hweights i)
      (-(∑ h, a i h)) (bias i)
    refine ⟨f, hf, ?_⟩
    simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hw
  choose f hf hw using hex
  obtain ⟨L, hL⟩ := exists_pairedCauchy_reverseAxisData C M ε ξ π
    (fun h i ↦ f i h) (fun h i ↦ -a i h) hε hξ hbound hC
    (fun i ↦ by simpa only [Finset.sum_neg_distrib] using hf i)
  refine ⟨L, fun i j ↦ ?_⟩
  rw [hL, hw]
  simp [neg_div, Finset.sum_neg_distrib]

end AxisZeroGluing
end HeadComplexity
