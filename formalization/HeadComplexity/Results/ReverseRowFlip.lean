import HeadComplexity.Results.ReverseRankCorrection

set_option linter.style.header false

/-! Exact row sign multiplication for reverse grid scores. -/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

private theorem row_flip_grid_affine {r s : ℕ} (c : ℝ)
    (a : Fin r → ℝ) (b : Fin s → ℝ) (i : Fin r) (j : Fin s) :
    affineValue c (Fin.addCases a b) (localGrid i j) = c + a i + b j := by
  simp [affineValue, localGrid, Fin.sum_univ_add, boolToReal, add_assoc]

private theorem row_flip_affine_split {r s : ℕ} (c : ℝ)
    (a : Fin (r + s) → ℝ) (i : Fin r) (j : Fin s) :
    affineValue c a (localGrid i j) = c + a (Fin.castAdd s i) + a (Fin.natAdd r j) := by
  simp [affineValue, localGrid, Fin.sum_univ_add, boolToReal, add_assoc]

/-- Removing any collection of negative row slopes improves the full-cube
margin. Numerators may be chosen freely. -/
private noncomputable def rowMaskedRatio {r s : ℕ}
    (R : StrictReverseRatio (r + s)) (active : Fin r → Bool)
    (row : Fin r → ℝ) (col : Fin s → ℝ) : WeakReverseRatio (r + s) where
  a₀ := 0
  a := Fin.addCases row col
  b₀ := R.b₀
  b := Fin.addCases (fun i ↦ if active i then R.b (Fin.castAdd s i) else 0)
    (fun j ↦ R.b (Fin.natAdd r j))
  nonpositive := by
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp only [Fin.addCases_left]
      split <;> linarith [R.negative (Fin.castAdd s i)]
    · intro j
      simpa using (R.negative (Fin.natAdd r j)).le
  positive := by
    intro bits
    apply lt_of_lt_of_le (R.positive bits)
    unfold affineValue
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right
    · refine Fin.addCases ?_ ?_ k
      · intro i
        simp only [Fin.addCases_left]
        split <;> linarith [R.negative (Fin.castAdd s i)]
      · intro j
        simp
    · cases bits k <;> norm_num [boolToReal]

/-- Two masked copies multiply one grid ratio by an arbitrary row sign,
up to a rank-one grid correction. -/
theorem strict_reverse_ratio_row_multiplier {r s : ℕ}
    (R : StrictReverseRatio (r + s)) (coeff : Fin r → ℝ)
    (hc : ∀ i, coeff i = -1 ∨ coeff i = 0 ∨ coeff i = 1) :
    ∃ P M : WeakReverseRatio (r + s), ∃ q : Fin s → ℝ, ∀ i j,
      P.value (localGrid i j) + M.value (localGrid i j) =
        coeff i * (R.value (localGrid i j) - q j) := by
  let A : Fin r → ℝ := fun i ↦ R.a₀ + R.a (Fin.castAdd s i)
  let a : Fin s → ℝ := fun j ↦ R.a (Fin.natAdd r j)
  classical
  let P := rowMaskedRatio R (fun i ↦ decide (coeff i = 1))
    (fun i ↦ if coeff i = 1 then A i else 0) a
  let M := rowMaskedRatio R (fun i ↦ decide (coeff i = -1))
    (fun i ↦ if coeff i = -1 then -A i else 0) (fun j ↦ -a j)
  let q : Fin s → ℝ := fun j ↦ a j / (R.b₀ + R.b (Fin.natAdd r j))
  refine ⟨P, M, q, ?_⟩
  intro i j
  change affineValue 0 (Fin.addCases (fun i ↦ if coeff i = 1 then A i else 0) a)
      (localGrid i j) /
      affineValue R.b₀ (Fin.addCases
        (fun i ↦ if decide (coeff i = 1) then R.b (Fin.castAdd s i) else 0)
        (fun j ↦ R.b (Fin.natAdd r j))) (localGrid i j) +
    affineValue 0 (Fin.addCases (fun i ↦ if coeff i = -1 then -A i else 0) (fun j ↦ -a j))
      (localGrid i j) /
      affineValue R.b₀ (Fin.addCases
        (fun i ↦ if decide (coeff i = -1) then R.b (Fin.castAdd s i) else 0)
        (fun j ↦ R.b (Fin.natAdd r j))) (localGrid i j) = _
  rw [row_flip_grid_affine, row_flip_grid_affine, row_flip_grid_affine, row_flip_grid_affine]
  unfold StrictReverseRatio.value
  rw [row_flip_affine_split, row_flip_affine_split]
  rcases hc i with hi | hi | hi <;> norm_num [hi, A, a, q, div_eq_mul_inv] <;> ring

/-- Every reverse grid score permits arbitrary row sign multiplication at a
constant head cost. Strictification retains the mandatory full-cube margin. -/
theorem exists_strict_reverse_row_multiplier {r s H : ℕ}
    (L : StrictReverseGridData r s H) (coeff : Fin r → ℝ)
    (hc : ∀ i, coeff i = -1 ∨ coeff i = 0 ∨ coeff i = 1) :
    ∃ Q : StrictReverseGridData r s (2 * H + 2), ∀ i j,
      Q.score (localGrid i j) = coeff i * L.score (localGrid i j) := by
  classical
  choose P M q hq using fun h ↦ strict_reverse_ratio_row_multiplier (L.head h) coeff hc
  let v : Fin s → ℝ := fun j ↦ ∑ h, q h j
  obtain ⟨C, hC⟩ := exists_weak_reverse_rank_grid
    (fun _ : Fin 1 ↦ fun i ↦ coeff i) (fun _ : Fin 1 ↦ v)
    (fun i ↦ coeff i * L.bias) (fun _ ↦ 0) 0
  let G : WeakReverseGridData r s ((H + H) + 2) :=
    { bias := C.bias
      head := Fin.addCases (Fin.addCases P M) C.head }
  have hG (i : Fin r) (j : Fin s) :
      G.score (localGrid i j) = coeff i * L.score (localGrid i j) := by
    have hpair : (∑ h, (P h).value (localGrid i j)) +
        (∑ h, (M h).value (localGrid i j)) =
        coeff i * ((∑ h, (L.head h).value (localGrid i j)) - v j) := by
      rw [← Finset.sum_add_distrib]
      simp only [hq, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    have hc := hC i j
    simp only [WeakReverseGridData.score, zero_add, add_zero, Fin.sum_univ_one] at hc
    change C.bias + (∑ h : Fin ((H + H) + 2),
      ((Fin.addCases (Fin.addCases P M) C.head :
        Fin ((H + H) + 2) → WeakReverseRatio (r + s)) h).value (localGrid i j)) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [hpair]
    simp only [StrictReverseGridData.score]
    nlinarith [hc]
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_grid_of_weak G
  have hresult : ∃ Q : StrictReverseGridData r s ((H + H) + 2), ∀ i j,
      Q.score (localGrid i j) = coeff i * L.score (localGrid i j) :=
    ⟨Q, fun i j ↦ (hQ i j).trans (hG i j)⟩
  rw [Nat.two_mul]
  exact hresult

/-- In particular, arbitrary row sign flips have the same constant budget. -/
theorem exists_strict_reverse_row_flip {r s H : ℕ}
    (L : StrictReverseGridData r s H) (sign : Fin r → Bool) :
    ∃ Q : StrictReverseGridData r s (2 * H + 2), ∀ i j,
      Q.score (localGrid i j) = outputSign (sign i) * L.score (localGrid i j) := by
  apply exists_strict_reverse_row_multiplier L (fun i ↦ outputSign (sign i))
  intro i
  cases sign i <;> simp [outputSign]

/-- Renaming coordinates preserves the original ratio admissibility. -/
private noncomputable def reverseRatioReindex {n m : ℕ}
    (e : Fin m ≃ Fin n) (R : StrictReverseRatio n) : StrictReverseRatio m where
  a₀ := R.a₀
  b₀ := R.b₀
  a := fun k ↦ R.a (e k)
  b := fun k ↦ R.b (e k)
  negative := fun k ↦ R.negative (e k)
  positive := by
    intro bits
    have h := R.positive (fun k ↦ bits (e.symm k))
    have heq : (∑ k : Fin m, R.b (e k) * boolToReal (bits k)) =
        ∑ k : Fin n, R.b k * boolToReal (bits (e.symm k)) := by
      simpa using e.sum_comp (fun k ↦ R.b k * boolToReal (bits (e.symm k)))
    simpa only [affineValue, heq] using h

/-- Swapping the two coordinate blocks transposes every represented grid. -/
noncomputable def StrictReverseGridData.transpose {r s H : ℕ}
    (L : StrictReverseGridData r s H) : StrictReverseGridData s r H where
  bias := L.bias
  head := fun h ↦ reverseRatioReindex finAddFlip (L.head h)

theorem StrictReverseGridData.transpose_grid {r s H : ℕ}
    (L : StrictReverseGridData r s H) (i : Fin r) (j : Fin s) :
    L.transpose.score (localGrid j i) = L.score (localGrid i j) := by
  unfold StrictReverseGridData.score
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  simp only [StrictReverseGridData.transpose, reverseRatioReindex, StrictReverseRatio.value]
  rw [row_flip_affine_split, row_flip_affine_split,
    row_flip_affine_split, row_flip_affine_split]
  simp only [finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]
  congr 1 <;> ring

/-- Exact column multipliers include zero masks for stacking separate batches. -/
theorem exists_strict_reverse_column_multiplier {r s H : ℕ}
    (L : StrictReverseGridData r s H) (coeff : Fin s → ℝ)
    (hc : ∀ j, coeff j = -1 ∨ coeff j = 0 ∨ coeff j = 1) :
    ∃ Q : StrictReverseGridData r s (2 * H + 2), ∀ i j,
      Q.score (localGrid i j) = coeff j * L.score (localGrid i j) := by
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_row_multiplier L.transpose coeff hc
  refine ⟨Q.transpose, ?_⟩
  intro i j
  rw [Q.transpose_grid j i, hQ, L.transpose_grid i j]

/-- A row sign followed by a column mask uses `4H+6` strictly admissible heads.
In particular, inactive columns are exactly zero on the promised grid. -/
theorem exists_strict_reverse_row_flip_column_mask {r s H : ℕ}
    (L : StrictReverseGridData r s H) (sign : Fin r → Bool)
    (active : Fin s → Bool) :
    ∃ Q : StrictReverseGridData r s (4 * H + 6), ∀ i j,
      Q.score (localGrid i j) =
        (if active j then 1 else 0) * outputSign (sign i) * L.score (localGrid i j) := by
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_row_flip L sign
  obtain ⟨R, hR⟩ := exists_strict_reverse_column_multiplier Q
    (fun j ↦ if active j then 1 else 0) (fun j ↦ by cases active j <;> simp)
  have heq : 2 * (2 * H + 2) + 2 = 4 * H + 6 := by omega
  have hresult : ∃ R : StrictReverseGridData r s (2 * (2 * H + 2) + 2), ∀ i j,
      R.score (localGrid i j) =
        (if active j then 1 else 0) * outputSign (sign i) * L.score (localGrid i j) := by
    refine ⟨R, ?_⟩
    intro i j
    rw [hR, hQ]
    ring
  rwa [heq] at hresult

/-- Multiplication of Boolean signs, written as a Boolean pattern. -/
def rowSignTranslate {r : ℕ} (v x : Fin r → Bool) : Fin r → Bool :=
  fun i ↦ if v i then x i else !(x i)

private def rowSignEquiv {r : ℕ} (v : Fin r → Bool) :
    (Fin r → Bool) ≃ (Fin r → Bool) where
  toFun := rowSignTranslate v
  invFun := rowSignTranslate v
  left_inv := by
    intro x
    funext i
    cases hv : v i <;> simp [rowSignTranslate, hv]
  right_inv := by
    intro x
    funext i
    cases hv : v i <;> simp [rowSignTranslate, hv]

/-- A common row sign sends all columns into a sufficiently dense pattern
family. This is the finite union bound, with its exact integer hypothesis. -/
theorem exists_row_sign_translate_into_dense {r s : ℕ}
    (good : Finset (Fin r → Bool)) (table : Fin r → Fin s → Bool)
    (hdense : s * (2 ^ r - good.card) < 2 ^ r) :
    ∃ sign : Fin r → Bool, ∀ j,
      rowSignTranslate (fun i ↦ table i j) sign ∈ good := by
  classical
  let bad : Finset (Fin r → Bool) := Finset.univ \ good
  let E : Fin s → ((Fin r → Bool) ≃ (Fin r → Bool)) :=
    fun j ↦ rowSignEquiv (fun i ↦ table i j)
  let B : Fin s → Finset (Fin r → Bool) := fun j ↦ bad.map (E j).toEmbedding
  have hbad : bad.card = 2 ^ r - good.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ good)]
    simp
  by_contra hn
  push Not at hn
  have hcover : (Finset.univ : Finset (Fin r → Bool)) ⊆
      Finset.univ.biUnion B := by
    intro x hx
    obtain ⟨j, hj⟩ := hn x
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨E j x, ?_, ?_⟩
    · simp only [bad, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hj
    · exact (E j).apply_symm_apply x
  have hbound : 2 ^ r ≤ s * (2 ^ r - good.card) := by
    calc
      2 ^ r = (Finset.univ : Finset (Fin r → Bool)).card := by simp
      _ ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hcover
      _ ≤ ∑ j : Fin s, (B j).card := Finset.card_biUnion_le
      _ = s * (2 ^ r - good.card) := by simp [B, hbad]
  omega

/-- A dense family promise retains full-cube positivity jointly for every
collection of `s` good columns. It does not merely assume separate one-column
realizations. This property is not asserted unconditionally. -/
def HasDenseReverseGridFamily (r s M : ℕ) : Prop :=
  ∃ good : Finset (Fin r → Bool),
    s * (2 ^ r - good.card) < 2 ^ r ∧
    ∀ table : Fin r → Fin s → Bool, (∀ j, (fun i ↦ table i j) ∈ good) →
      ∃ H ≤ M, ∃ L : StrictReverseGridData r s H,
        ∀ i j, 0 < outputSign (table i j) * L.score (localGrid i j)

/-- Dense column-pattern universality suffices for full sign-table universality
after a common row sign and exact constant-cost row multiplication. -/
theorem hasStrictReverseGridCompiler_of_dense_family {r s M : ℕ}
    (hdense : HasDenseReverseGridFamily r s M) :
    HasStrictReverseGridCompiler r s (2 * M + 2) := by
  intro table
  obtain ⟨good, hcard, hgood⟩ := hdense
  obtain ⟨sign, hsign⟩ := exists_row_sign_translate_into_dense good table hcard
  let table' : Fin r → Fin s → Bool :=
    fun i j ↦ rowSignTranslate (fun k ↦ table k j) sign i
  obtain ⟨H, hH, L, hL⟩ := hgood table' hsign
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_row_flip L sign
  refine ⟨2 * H + 2, by omega, Q, ?_⟩
  intro i j
  rw [hQ]
  have h := hL i j
  change 0 < outputSign (rowSignTranslate (fun k ↦ table k j) sign i) *
    L.score (localGrid i j) at h
  cases hs : sign i <;> cases ht : table i j <;>
    simpa [rowSignTranslate, outputSign, hs, ht] using h

/-- The dense-family promise also transfers to exact axes, with a fixed
constant budget. The local high-density hypothesis remains explicit. -/
theorem hasReverseAxisCompiler_of_dense_family {r s M : ℕ}
    (hdense : HasDenseReverseGridFamily r s M) :
    HasReverseAxisCompiler r s (6 * M + 9) := by
  have h := hasReverseAxisCompiler_of_strictReverseGridCompiler
    (hasStrictReverseGridCompiler_of_dense_family hdense)
  convert h using 1; omega

end AxisZeroGluing
end HeadComplexity
