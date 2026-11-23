import HeadComplexity.Results.AxisZeroTransfer

set_option linter.style.header false

/-! Exact strict-axis repair of reverse grid compilers, with `3H + 3` heads. -/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

/-- A reverse affine ratio positive on the entire Boolean cube. -/
structure StrictReverseRatio (n : ℕ) where
  a₀ : ℝ
  b₀ : ℝ
  a : Fin n → ℝ
  b : Fin n → ℝ
  positive : ∀ bits, 0 < affineValue b₀ b bits
  negative : ∀ k, b k < 0

noncomputable def StrictReverseRatio.value {n : ℕ} (R : StrictReverseRatio n)
    (bits : Fin n → Bool) : ℝ :=
  affineValue R.a₀ R.a bits / affineValue R.b₀ R.b bits

private theorem repair_split_bits {r s : ℕ} (bits : Fin (r + s) → Bool) :
    Fin.addCases (fun i ↦ bits (Fin.castAdd s i))
      (fun j ↦ bits (Fin.natAdd r j)) = bits := by
  funext k
  refine Fin.addCases ?_ ?_ k <;> intro i <;> simp

private theorem affine_split {r s : ℕ} (c : ℝ) (a : Fin r → ℝ)
    (b : Fin s → ℝ) (z : Fin r → Bool) (w : Fin s → Bool) :
    affineValue c (Fin.addCases a b) (Fin.addCases z w) =
      c + (∑ i, a i * boolToReal (z i)) + ∑ j, b j * boolToReal (w j) := by
  simp [affineValue, Fin.sum_univ_add, add_assoc]

private theorem affine_mono {n : ℕ} (c : ℝ) (a b : Fin n → ℝ)
    (hab : ∀ k, a k ≤ b k) (bits : Fin n → Bool) :
    affineValue c a bits ≤ affineValue c b bits := by
  unfold affineValue
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hab k) (by cases bits k <;> norm_num [boolToReal])

private theorem exists_negative_upper {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ k, b k < 0) : ∃ t : ℝ, t < 0 ∧ ∀ k, b k ≤ t := by
  have hfin (S : Finset (Fin n)) : ∃ t : ℝ, t < 0 ∧ ∀ k ∈ S, b k ≤ t := by
    induction S using Finset.induction_on with
    | empty => exact ⟨-1, by norm_num, by simp⟩
    | @insert k S hk ih =>
      obtain ⟨t, ht, hbS⟩ := ih
      refine ⟨max (b k) t, max_lt (hb k) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_max_left _ _
      · exact (hbS j hj).trans (le_max_right _ _)
  obtain ⟨t, ht, hbt⟩ := hfin Finset.univ
  exact ⟨t, ht, fun k ↦ hbt k (Finset.mem_univ k)⟩

/-- A family of strict reverse grid heads with an arbitrary scalar bias. -/
structure StrictReverseGridData (r s H : ℕ) where
  bias : ℝ
  head : Fin H → StrictReverseRatio (r + s)

noncomputable def StrictReverseGridData.score {r s H : ℕ}
    (L : StrictReverseGridData r s H) (bits : Fin (r + s) → Bool) : ℝ :=
  L.bias + ∑ h, (L.head h).value bits

/-- The unproved reverse grid compiler hypothesis without an axis condition. -/
def HasStrictReverseGridCompiler (r s M : ℕ) : Prop :=
  ∀ table : Fin r → Fin s → Bool, ∃ H ≤ M, ∃ L : StrictReverseGridData r s H,
    ∀ i j, 0 < outputSign (table i j) * L.score (localGrid i j)

/-- Exact axis cancellation for one head, with row and column grid correction. -/
theorem strict_reverse_ratio_axisize {r s : ℕ} (R : StrictReverseRatio (r + s)) :
    ∃ (Q : Fin 3 → StrictReverseRatio (r + s))
      (row : Fin r → ℝ) (col : Fin s → ℝ),
      (∀ w : Fin s → Bool,
        (∑ h, (Q h).value (Fin.addCases (fun _ : Fin r ↦ false) w)) = 0) ∧
      (∀ z : Fin r → Bool,
        (∑ h, (Q h).value (Fin.addCases z (fun _ : Fin s ↦ false))) = 0) ∧
      (∀ i j, (∑ h, (Q h).value (localGrid i j)) + row i + col j =
        R.value (localGrid i j)) := by
  classical
  obtain ⟨t, ht, hbt⟩ := exists_negative_upper R.b R.negative
  have hb₀ : 0 < R.b₀ := by simpa [affineValue, boolToReal] using R.positive (fun _ ↦ false)
  let k := R.a₀ / R.b₀
  let a : Fin (r + s) → ℝ := fun i ↦ R.a i - k * R.b i
  let al : Fin r → ℝ := fun i ↦ a (Fin.castAdd s i)
  let ar : Fin s → ℝ := fun j ↦ a (Fin.natAdd r j)
  let bl : Fin r → ℝ := fun i ↦ R.b (Fin.castAdd s i)
  let br : Fin s → ℝ := fun j ↦ R.b (Fin.natAdd r j)
  let main : StrictReverseRatio (r + s) := { R with a₀ := 0, a := a }
  let left : StrictReverseRatio (r + s) :=
    { a₀ := 0, b₀ := R.b₀
      a := Fin.addCases (fun i ↦ -al i) (fun _ ↦ 0)
      b := Fin.addCases bl (fun _ ↦ t)
      positive := fun bits ↦ (R.positive bits).trans_le (affine_mono R.b₀ _ _
        (fun k ↦ Fin.addCases (fun i ↦ by simp [bl])
          (fun j ↦ by simpa using hbt (Fin.natAdd r j)) k) bits)
      negative := fun k ↦ Fin.addCases (fun i ↦ by simpa [bl] using R.negative (Fin.castAdd s i))
        (fun _ ↦ by simpa using ht) k }
  let right : StrictReverseRatio (r + s) :=
    { a₀ := 0, b₀ := R.b₀
      a := Fin.addCases (fun _ ↦ 0) (fun j ↦ -ar j)
      b := Fin.addCases (fun _ ↦ t) br
      positive := fun bits ↦ (R.positive bits).trans_le (affine_mono R.b₀ _ _
        (fun k ↦ Fin.addCases (fun i ↦ by simpa using hbt (Fin.castAdd s i))
          (fun j ↦ by simp [br]) k) bits)
      negative := fun k ↦ Fin.addCases (fun _ ↦ by simpa using ht)
        (fun j ↦ by simpa [br] using R.negative (Fin.natAdd r j)) k }
  let Q : Fin 3 → StrictReverseRatio (r + s) := ![main, left, right]
  let row : Fin r → ℝ := fun i ↦ k + al i / (R.b₀ + bl i + t)
  let col : Fin s → ℝ := fun j ↦ ar j / (R.b₀ + t + br j)
  have hnorm (bits : Fin (r + s) → Bool) : main.value bits = R.value bits - k := by
    have hd := ne_of_gt (R.positive bits)
    have ha : affineValue 0 a bits = affineValue R.a₀ R.a bits - k * affineValue R.b₀ R.b bits := by
      simp only [affineValue, zero_add, a, sub_mul, Finset.sum_sub_distrib,
        mul_assoc]
      have hk : k * R.b₀ = R.a₀ := div_mul_cancel₀ _ (ne_of_gt hb₀)
      rw [mul_add, hk]
      simp only [Finset.mul_sum]
      ring
    change affineValue 0 a bits / _ = _
    rw [ha, sub_div, mul_div_cancel_right₀ _ hd]
    rfl
  have hsplit (bits : Fin (r + s) → Bool) :
      affineValue 0 a bits = affineValue 0 (Fin.addCases al ar) bits := by
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [al, ar]
  refine ⟨Q, row, col, ?_, ?_, ?_⟩
  · intro w
    simp only [Q, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    change main.value _ + (left.value _ + right.value _) = 0
    unfold StrictReverseRatio.value
    dsimp [main, left, right]
    rw [hsplit]
    simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_mul, Finset.sum_neg_distrib]
    simp [boolToReal, ar, br, neg_div]
  · intro z
    simp only [Q, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    change main.value _ + (left.value _ + right.value _) = 0
    unfold StrictReverseRatio.value
    dsimp [main, left, right]
    rw [hsplit]
    simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      neg_mul, Finset.sum_neg_distrib]
    simp [boolToReal, al, bl, neg_div]
  · intro i j
    simp only [Q, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    rw [hnorm]
    have hl : left.value (localGrid i j) = -al i / (R.b₀ + bl i + t) := by
      change affineValue 0 (Fin.addCases (fun i ↦ -al i) (fun _ ↦ 0))
        (Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j))) /
        affineValue R.b₀ (Fin.addCases bl (fun _ ↦ t))
          (Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j))) = _
      simp [affine_split, boolToReal]
    have hr : right.value (localGrid i j) = -ar j / (R.b₀ + t + br j) := by
      change affineValue 0 (Fin.addCases (fun _ ↦ 0) (fun j ↦ -ar j))
        (Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j))) /
        affineValue R.b₀ (Fin.addCases (fun _ ↦ t) br)
          (Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j))) = _
      simp [affine_split, boolToReal]
    rw [hl, hr]
    dsimp [row, col]
    ring

private theorem affine_grid {r s : ℕ} (c : ℝ) (a : Fin r → ℝ)
    (b : Fin s → ℝ) (i : Fin r) (j : Fin s) :
    affineValue c (Fin.addCases a b) (localGrid i j) = c + a i + b j := by
  change affineValue c (Fin.addCases a b)
    (Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j))) = _
  simp [affine_split, boolToReal]

private theorem bounded_slopes_positive {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, -2 ≤ b i) (bits : Fin n → Bool) :
    0 < affineValue (2 * (n : ℝ) + 4) b bits := by
  have hh : (∑ i : Fin n, (-2 : ℝ)) ≤ ∑ i, b i * boolToReal (bits i) := by
    apply Finset.sum_le_sum
    intro i _
    cases bits i <;> simp [boolToReal, hb i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  unfold affineValue
  linarith

/-- Arbitrary additive row and column data have a three-head strict axis-zero
realization on the grid. This repairs the grid changes from axis subtraction. -/
theorem strict_axis_row_col_repair {r s : ℕ} (row : Fin r → ℝ) (col : Fin s → ℝ) :
    ∃ Q : Fin 3 → StrictReverseRatio (r + s),
      (∀ w : Fin s → Bool,
        (∑ h, (Q h).value (Fin.addCases (fun _ : Fin r ↦ false) w)) = 0) ∧
      (∀ z : Fin r → Bool,
        (∑ h, (Q h).value (Fin.addCases z (fun _ : Fin s ↦ false))) = 0) ∧
      (∀ i j, (∑ h, (Q h).value (localGrid i j)) = row i + col j) := by
  classical
  let L : ℝ := 2 * ((r + s : ℕ) : ℝ) + 4
  let scale := (L - 2) * (L - 3)
  let mk (a b : Fin (r + s) → ℝ) (hb : ∀ k, -2 ≤ b k) (hneg : ∀ k, b k < 0) :
      StrictReverseRatio (r + s) :=
    { a₀ := 0, b₀ := L, a := a, b := b
      positive := bounded_slopes_positive b hb
      negative := hneg }
  let left := mk (Fin.addCases (fun i ↦ scale * row i) (fun _ ↦ 0))
    (Fin.addCases (fun _ ↦ -1) (fun _ ↦ -2))
    (fun k ↦ Fin.addCases (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) k)
    (fun k ↦ Fin.addCases (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) k)
  let right := mk (Fin.addCases (fun _ ↦ 0) (fun j ↦ scale * col j))
    (Fin.addCases (fun _ ↦ -2) (fun _ ↦ -1))
    (fun k ↦ Fin.addCases (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) k)
    (fun k ↦ Fin.addCases (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) k)
  let common := mk (Fin.addCases (fun i ↦ -(scale * row i)) (fun j ↦ -(scale * col j)))
    (Fin.addCases (fun _ ↦ -1) (fun _ ↦ -1))
    (fun k ↦ Fin.addCases (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) k)
    (fun k ↦ Fin.addCases (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) k)
  let Q : Fin 3 → StrictReverseRatio (r + s) := ![left, right, common]
  have heval (z : Fin r → Bool) (w : Fin s → Bool) :
      (∑ h, (Q h).value (Fin.addCases z w)) =
      (scale * ∑ i, row i * boolToReal (z i)) /
        (L - (∑ i, boolToReal (z i)) - 2 * (∑ j, boolToReal (w j))) +
      (scale * ∑ j, col j * boolToReal (w j)) /
        (L - 2 * (∑ i, boolToReal (z i)) - (∑ j, boolToReal (w j))) -
      (scale * (∑ i, row i * boolToReal (z i)) +
        scale * (∑ j, col j * boolToReal (w j))) /
        (L - (∑ i, boolToReal (z i)) - (∑ j, boolToReal (w j))) := by
    simp only [Q, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    change left.value _ + (right.value _ + common.value _) = _
    unfold StrictReverseRatio.value
    dsimp [left, right, common, mk]
    simp only [affine_split, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
      neg_mul, one_mul, Finset.sum_neg_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro w
    rw [heval]
    simp [boolToReal]
  · intro z
    rw [heval]
    simp [boolToReal]
  · intro i j
    change (∑ h, (Q h).value
      (Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j)))) = _
    rw [heval]
    simp only [boolToReal, decide_eq_true_eq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h2 : L - 2 ≠ 0 := by dsimp [L]; have hn := Nat.cast_nonneg (α := ℝ) (r + s); linarith
    have h3 : L - 3 ≠ 0 := by dsimp [L]; have hn := Nat.cast_nonneg (α := ℝ) (r + s); linarith
    have heq1 : L - 1 - 2 = L - 3 := by ring
    have heq2 : L - 2 - 1 = L - 3 := by ring
    have heq3 : L - 1 - 1 = L - 2 := by ring
    norm_num only [mul_one, heq1, heq2, heq3]
    dsimp [scale]
    field_simp [h2, h3]
    ring

private theorem exists_axis_data_of_family {r s : ℕ} {X : Type*} [Fintype X]
    (Q : X → StrictReverseRatio (r + s))
    (hleft : ∀ w : Fin s → Bool,
      (∑ h, (Q h).value (Fin.addCases (fun _ : Fin r ↦ false) w)) = 0)
    (hright : ∀ z : Fin r → Bool,
      (∑ h, (Q h).value (Fin.addCases z (fun _ : Fin s ↦ false))) = 0) :
    ∃ L : ReverseAxisData r s (Fintype.card X),
      ∀ bits, L.score bits = ∑ h, (Q h).value bits := by
  classical
  let e := (Fintype.equivFin X).symm
  have heval bits : (∑ h, (Q (e h)).value bits) = ∑ h, (Q h).value bits :=
    e.sum_comp (fun h ↦ (Q h).value bits)
  let L : ReverseAxisData r s (Fintype.card X) :=
    { a₀ := fun h ↦ (Q (e h)).a₀, b₀ := fun h ↦ (Q (e h)).b₀
      a := fun h ↦ (Q (e h)).a, b := fun h ↦ (Q (e h)).b
      positive := fun h ↦ (Q (e h)).positive
      negative := fun h ↦ (Q (e h)).negative
      zero_left := fun w ↦ (heval _).trans (hleft w)
      zero_right := fun z ↦ (heval _).trans (hright z) }
  exact ⟨L, heval⟩

/-- Every strict reverse grid score admits an exact axis-zero realization with
`3H + 3` heads. The input dimension and full-cube admissibility are preserved. -/
theorem exists_reverse_axis_repair {r s H : ℕ} (L : StrictReverseGridData r s H) :
    ∃ G : ReverseAxisData r s (3 * H + 3),
      ∀ i j, G.score (localGrid i j) = L.score (localGrid i j) := by
  classical
  choose Q row col hleft hright hgrid using
    fun h ↦ strict_reverse_ratio_axisize (L.head h)
  let R : Fin r → ℝ := fun i ↦ L.bias + ∑ h, row h i
  let C : Fin s → ℝ := fun j ↦ ∑ h, col h j
  obtain ⟨P, hPleft, hPright, hPgrid⟩ := strict_axis_row_col_repair R C
  let X := (Fin H × Fin 3) ⊕ Fin 3
  let A : X → StrictReverseRatio (r + s) := Sum.elim (fun h ↦ Q h.1 h.2) P
  have hsum bits : (∑ h, (A h).value bits) =
      (∑ h, ∑ k, (Q h k).value bits) + ∑ k, (P k).value bits := by
    change (∑ h : (Fin H × Fin 3) ⊕ Fin 3,
      ((Sum.elim (fun h ↦ Q h.1 h.2) P) h).value bits) = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    rfl
  have hAleft (w : Fin s → Bool) :
      (∑ h, (A h).value (Fin.addCases (fun _ : Fin r ↦ false) w)) = 0 := by
    rw [hsum, hPleft]
    simp [hleft]
  have hAright (z : Fin r → Bool) :
      (∑ h, (A h).value (Fin.addCases z (fun _ : Fin s ↦ false))) = 0 := by
    rw [hsum, hPright]
    simp [hright]
  have hAgrid (i : Fin r) (j : Fin s) :
      (∑ h, (A h).value (localGrid i j)) = L.score (localGrid i j) := by
    rw [hsum, hPgrid]
    have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun h _ ↦ hgrid h i j)
    simp only [Finset.sum_add_distrib] at hh
    dsimp [R, C, StrictReverseGridData.score]
    linarith
  obtain ⟨G, heval⟩ := exists_axis_data_of_family A hAleft hAright
  have hresult : ∃ G : ReverseAxisData r s (Fintype.card X),
      ∀ i j, G.score (localGrid i j) = L.score (localGrid i j) :=
    ⟨G, fun i j ↦ (heval _).trans (hAgrid i j)⟩
  have hcard : Fintype.card X = 3 * H + 3 := by
    change Fintype.card ((Fin H × Fin 3) ⊕ Fin 3) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    simp [Nat.mul_comm]
  rw [hcard] at hresult
  exact hresult

/-- Axis vanishing costs only a constant factor once a strict reverse grid
compiler exists. No existence of the sublinear reverse grid compiler is claimed. -/
theorem hasReverseAxisCompiler_of_strictReverseGridCompiler {r s M : ℕ}
    (h : HasStrictReverseGridCompiler r s M) : HasReverseAxisCompiler r s (3 * M + 3) := by
  intro table
  obtain ⟨H, hH, L, hL⟩ := h table
  obtain ⟨G, hG⟩ := exists_reverse_axis_repair L
  refine ⟨3 * H + 3, by omega, G, ?_⟩
  intro i j
  rw [hG]
  exact hL i j

/-- The concrete global bound now requires only a reverse grid compiler;
axis cancellation is supplied by the exact construction above. -/
theorem worstCaseHeadComplexity_real_le_of_strictReverseGridCompiler {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (h : HasStrictReverseGridCompiler a b M) :
    (worstCaseHeadComplexity (a + b) : ℝ) ≤
      484 * (2 : ℝ) ^ (a + b) * (3 * M + 3) / ((a : ℝ) * b) + 2 ^ a + 2 ^ b := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    worstCaseHeadComplexity_real_le_of_reverse_axis_compiler ha hb
      (hasReverseAxisCompiler_of_strictReverseGridCompiler h)

/-- A weak reverse affine ratio, positive on the entire Boolean cube. -/
structure WeakReverseRatio (n : ℕ) where
  a₀ : ℝ
  b₀ : ℝ
  a : Fin n → ℝ
  b : Fin n → ℝ
  positive : ∀ bits, 0 < affineValue b₀ b bits
  nonpositive : ∀ k, b k ≤ 0

noncomputable def WeakReverseRatio.value {n : ℕ} (R : WeakReverseRatio n)
    (bits : Fin n → Bool) : ℝ :=
  affineValue R.a₀ R.a bits / affineValue R.b₀ R.b bits

/-- A uniform weight-two gauge restores strict slopes without altering grid values. -/
theorem weak_reverse_ratio_strictify {r s : ℕ} (R : WeakReverseRatio (r + s)) :
    ∃ Q : StrictReverseRatio (r + s),
      ∀ i j, Q.value (localGrid i j) = R.value (localGrid i j) := by
  classical
  let δ := affineValue R.b₀ R.b (fun _ ↦ true)
  have hδ : 0 < δ := R.positive _
  let ε := δ / (((r + s : ℕ) : ℝ) + 1)
  have hn : 0 ≤ ((r + s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεeq : ε * (((r + s : ℕ) : ℝ) + 1) = δ :=
    div_mul_cancel₀ _ (by positivity)
  have hlower (bits : Fin (r + s) → Bool) : δ ≤ affineValue R.b₀ R.b bits := by
    unfold δ affineValue
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro k _
    have hk := R.nonpositive k
    cases bits k <;> simp [boolToReal, hk]
  have hcount (bits : Fin (r + s) → Bool) :
      (∑ k, boolToReal (bits k)) ≤ ((r + s : ℕ) : ℝ) := by
    calc
      (∑ k, boolToReal (bits k)) ≤ ∑ _ : Fin (r + s), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        cases bits k <;> norm_num [boolToReal]
      _ = _ := by simp
  have heval (bits : Fin (r + s) → Bool) :
      affineValue (R.b₀ + 2 * ε) (fun k ↦ R.b k - ε) bits =
        affineValue R.b₀ R.b bits + 2 * ε - ε * ∑ k, boolToReal (bits k) := by
    simp only [affineValue, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  let Q : StrictReverseRatio (r + s) :=
    { a₀ := R.a₀, b₀ := R.b₀ + 2 * ε, a := R.a, b := fun k ↦ R.b k - ε
      positive := fun bits ↦ by
        rw [heval]
        have hl := hlower bits
        have hc := hcount bits
        nlinarith
      negative := fun k ↦ by have hk := R.nonpositive k; linarith }
  refine ⟨Q, ?_⟩
  intro i j
  have hc : (∑ k, boolToReal (localGrid i j k)) = 2 := by
    change (∑ k : Fin (r + s), boolToReal ((Fin.addCases (fun k : Fin r ↦ decide (k = i))
      (fun k : Fin s ↦ decide (k = j)) : Fin (r + s) → Bool) k)) = 2
    rw [Fin.sum_univ_add]
    norm_num [boolToReal]
  change affineValue R.a₀ R.a (localGrid i j) /
    affineValue (R.b₀ + 2 * ε) (fun k ↦ R.b k - ε) (localGrid i j) = _
  rw [heval, hc]
  have heq : affineValue R.b₀ R.b (localGrid i j) + 2 * ε - ε * 2 =
      affineValue R.b₀ R.b (localGrid i j) := by ring
  rw [heq]
  rfl

/-- Weak reverse grid data retain mandatory positivity on the entire cube. -/
structure WeakReverseGridData (r s H : ℕ) where
  bias : ℝ
  head : Fin H → WeakReverseRatio (r + s)

noncomputable def WeakReverseGridData.score {r s H : ℕ}
    (L : WeakReverseGridData r s H) (bits : Fin (r + s) → Bool) : ℝ :=
  L.bias + ∑ h, (L.head h).value bits

/-- Strictification of a whole weak reverse grid score costs no heads. -/
theorem exists_strict_reverse_grid_of_weak {r s H : ℕ} (L : WeakReverseGridData r s H) :
    ∃ Q : StrictReverseGridData r s H,
      ∀ i j, Q.score (localGrid i j) = L.score (localGrid i j) := by
  classical
  choose Q hQ using fun h ↦ weak_reverse_ratio_strictify (L.head h)
  refine ⟨⟨L.bias, Q⟩, ?_⟩
  intro i j
  simp only [StrictReverseGridData.score, WeakReverseGridData.score, hQ]

/-- Weak reverse input slopes suffice for exact axis repair with strictly
admissible output heads and the same `3H + 3` budget. -/
theorem exists_reverse_axis_repair_of_weak {r s H : ℕ} (L : WeakReverseGridData r s H) :
    ∃ G : ReverseAxisData r s (3 * H + 3),
      ∀ i j, G.score (localGrid i j) = L.score (localGrid i j) := by
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_grid_of_weak L
  obtain ⟨G, hG⟩ := exists_reverse_axis_repair Q
  exact ⟨G, fun i j ↦ (hG i j).trans (hQ i j)⟩

/-- The remaining local universality hypothesis may allow nonpositive slopes. -/
def HasWeakReverseGridCompiler (r s M : ℕ) : Prop :=
  ∀ table : Fin r → Fin s → Bool, ∃ H ≤ M, ∃ L : WeakReverseGridData r s H,
    ∀ i j, 0 < outputSign (table i j) * L.score (localGrid i j)

/-- Weak input slopes and absent axis conditions together cost only the fixed
factor-three exact repair. -/
theorem hasReverseAxisCompiler_of_weakReverseGridCompiler {r s M : ℕ}
    (h : HasWeakReverseGridCompiler r s M) : HasReverseAxisCompiler r s (3 * M + 3) := by
  intro table
  obtain ⟨H, hH, L, hL⟩ := h table
  obtain ⟨G, hG⟩ := exists_reverse_axis_repair_of_weak L
  refine ⟨3 * H + 3, by omega, G, ?_⟩
  intro i j
  rw [hG]
  exact hL i j

end AxisZeroGluing
end HeadComplexity
