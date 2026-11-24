import HeadComplexity.Results.ReverseBalancedRows
import HeadComplexity.Results.ReverseGridEmbedding
import HeadComplexity.Results.AffinePlaneCompiler

set_option linter.style.header false

/-!
# Joint axis repair of rank and Cauchy factors

Common axis denominators allow the rank factors of a single local table to
share one cancellation head. This saves a constant factor in the known local
compiler. The arbitrary column data are still supplied separately for each
table, so this theorem does not provide an asymptotic saving across cells.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private theorem exists_rank_parameters {r L : ℕ} (f : Fin L → Fin r → ℝ) :
    ∃ C M : Fin L → ℝ, ∃ u : Fin L → Fin r → ℝ,
      (∀ h, 0 < M h) ∧ (∀ h i, 0 < u h i) ∧
      (∀ h i, u h i / (M h + u h i) ≤ 1 / (2 * ((r : ℝ) + 1))) ∧
      (∀ h i, u h i = f h i + C h) := by
  let C : Fin L → ℝ := fun h ↦ 1 + ∑ i, |f h i|
  have hC (h : Fin L) : 0 < C h := by dsimp [C]; positivity
  have hf (h : Fin L) (i : Fin r) : |f h i| < C h := by
    have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) ↦ abs_nonneg (f h k))
      (Finset.mem_univ i)
    dsimp [C]
    linarith
  let u : Fin L → Fin r → ℝ := fun h i ↦ f h i + C h
  have hu (h : Fin L) (i : Fin r) : 0 < u h i := by
    have h₁ := hf h i
    have h₂ := neg_abs_le (f h i)
    dsimp [u]
    linarith
  have huC (h : Fin L) (i : Fin r) : u h i < 2 * C h := by
    have h₁ := hf h i
    have h₂ := le_abs_self (f h i)
    dsimp [u]
    linarith
  let M : Fin L → ℝ := fun h ↦ 4 * ((r : ℝ) + 1) * C h
  have hM (h : Fin L) : 0 < M h := by dsimp [M]; positivity
  refine ⟨C, M, u, hM, hu, ?_, fun _ _ ↦ rfl⟩
  intro h i
  have hd : 0 < M h + u h i := add_pos (hM h) (hu h i)
  apply (div_le_iff₀ hd).mpr
  have hmul : (1 / (2 * ((r : ℝ) + 1))) * M h = 2 * C h := by
    dsimp [M]
    field_simp
    ring
  rw [mul_add, hmul]
  have hpos : 0 < (1 / (2 * ((r : ℝ) + 1))) * u h i :=
    mul_pos (by positivity) (hu h i)
  linarith [huC h i]

/-- All factors share one column-axis subtraction. The remaining correction
is one row vector and one column vector, handled by three fixed-shape heads. -/
theorem exists_reverse_axis_rank_grid_joint {r s L : ℕ}
    (f : Fin L → Fin r → ℝ) (g : Fin L → Fin s → ℝ)
    (row : Fin r → ℝ) (col : Fin s → ℝ) (bias : ℝ) :
    ∃ Q : ReverseAxisData r s (L + 4), ∀ i j,
      Q.score (localGrid i j) =
        bias + row i + col j + ∑ h, f h i * g h j := by
  classical
  obtain ⟨C, M, u, hM, hu, hsmall, hueq⟩ := exists_rank_parameters f
  let ε : ℝ := 1 / (4 * (((r + s : ℕ) : ℝ) + 1))
  let B : ℝ := 1 + 2 * ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεsmall : (((r + s : ℕ) : ℝ)) * ε < 1 / 4 := by
    have heq : ε * (4 * (((r + s : ℕ) : ℝ) + 1)) = 1 := by
      dsimp [ε]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  let p : Fin (L + 1) → Fin r → ℝ :=
    Fin.addCases (fun h i ↦ ε + u h i / (M h + u h i)) (fun _ _ ↦ ε)
  let a : Fin (L + 1) → Fin s → ℝ :=
    Fin.addCases (fun h j ↦ M h * g h j) (fun _ j ↦ -(∑ h, M h * g h j))
  have hp : ∀ h i, 0 < p h i := by
    intro h i
    refine Fin.addCases ?_ ?_ h
    · intro k
      simp only [p, Fin.addCases_left]
      exact add_pos hε (div_pos (hu k i) (add_pos (hM k) (hu k i)))
    · intro k
      simpa only [p, Fin.addCases_right] using hε
  have hbound (h : Fin (L + 1)) :
      (∑ _j : Fin s, ε) + (∑ i, p h i) < B := by
    have hs : (∑ i, p h i) ≤ (r : ℝ) * ε +
        (r : ℝ) / (2 * ((r : ℝ) + 1)) := by
      calc
        (∑ i, p h i) ≤ ∑ _i : Fin r, (ε + 1 / (2 * ((r : ℝ) + 1))) := by
          apply Finset.sum_le_sum
          intro i _
          refine Fin.addCases ?_ ?_ h
          · intro k
            simp only [p, Fin.addCases_left]
            linarith [hsmall k i]
          · intro k
            simp only [p, Fin.addCases_right]
            have hh : (0 : ℝ) ≤ 1 / (2 * ((r : ℝ) + 1)) := by positivity
            linarith
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have hhalf : (r : ℝ) / (2 * ((r : ℝ) + 1)) < 1 / 2 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ((r : ℝ) + 1))).mpr
      linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [B]
    push_cast at hεsmall
    nlinarith
  have ha (j : Fin s) : (∑ h, a h j) = 0 := by
    simp [a, Fin.sum_univ_add]
  let Q₀ : ReverseAxisData r s (L + 1) :=
    (balancedRowsAxisData B (fun _ : Fin s ↦ ε) p a (fun _ ↦ hε) hp hbound ha).transpose
  have hQ₀ (i : Fin r) (j : Fin s) :
      Q₀.score (localGrid i j) = ∑ h, (C h + f h i) * g h j := by
    dsimp [Q₀]
    rw [ReverseAxisData.transpose_grid, balancedRowsAxisData_grid]
    simp only [a, p, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    have hbase : B - ε - ε = 1 := by dsimp [B]; ring
    rw [hbase, div_one]
    have hterm (h : Fin L) :
        M h * g h j / (B - ε - (ε + u h i / (M h + u h i))) =
          (M h + C h + f h i) * g h j := by
      have hden : M h + u h i ≠ 0 := (add_pos (hM h) (hu h i)).ne'
      have hMne : M h ≠ 0 := (hM h).ne'
      have hd : B - ε - (ε + u h i / (M h + u h i)) =
          M h / (M h + u h i) := by
        dsimp [B]
        field_simp [hden]
        ring
      rw [hd, div_div_eq_mul_div]
      field_simp [hMne]
      rw [hueq]
      ring
    simp_rw [hterm]
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  obtain ⟨P, hPleft, hPright, hPgrid⟩ := strict_axis_row_col_repair
    (fun i ↦ bias + row i) (fun j ↦ col j - ∑ h, C h * g h j)
  let Q₁ : ReverseAxisData r s 3 :=
    { a₀ := fun h ↦ (P h).a₀
      b₀ := fun h ↦ (P h).b₀
      a := fun h ↦ (P h).a
      b := fun h ↦ (P h).b
      positive := fun h ↦ (P h).positive
      negative := fun h ↦ (P h).negative
      zero_left := hPleft
      zero_right := hPright }
  refine ⟨Q₀.append Q₁, ?_⟩
  intro i j
  rw [ReverseAxisData.append_score, hQ₀]
  change _ + (∑ h, (P h).value (localGrid i j)) = _
  rw [hPgrid]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

private theorem exists_axis_sum_family {r s G H : ℕ}
    (Q : Fin G → ReverseAxisData r s H) :
    ∃ R : ReverseAxisData r s (G * H), ∀ bits,
      R.score bits = ∑ g, (Q g).score bits := by
  classical
  let e : Fin (G * H) ≃ (Fin G × Fin H) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  have heval (bits : Fin (r + s) → Bool) :
      (∑ h, affineValue ((Q (e h).1).a₀ (e h).2) ((Q (e h).1).a (e h).2) bits /
        affineValue ((Q (e h).1).b₀ (e h).2) ((Q (e h).1).b (e h).2) bits) =
      ∑ g, (Q g).score bits := by
    have he := e.sum_comp (fun h : Fin G × Fin H ↦
      affineValue ((Q h.1).a₀ h.2) ((Q h.1).a h.2) bits /
        affineValue ((Q h.1).b₀ h.2) ((Q h.1).b h.2) bits)
    simpa only [Fintype.sum_prod_type, ReverseAxisData.score] using he
  refine ⟨{
    a₀ := fun h ↦ (Q (e h).1).a₀ (e h).2
    b₀ := fun h ↦ (Q (e h).1).b₀ (e h).2
    a := fun h ↦ (Q (e h).1).a (e h).2
    b := fun h ↦ (Q (e h).1).b (e h).2
    positive := fun h ↦ (Q (e h).1).positive (e h).2
    negative := fun h ↦ (Q (e h).1).negative (e h).2
    zero_left := fun w ↦ by
      rw [heval]
      simp only [ReverseAxisData.score, ReverseAxisData.zero_left, Finset.sum_const_zero]
    zero_right := fun z ↦ by
      rw [heval]
      simp only [ReverseAxisData.score, ReverseAxisData.zero_right, Finset.sum_const_zero]
    }, heval⟩

/-- Each compact Cauchy correction uses one moving-token head and one fixed
axis subtraction. The entire remaining grid correction is a row vector. -/
theorem exists_reverse_axis_cauchy_family_joint {r s G : ℕ}
    (δ : ℝ) (A D : Fin G → Fin r → ℝ) (T : Fin G → Fin s → ℝ)
    (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (hD : ∀ h i, 1 - δ < D h i ∧ D h i < 1)
    (hT : ∀ h j, 0 < T h j ∧ T h j < δ) :
    ∃ Q : ReverseAxisData r s (2 * G), ∀ i j,
      Q.score (localGrid i j) =
        ∑ h, (A h i / (D h i - T h j) - A h i / (D h i - δ / 2)) := by
  let u : Fin G → Fin 2 → Fin s → ℝ := fun h ↦ ![T h, fun _ ↦ δ / 2]
  let a : Fin G → Fin 2 → Fin r → ℝ := fun h ↦ ![A h, fun i ↦ -A h i]
  have hε (h : Fin G) (i : Fin r) : 0 < 1 - D h i := by linarith [(hD h i).2]
  have hu (h : Fin G) (k : Fin 2) (j : Fin s) : 0 < u h k j := by
    fin_cases k
    · change 0 < T h j
      exact (hT h j).1
    · change 0 < δ / 2
      positivity
  have hule (h : Fin G) (k : Fin 2) (j : Fin s) : u h k j ≤ δ := by
    fin_cases k
    · change T h j ≤ δ
      exact (hT h j).2.le
    · change δ / 2 ≤ δ
      linarith
  have hbound (h : Fin G) (k : Fin 2) :
      (∑ i, (1 - D h i)) + (∑ j, u h k j) < 1 := by
    have hl : (∑ i, (1 - D h i)) ≤ (r : ℝ) * δ := by
      calc
        _ ≤ ∑ _i : Fin r, δ := Finset.sum_le_sum fun i _ ↦ by linarith [(hD h i).1]
        _ = _ := by simp
    have hr : (∑ j, u h k j) ≤ (s : ℝ) * δ := by
      calc
        _ ≤ ∑ _j : Fin s, δ := Finset.sum_le_sum fun j _ ↦ hule h k j
        _ = _ := by simp
    push_cast at hsize
    nlinarith
  have ha (h : Fin G) (i : Fin r) : (∑ k, a h k i) = 0 := by
    simp [a, Fin.sum_univ_two]
  let Q : Fin G → ReverseAxisData r s 2 := fun h ↦
    balancedRowsAxisData 1 (fun i ↦ 1 - D h i) (u h) (a h)
      (hε h) (hu h) (hbound h) (ha h)
  have hex := exists_axis_sum_family Q
  rw [Nat.mul_comm G 2] at hex
  obtain ⟨R, hR⟩ := hex
  refine ⟨R, ?_⟩
  intro i j
  rw [hR]
  apply Finset.sum_congr rfl
  intro h _
  dsimp [Q]
  rw [balancedRowsAxisData_grid]
  have hden (x : ℝ) : 1 - (1 - D h i) - x = D h i - x := by ring
  simp only [a, u, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hden, hden]
  simp only [neg_div, sub_eq_add_neg]

/-- Complete exact budget for arbitrary rank factors plus exterior Cauchy
corrections. Axis subtraction is charged before the three-head row/column
repair, so it costs `L + 2G + 4` in total. -/
theorem exists_reverse_axis_rank_cauchy_grid_joint {r s L G : ℕ}
    (δ : ℝ) (f : Fin L → Fin r → ℝ) (g : Fin L → Fin s → ℝ)
    (A D : Fin G → Fin r → ℝ) (T : Fin G → Fin s → ℝ)
    (row : Fin r → ℝ) (col : Fin s → ℝ) (bias : ℝ)
    (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (hD : ∀ h i, 1 - δ < D h i ∧ D h i < 1)
    (hT : ∀ h j, 0 < T h j ∧ T h j < δ) :
    ∃ Q : ReverseAxisData r s (L + 2 * G + 4), ∀ i j,
      Q.score (localGrid i j) = bias + row i + col j +
        (∑ h, f h i * g h j) + ∑ h, A h i / (D h i - T h j) := by
  obtain ⟨C, hC⟩ := exists_reverse_axis_cauchy_family_joint δ A D T hδ hsize hD hT
  obtain ⟨R, hR⟩ := exists_reverse_axis_rank_grid_joint f g
    (fun i ↦ row i + ∑ h, A h i / (D h i - δ / 2)) col bias
  have hcount : (L + 4) + 2 * G = L + 2 * G + 4 := by omega
  have hex : ∃ Q : ReverseAxisData r s ((L + 4) + 2 * G), ∀ i j,
      Q.score (localGrid i j) = bias + row i + col j +
        (∑ h, f h i * g h j) + ∑ h, A h i / (D h i - T h j) := by
    refine ⟨R.append C, ?_⟩
    intro i j
    rw [ReverseAxisData.append_score, hR, hC, Finset.sum_sub_distrib]
    ring
  rw [← hcount]
  exact hex


/-- Exact affine-plane decoding with joint axis cancellation. Every point
correction is charged twice, and all rank-axis terms share one denominator. -/
theorem exists_affinePlane_reverse_axis_joint {F : Type*} [Field F] [Fintype F]
    {r s : ℕ} (δ : ℝ) (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (pole token : F → ℝ)
    (hpole : ∀ a, 1 - δ < pole a ∧ pole a < 1)
    (htoken : ∀ z, 0 < token z ∧ token z < δ)
    (point : Fin r → F × F) (memory : (F × F) → Fin s → F)
    (η : Fin r → F → ℝ) (rowBias : Fin r → ℝ) :
    ∃ Q : ReverseAxisData r s (3 * Fintype.card (F × F) + 4),
      ∀ i j, Q.score (localGrid i j) =
        rowBias i + ∑ a : F, η i a / (pole a - token (memory (point i) j)) := by
  classical
  let N := Fintype.card (F × F)
  let e : Fin N ≃ (F × F) := (Fintype.equivFin (F × F)).symm
  let Z : (F × F) → Fin s → ℝ := fun L j ↦
    ∑ g : F × F, if g.2 = L.1 * g.1 + L.2 then
      1 / (pole L.1 - token (memory g j)) else 0
  let f : Fin N → Fin r → ℝ := fun l i ↦
    if (e l).2 = (point i).2 - (e l).1 * (point i).1 then η i (e l).1 else 0
  let off : Fin r → Fin s → ℝ := fun i j ↦
    ∑ g : F × F, if g.1 ≠ (point i).1 then
      η i (affinePlaneSlope (point i) g) /
        (pole (affinePlaneSlope (point i) g) - token (memory g j)) else 0
  have hline (i : Fin r) (j : Fin s) :
      (∑ l : Fin N, f l i * Z (e l) j) =
        (∑ a : F, η i a / (pole a - token (memory (point i) j))) + off i j := by
    have hReindex : (∑ l : Fin N, f l i * Z (e l) j) =
        ∑ L : F × F,
          (if L.2 = (point i).2 - L.1 * (point i).1 then η i L.1 else 0) * Z L j :=
      e.sum_comp (fun L : F × F ↦
        (if L.2 = (point i).2 - L.1 * (point i).1 then η i L.1 else 0) * Z L j)
    rw [hReindex, affinePlane_line_rank_identity]
    have hInc := affinePlane_weighted_pencil_identity (point i) (η i)
      (fun a g ↦ 1 / (pole a - token (memory g j)))
    dsimp [Z]
    simp only [mul_one_div] at hInc
    exact hInc
  let A : (F × F) → Fin r → ℝ := fun g i ↦
    if g.1 ≠ (point i).1 then -η i (affinePlaneSlope (point i) g) else 0
  let D : (F × F) → Fin r → ℝ := fun g i ↦ pole (affinePlaneSlope (point i) g)
  have hCorr (i : Fin r) (j : Fin s) :
      (∑ l : Fin N, A (e l) i / (D (e l) i - token (memory (e l) j))) = -off i j := by
    have hReindex : (∑ l : Fin N, A (e l) i /
        (D (e l) i - token (memory (e l) j))) =
        ∑ g : F × F, A g i / (D g i - token (memory g j)) :=
      e.sum_comp (fun g : F × F ↦ A g i / (D g i - token (memory g j)))
    rw [hReindex]
    dsimp [off]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro g _
    dsimp [A, D]
    split_ifs <;> simp only [neg_div, zero_div, neg_zero]
  have hex := exists_reverse_axis_rank_cauchy_grid_joint δ f (fun l ↦ Z (e l))
    (fun l ↦ A (e l)) (fun l ↦ D (e l)) (fun l j ↦ token (memory (e l) j))
    rowBias (fun _ ↦ 0) 0 hδ hsize (fun _ _ ↦ hpole _) (fun _ _ ↦ htoken _)
  have hcount : N + 2 * N + 4 = 3 * Fintype.card (F × F) + 4 := by dsimp [N]; omega
  rw [hcount] at hex
  obtain ⟨Q, hQ⟩ := hex
  refine ⟨Q, ?_⟩
  intro i j
  rw [hQ, hline, hCorr]
  ring

/-- An unconditional axis-zero affine-plane compiler with `3 * 4^a + 4`
heads. This improves the constant in the existing logarithmic saving. -/
theorem hasReverseAxisCompiler_affinePlane_joint (a r s : ℕ)
    (ha : 1 ≤ a) (hr : r ≤ a * 4 ^ a) :
    HasReverseAxisCompiler r s (3 * 4 ^ a + 4) := by
  classical
  let F := BinaryGaloisField a
  have hcard : Fintype.card F = 2 ^ a := binaryGaloisField_card ha
  intro table
  obtain ⟨row, decode, memory, hmemory⟩ := exists_affinePlane_encoding F hcard hr table
  let δ : ℝ := 1 / (4 * (((r + s : ℕ) : ℝ) + 1))
  have hn : (0 : ℝ) ≤ ((r + s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (4 * (((r + s : ℕ) : ℝ) + 1)) = 1 := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hsmall : δ < 1 / 2 := by nlinarith
  have hsize : ((r + s : ℕ) : ℝ) * δ < 1 := by nlinarith
  let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  choose c η hη using fun b : Fin a ↦
    exists_compact_cauchy_grid_decoder (q := Fintype.card F) hδ hsmall
      (fun z ↦ outputSign (decode (e.symm z) b))
  let pole : F → ℝ := fun z ↦ compactCauchyPole δ (e z)
  let token : F → ℝ := fun z ↦ compactCauchyToken δ (e z)
  have hdecode (b : Fin a) (z : F) :
      c b + (∑ u : F, η b (e u) / (pole u - token z)) =
        outputSign (decode z b) := by
    have hs := e.sum_comp (fun u ↦ η b u /
      (compactCauchyPole δ u - compactCauchyToken δ (e z)))
    dsimp [pole, token]
    rw [hs]
    simpa using hη b (e z)
  obtain ⟨Q, hQ⟩ := exists_affinePlane_reverse_axis_joint δ hδ hsize pole token
    (fun z ↦ compactCauchyPole_bounds hδ (e z))
    (fun z ↦ ⟨compactCauchyToken_pos hδ (e z), compactCauchyToken_lt hδ (e z)⟩)
    (fun i ↦ (row i).1) memory (fun i z ↦ η (row i).2 (e z))
    (fun i ↦ c (row i).2)
  have hN : Fintype.card (F × F) = 4 ^ a := by
    rw [Fintype.card_prod, hcard, ← mul_pow]
    norm_num
  refine ⟨3 * Fintype.card (F × F) + 4, by rw [hN], Q, ?_⟩
  intro i j
  rw [hQ, hdecode, hmemory]
  cases table i j <;> norm_num [outputSign]

end HeadComplexity.AxisZeroGluing
