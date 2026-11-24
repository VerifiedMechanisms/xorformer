import HeadComplexity.Results.ReverseDensityBatching

set_option linter.style.header false

/-! Grid modules may be embedded into larger rectangles and masked once.
The ambient full-cube denominator condition is preserved. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private theorem transpose_affine {r s : ℕ} (c : ℝ) (a : Fin (r + s) → ℝ)
    (bits : Fin (s + r) → Bool) :
    affineValue c (fun k ↦ a (finAddFlip k)) bits =
      affineValue c a (fun k ↦ bits (finAddFlip k)) := by
  simp [affineValue, Fin.sum_univ_add, add_comm]

/-- Transposition costs no heads and preserves exact zeros on both axes. -/
noncomputable def ReverseAxisData.transpose {r s H : ℕ}
    (L : ReverseAxisData r s H) : ReverseAxisData s r H where
  a₀ := L.a₀
  b₀ := L.b₀
  a := fun h k ↦ L.a h (finAddFlip k)
  b := fun h k ↦ L.b h (finAddFlip k)
  positive := by
    intro h bits
    rw [transpose_affine]
    exact L.positive h _
  negative := fun h k ↦ L.negative h (finAddFlip k)
  zero_left := by
    intro w
    simp only [transpose_affine]
    convert L.zero_right w using 1
    congr 1
    funext h
    congr 1 <;> congr 1 <;> funext k <;>
      refine Fin.addCases ?_ ?_ k <;> intro i <;> simp
  zero_right := by
    intro z
    simp only [transpose_affine]
    convert L.zero_left z using 1
    congr 1
    funext h
    congr 1 <;> congr 1 <;> funext k <;>
      refine Fin.addCases ?_ ?_ k <;> intro i <;> simp

theorem ReverseAxisData.transpose_grid {r s H : ℕ}
    (L : ReverseAxisData r s H) (i : Fin r) (j : Fin s) :
    L.transpose.score (localGrid j i) = L.score (localGrid i j) := by
  have hb : (fun k ↦ localGrid j i (finAddFlip k)) = localGrid i j := by
    funext k
    refine Fin.addCases ?_ ?_ k <;> intro l <;> simp [localGrid]
  simp only [ReverseAxisData.score, ReverseAxisData.transpose, transpose_affine, hb]

private noncomputable def extendSlope {n m : ℕ} (e : Fin n ↪ Fin m)
    (a : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i, if e i = j then a i else 0

private theorem extendSlope_eval {n m : ℕ} (e : Fin n ↪ Fin m)
    (a : Fin n → ℝ) (c : ℝ) (bits : Fin m → Bool) :
    affineValue c (extendSlope e a) bits = affineValue c a (bits ∘ e) := by
  classical
  simp only [affineValue, extendSlope, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

private noncomputable def extendReverseRatio {n m : ℕ} (e : Fin n ↪ Fin m)
    (A : StrictReverseRatio n) : WeakReverseRatio m where
  a₀ := A.a₀
  b₀ := A.b₀
  a := extendSlope e A.a
  b := extendSlope e A.b
  nonpositive := by
    intro j
    apply Finset.sum_nonpos
    intro i _
    split <;> simp_all [le_of_lt (A.negative i)]
  positive := by
    intro bits
    rw [extendSlope_eval]
    exact A.positive _

private theorem extendReverseRatio_eval {n m : ℕ} (e : Fin n ↪ Fin m)
    (A : StrictReverseRatio n) (bits : Fin m → Bool) :
    (extendReverseRatio e A).value bits = A.value (bits ∘ e) := by
  simp only [WeakReverseRatio.value, extendReverseRatio, StrictReverseRatio.value,
    extendSlope_eval]

private def gridEmbedding {r s R S : ℕ} (u : Fin r ↪ Fin R)
    (v : Fin s ↪ Fin S) : Fin (r + s) ↪ Fin (R + S) where
  toFun := Fin.addCases (fun i ↦ Fin.castAdd S (u i)) (fun j ↦ Fin.natAdd R (v j))
  inj' := by
    intro x
    refine Fin.addCases ?_ ?_ x <;> intro i y
    · refine Fin.addCases ?_ ?_ y <;> intro j h
      · simp only [Fin.addCases_left, Fin.castAdd_inj] at h
        exact congrArg (Fin.castAdd s) (u.injective h)
      · simp only [Fin.addCases_left, Fin.addCases_right] at h
        have hv := congrArg Fin.val h
        have hi := (u i).isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    · refine Fin.addCases ?_ ?_ y <;> intro j h
      · simp only [Fin.addCases_left, Fin.addCases_right] at h
        have hv := congrArg Fin.val h
        have hj := (u j).isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · simp only [Fin.addCases_right, Fin.natAdd_inj] at h
        exact congrArg (Fin.natAdd r) (v.injective h)

private theorem gridEmbedding_grid {r s R S : ℕ} (u : Fin r ↪ Fin R)
    (v : Fin s ↪ Fin S) (i : Fin r) (j : Fin s) :
    localGrid (u i) (v j) ∘ gridEmbedding u v = localGrid i j := by
  funext k
  refine Fin.addCases ?_ ?_ k <;> intro l
  · have hm : gridEmbedding u v (Fin.castAdd s l) = Fin.castAdd S (u l) := by
      change Fin.addCases (fun i ↦ Fin.castAdd S (u i))
        (fun j ↦ Fin.natAdd R (v j)) (Fin.castAdd s l) = Fin.castAdd S (u l)
      rw [Fin.addCases_left]
    rw [Function.comp_apply, hm]
    simp [localGrid, u.injective.eq_iff]
  · have hm : gridEmbedding u v (Fin.natAdd r l) = Fin.natAdd R (v l) := by
      change Fin.addCases (fun i ↦ Fin.castAdd S (u i))
        (fun j ↦ Fin.natAdd R (v j)) (Fin.natAdd r l) = Fin.natAdd R (v l)
      rw [Fin.addCases_right]
    rw [Function.comp_apply, hm]
    simp [localGrid, v.injective.eq_iff]

/-- An arbitrary subrectangle module extends to the ambient cube at the same
head count. Strictification does not change any ambient two-hot grid value. -/
theorem exists_strict_reverse_grid_embedding {r s R S H : ℕ}
    (u : Fin r ↪ Fin R) (v : Fin s ↪ Fin S)
    (L : StrictReverseGridData r s H) :
    ∃ Q : StrictReverseGridData R S H, ∀ i j,
      Q.score (localGrid (u i) (v j)) = L.score (localGrid i j) := by
  let E : WeakReverseGridData R S H :=
    { bias := L.bias, head := fun h ↦ extendReverseRatio (gridEmbedding u v) (L.head h) }
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_grid_of_weak E
  refine ⟨Q, ?_⟩
  intro i j
  rw [hQ]
  simp only [WeakReverseGridData.score, E, extendReverseRatio_eval, gridEmbedding_grid,
    StrictReverseGridData.score]

/-- A subrectangle can be embedded, given row multipliers, and masked on both
sides for a single constant-factor cost. This operation is applied separately
to each batch, so its factor does not compound with the number of batches. -/
theorem exists_reverse_axis_grid_patch {r s R S H : ℕ}
    (u : Fin r ↪ Fin R) (v : Fin s ↪ Fin S)
    (L : StrictReverseGridData r s H) (coeff : Fin r → ℝ)
    (hc : ∀ i, coeff i = -1 ∨ coeff i = 0 ∨ coeff i = 1)
    (active : Fin s → Bool) :
    ∃ Q : ReverseAxisData R S (12 * H + 21),
      (∀ i j, Q.score (localGrid (u i) (v j)) =
        (if active j then 1 else 0) * coeff i * L.score (localGrid i j)) ∧
      (∀ i j, ((∀ k, u k ≠ i) ∨ (∀ k, active k = true → v k ≠ j)) →
        Q.score (localGrid i j) = 0) := by
  classical
  obtain ⟨E, hE⟩ := exists_strict_reverse_grid_embedding u v L
  let row : Fin R → ℝ := extendSlope u coeff
  have hrow (i : Fin r) : row (u i) = coeff i := by
    simp [row, extendSlope, u.injective.eq_iff]
  have hrowzero (i : Fin R) (hi : ∀ k, u k ≠ i) : row i = 0 := by
    simp [row, extendSlope, hi]
  have hrowrange (i : Fin R) : row i = -1 ∨ row i = 0 ∨ row i = 1 := by
    by_cases hi : ∃ k, u k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [hrow]
      exact hc k
    · exact Or.inr (Or.inl (hrowzero i (by simpa using hi)))
  let col : Fin S → ℝ := fun j ↦ if ∃ k, active k = true ∧ v k = j then 1 else 0
  have hcol (j : Fin s) : col (v j) = if active j then 1 else 0 := by
    simp [col, v.injective.eq_iff]
  have hcolzero (j : Fin S) (hj : ∀ k, active k = true → v k ≠ j) : col j = 0 := by
    have hn : ¬ ∃ k, active k = true ∧ v k = j := by
      rintro ⟨k, hk, hkj⟩
      exact hj k hk hkj
    simp [col, hn]
  obtain ⟨F, hF⟩ := exists_strict_reverse_row_multiplier E row hrowrange
  obtain ⟨G, hG⟩ := exists_strict_reverse_column_multiplier F col
    (fun j ↦ by dsimp [col]; split <;> simp)
  obtain ⟨Q, hQ⟩ := exists_reverse_axis_repair G
  have hcount : 3 * (2 * (2 * H + 2) + 2) + 3 = 12 * H + 21 := by omega
  have hresult : ∃ Q : ReverseAxisData R S (3 * (2 * (2 * H + 2) + 2) + 3),
      (∀ i j, Q.score (localGrid (u i) (v j)) =
        (if active j then 1 else 0) * coeff i * L.score (localGrid i j)) ∧
      (∀ i j, ((∀ k, u k ≠ i) ∨ (∀ k, active k = true → v k ≠ j)) →
        Q.score (localGrid i j) = 0) := by
    refine ⟨Q, ?_, ?_⟩
    · intro i j
      rw [hQ, hG, hF, hrow, hcol, hE]
      ring
    · intro i j hij
      rw [hQ, hG, hF]
      rcases hij with hi | hj
      · rw [hrowzero i hi]
        ring
      · rw [hcolzero j hj]
        ring
  rwa [hcount] at hresult

/-- One half-dense decoder batch on any embedded rectangle fixes at least
half its columns and is exactly zero on the remaining rectangle and outside
the embedded rectangle. All output heads have strict reverse slopes. -/
theorem exists_half_dense_reverse_rectangle_batch {r s R S M : ℕ}
    (u : Fin r ↪ Fin R) (v : Fin s ↪ Fin S)
    (hdense : HasHalfDenseReverseGridFamily r s M)
    (table : Fin r → Fin s → Bool) :
    ∃ U : Finset (Fin s), 2 * U.card ≤ s ∧
      ∃ H ≤ 12 * M + 21, ∃ Q : ReverseAxisData R S H,
        (∀ i j, j ∉ U →
          0 < outputSign (table i j) * Q.score (localGrid (u i) (v j))) ∧
        (∀ i j, j ∈ U → Q.score (localGrid (u i) (v j)) = 0) ∧
        (∀ i j, ((∀ k, u k ≠ i) ∨ (∀ k, v k ≠ j)) →
          Q.score (localGrid i j) = 0) := by
  classical
  obtain ⟨good, hd, hgood⟩ := hdense
  have hne : good.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < 2 ^ r := by positivity
    omega
  obtain ⟨fallback, hfallback⟩ := hne
  obtain ⟨sign, hsign⟩ := exists_row_sign_half_remainder good table Finset.univ hd
  let U : Finset (Fin s) := Finset.univ.filter (fun j ↦
    rowSignTranslate (fun i ↦ table i j) sign ∉ good)
  have hU : 2 * U.card ≤ s := by simpa [U] using hsign
  let next : Fin r → Fin s → Bool := fun i j ↦
    if j ∈ U then fallback i else rowSignTranslate (fun k ↦ table k j) sign i
  have hnext : ∀ j, (fun i ↦ next i j) ∈ good := by
    intro j
    by_cases hj : j ∈ U
    · simpa [next, hj] using hfallback
    · have hg : rowSignTranslate (fun i ↦ table i j) sign ∈ good := by
        simpa [U] using hj
      simpa [next, hj] using hg
  obtain ⟨G, hG, L, hL⟩ := hgood next hnext
  obtain ⟨Q, hQ, hQzero⟩ := exists_reverse_axis_grid_patch u v L
    (fun i ↦ outputSign (sign i))
    (fun i ↦ by cases sign i <;> simp [outputSign]) (fun j ↦ decide (j ∉ U))
  refine ⟨U, hU, 12 * G + 21, by omega, Q, ?_, ?_, ?_⟩
  · intro i j hj
    rw [hQ]
    have h := hL i j
    cases hs : sign i <;> cases ht : table i j <;>
      simpa [next, rowSignTranslate, outputSign, hj, hs, ht] using h
  · intro i j hj
    rw [hQ]
    simp [hj]
  · intro i j hij
    apply hQzero
    rcases hij with hi | hj
    · exact Or.inl hi
    · exact Or.inr (fun k _ ↦ hj k)

end HeadComplexity.AxisZeroGluing
