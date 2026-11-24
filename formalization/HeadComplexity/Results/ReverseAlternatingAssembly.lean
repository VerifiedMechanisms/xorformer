import HeadComplexity.Results.ReverseAxisRestriction

set_option linter.style.header false

/-! Exact finite assembly by alternating balanced rectangles. The decoder
premises remain explicit; this file does not assert a sublinear decoder. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private theorem exists_finset_embedding {n m : ℕ} (V : Finset (Fin n))
    (hV : V.card = m) :
    ∃ e : Fin m ↪ Fin n, ∀ j, (∃ i, e i = j) ↔ j ∈ V := by
  classical
  let e : Fin m ≃ V := (finCongr hV.symm).trans V.equivFin.symm
  let f : Fin m ↪ Fin n := ⟨fun i ↦ (e i).val,
    fun i j h ↦ e.injective (Subtype.ext h)⟩
  refine ⟨f, ?_⟩
  intro j
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hj
    refine ⟨e.symm ⟨j, hj⟩, ?_⟩
    change (e (e.symm ⟨j, hj⟩)).val = j
    rw [e.apply_symm_apply]

/-- The exact dyadic budget. Each original batch pays its masking factor once. -/
def alternatingDenseBudget (M : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 12 * M 1 1 + 21
  | k + 1 => (12 * M (2 ^ (k + 1)) (2 ^ (k + 1)) + 21) +
      (12 * M (2 ^ k) (2 ^ (k + 1)) + 21) + alternatingDenseBudget M k

/-- Balanced half-dense families on squares and aspect-two rectangles suffice
for an exact axis-zero compiler on every embedded dyadic square. Overlapping
good batches add nonnegative signed scores, preserving all earlier strict signs. -/
theorem exists_alternating_dense_square_patch
    (M : ℕ → ℕ → ℕ)
    (hsquare : ∀ k, HasHalfDenseReverseGridFamily (2 ^ k) (2 ^ k)
      (M (2 ^ k) (2 ^ k)))
    (hrect : ∀ k, HasHalfDenseReverseGridFamily (2 ^ k) (2 ^ (k + 1))
      (M (2 ^ k) (2 ^ (k + 1))))
    (k R S : ℕ) (u : Fin (2 ^ k) ↪ Fin R) (v : Fin (2 ^ k) ↪ Fin S)
    (table : Fin (2 ^ k) → Fin (2 ^ k) → Bool) :
    ∃ H ≤ alternatingDenseBudget M k, ∃ Q : ReverseAxisData R S H,
      (∀ i j, 0 < outputSign (table i j) * Q.score (localGrid (u i) (v j))) ∧
      (∀ i j, ((∀ a, u a ≠ i) ∨ (∀ b, v b ≠ j)) →
        Q.score (localGrid i j) = 0) := by
  classical
  induction k generalizing R S with
  | zero =>
    obtain ⟨U, hU, H, hH, Q, hQ, _, hzero⟩ :=
      exists_half_dense_reverse_rectangle_batch u v (hsquare 0) table
    have hUempty : U = ∅ := Finset.card_eq_zero.mp (by simpa using (show U.card = 0 by
      norm_num at hU
      omega))
    refine ⟨H, hH, Q, ?_, hzero⟩
    intro i j
    exact hQ i j (by simp [hUempty])
  | succ k ih =>
    obtain ⟨U, hU, H₁, hH₁, Q₁, hQ₁, hz₁, hout₁⟩ :=
      exists_half_dense_reverse_rectangle_batch u v (hsquare (k + 1)) table
    have hhalf : U.card ≤ 2 ^ k := by
      have hp : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      omega
    have hsize : 2 ^ k ≤ Fintype.card (Fin (2 ^ (k + 1))) := by
      simp only [Fintype.card_fin, pow_succ]
      omega
    obtain ⟨V, hUV, _, hV⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ U) hhalf (by simpa using hsize)
    obtain ⟨ev, hev⟩ := exists_finset_embedding V hV
    let vt : Fin (2 ^ k) ↪ Fin S := ev.trans v
    let table₂ : Fin (2 ^ k) → Fin (2 ^ (k + 1)) → Bool :=
      fun j i ↦ table i (ev j)
    obtain ⟨T, hT, H₂, hH₂, Q₂, hQ₂, hz₂, hout₂⟩ :=
      exists_half_dense_reverse_rectangle_batch vt u (hrect k) table₂
    have hThalf : T.card ≤ 2 ^ k := by
      have hp : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      omega
    obtain ⟨W, hTW, _, hW⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ T) hThalf (by simpa using hsize)
    obtain ⟨eu, heu⟩ := exists_finset_embedding W hW
    let ut : Fin (2 ^ k) ↪ Fin R := eu.trans u
    obtain ⟨H₃, hH₃, Q₃, hQ₃, hout₃⟩ :=
      ih R S ut vt (fun i j ↦ table (eu i) (ev j))
    have hn₁ (i j) : 0 ≤ outputSign (table i j) *
        Q₁.score (localGrid (u i) (v j)) := by
      by_cases hj : j ∈ U
      · rw [hz₁ i j hj, mul_zero]
      · exact le_of_lt (hQ₁ i j hj)
    have hn₂ (i j) : 0 ≤ outputSign (table i (ev j)) *
        Q₂.score (localGrid (v (ev j)) (u i)) := by
      by_cases hi : i ∈ T
      · rw [show Q₂.score (localGrid (v (ev j)) (u i)) = 0 from hz₂ j i hi,
          mul_zero]
      · exact le_of_lt (hQ₂ j i hi)
    refine ⟨H₁ + H₂ + H₃, ?_, (Q₁.append Q₂.transpose).append Q₃, ?_, ?_⟩
    · simp only [alternatingDenseBudget]
      omega
    · intro i j
      simp only [ReverseAxisData.append_score, mul_add]
      rw [Q₂.transpose_grid]
      by_cases hj : j ∈ V
      · obtain ⟨j', rfl⟩ := (hev j).mpr hj
        by_cases hi : i ∈ W
        · obtain ⟨i', rfl⟩ := (heu i).mpr hi
          have hp := hQ₃ i' j'
          have ha := hn₁ (eu i') (ev j')
          have hb := hn₂ (eu i') j'
          change 0 < outputSign (table (eu i') (ev j')) *
            Q₃.score (localGrid (u (eu i')) (v (ev j'))) at hp
          linarith
        · have hp := hQ₂ j' i (fun hiT ↦ hi (hTW hiT))
          have hz : Q₃.score (localGrid (u i) (v (ev j'))) = 0 := by
            apply hout₃
            left
            intro a h
            apply hi
            apply (heu i).mp
            exact ⟨a, u.injective h⟩
          rw [hz, mul_zero, add_zero]
          have ha := hn₁ i (ev j')
          change 0 < outputSign (table i (ev j')) *
            Q₂.score (localGrid (v (ev j')) (u i)) at hp
          linarith
      · have hp := hQ₁ i j (fun hjU ↦ hj (hUV hjU))
        have hz2 : Q₂.score (localGrid (v j) (u i)) = 0 := by
          apply hout₂
          left
          intro a h
          apply hj
          apply (hev j).mp
          exact ⟨a, v.injective h⟩
        have hz3 : Q₃.score (localGrid (u i) (v j)) = 0 := by
          apply hout₃
          right
          intro a h
          apply hj
          apply (hev j).mp
          exact ⟨a, v.injective h⟩
        simpa [hz2, hz3] using hp
    · intro i j hij
      simp only [ReverseAxisData.append_score]
      rw [Q₂.transpose_grid, hout₁ i j hij]
      have hz2 : Q₂.score (localGrid j i) = 0 := by
        apply hout₂
        rcases hij with hi | hj
        · exact Or.inr hi
        · exact Or.inl (fun a ↦ hj (ev a))
      have hz3 : Q₃.score (localGrid i j) = 0 := by
        apply hout₃
        rcases hij with hi | hj
        · exact Or.inl (fun a ↦ hi (eu a))
        · exact Or.inr (fun a ↦ hj (ev a))
      simp [hz2, hz3]

/-- The alternating construction is a genuine compiler once the explicit
half-dense decoder premises have been supplied. -/
theorem hasReverseAxisCompiler_of_alternating_half_dense
    (M : ℕ → ℕ → ℕ)
    (hsquare : ∀ k, HasHalfDenseReverseGridFamily (2 ^ k) (2 ^ k)
      (M (2 ^ k) (2 ^ k)))
    (hrect : ∀ k, HasHalfDenseReverseGridFamily (2 ^ k) (2 ^ (k + 1))
      (M (2 ^ k) (2 ^ (k + 1))))
    (k : ℕ) : HasReverseAxisCompiler (2 ^ k) (2 ^ k)
      (alternatingDenseBudget M k) := by
  intro table
  obtain ⟨H, hH, Q, hQ, _⟩ := exists_alternating_dense_square_patch M
    hsquare hrect k (2 ^ k) (2 ^ k) (Function.Embedding.refl _)
      (Function.Embedding.refl _) table
  exact ⟨H, hH, Q, hQ⟩

/-- Padding arbitrary rectangles to a dyadic square costs no additional heads. -/
theorem hasReverseAxisCompiler_of_alternating_half_dense_le
    (M : ℕ → ℕ → ℕ)
    (hsquare : ∀ k, HasHalfDenseReverseGridFamily (2 ^ k) (2 ^ k)
      (M (2 ^ k) (2 ^ k)))
    (hrect : ∀ k, HasHalfDenseReverseGridFamily (2 ^ k) (2 ^ (k + 1))
      (M (2 ^ k) (2 ^ (k + 1))))
    {r s k : ℕ} (hr : r ≤ 2 ^ k) (hs : s ≤ 2 ^ k) :
    HasReverseAxisCompiler r s (alternatingDenseBudget M k) :=
  (hasReverseAxisCompiler_of_alternating_half_dense M hsquare hrect k).restrict
    (Fin.castLEEmb hr) (Fin.castLEEmb hs)

/-- A logarithmic dyadic batch rate survives the complete alternating sum.
The assumptions bound each already masked batch, including its additive cost. -/
theorem alternatingDenseBudget_le
    (M : ℕ → ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsquare : ∀ k : ℕ, (12 * M (2 ^ k) (2 ^ k) + 21 : ℝ) ≤
      C * (2 : ℝ) ^ k / (k + 2))
    (hrect : ∀ k : ℕ, (12 * M (2 ^ k) (2 ^ (k + 1)) + 21 : ℝ) ≤
      C * (2 : ℝ) ^ k / (k + 2))
    (k : ℕ) : (alternatingDenseBudget M k : ℝ) ≤
      8 * C * (2 : ℝ) ^ k / (k + 2) := by
  induction k with
  | zero =>
    have h := hsquare 0
    norm_num [alternatingDenseBudget] at h ⊢
    linarith
  | succ k ih =>
    have ha := hsquare (k + 1)
    have hb := hrect k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hp : 0 ≤ C * (2 : ℝ) ^ k := mul_nonneg hC (by positivity)
    have hsum : (alternatingDenseBudget M (k + 1) : ℝ) ≤
        C * (2 : ℝ) ^ (k + 1) / (↑(k + 1) + 2) +
        C * (2 : ℝ) ^ k / (k + 2) + 8 * C * (2 : ℝ) ^ k / (k + 2) := by
      simp only [alternatingDenseBudget, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      simpa only [Nat.cast_add, Nat.cast_one] using add_le_add (add_le_add ha hb) ih
    apply hsum.trans
    push_cast
    rw [pow_succ]
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hk3 : (0 : ℝ) < k + 1 + 2 := by positivity
    apply (le_div_iff₀ hk3).2
    field_simp
    nlinarith [mul_nonneg hp hk]

end HeadComplexity.AxisZeroGluing
