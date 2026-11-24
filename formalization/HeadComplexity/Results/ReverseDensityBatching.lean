import HeadComplexity.Results.ReverseRowFlip
import HeadComplexity.Results.ReverseCauchyBiasAssembly

set_option linter.style.header false

/-! Constant-density local families can be assembled in disjoint batches.
The density premise is explicit; no sublinear compiler is assumed proved. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- Averaging a common row sign leaves at most half of any set of columns
outside a family containing at least half of all row patterns. -/
theorem exists_row_sign_half_remainder {r s : ℕ}
    (good : Finset (Fin r → Bool)) (table : Fin r → Fin s → Bool)
    (active : Finset (Fin s)) (hdense : 2 ^ r ≤ 2 * good.card) :
    ∃ sign : Fin r → Bool,
      2 * (active.filter (fun j ↦
        rowSignTranslate (fun i ↦ table i j) sign ∉ good)).card ≤ active.card := by
  classical
  let E : Fin s → ((Fin r → Bool) ≃ (Fin r → Bool)) := fun j ↦
    { toFun := rowSignTranslate (fun i ↦ table i j)
      invFun := rowSignTranslate (fun i ↦ table i j)
      left_inv := by
        intro x
        funext i
        cases h : table i j <;> simp [rowSignTranslate, h]
      right_inv := by
        intro x
        funext i
        cases h : table i j <;> simp [rowSignTranslate, h] }
  have hcolumn (j : Fin s) :
      (∑ sign : Fin r → Bool,
        if rowSignTranslate (fun i ↦ table i j) sign ∉ good then 1 else 0) =
        2 ^ r - good.card := by
    have he := (E j).sum_comp (fun x ↦ if x ∉ good then (1 : ℕ) else 0)
    have hc : (Finset.univ \ good).card = 2 ^ r - good.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ good)]
      simp
    rw [← hc]
    convert he using 1
    rw [Finset.card_eq_sum_ones]
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  let bad : (Fin r → Bool) → ℕ := fun sign ↦
    (active.filter (fun j ↦ rowSignTranslate (fun i ↦ table i j) sign ∉ good)).card
  have hsum : (∑ sign, bad sign) = active.card * (2 ^ r - good.card) := by
    simp only [bad, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [hcolumn, Finset.sum_const, smul_eq_mul]
    simp
  have hcard : good.card ≤ 2 ^ r := by
    simpa using Finset.card_le_card (Finset.subset_univ good)
  have hsmall : 2 * (2 ^ r - good.card) ≤ 2 ^ r := by omega
  by_contra hn
  push Not at hn
  have hlt : (∑ _sign : Fin r → Bool, active.card) < ∑ sign, 2 * bad sign := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro sign _
    exact hn sign
  rw [← Finset.mul_sum, hsum] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at hlt
  have hle := Nat.mul_le_mul_left active.card hsmall
  nlinarith

/-- Joint universality on a family occupying at least half of the pattern
cube. Denominators retain full-cube positivity, even for repeated columns. -/
def HasHalfDenseReverseGridFamily (r s M : ℕ) : Prop :=
  ∃ good : Finset (Fin r → Bool), 2 ^ r ≤ 2 * good.card ∧
    ∀ table : Fin r → Fin s → Bool, (∀ j, (fun i ↦ table i j) ∈ good) →
      ∃ H ≤ M, ∃ L : StrictReverseGridData r s H,
        ∀ i j, 0 < outputSign (table i j) * L.score (localGrid i j)

private theorem exists_axis_good_batch {r s M : ℕ}
    (good : Finset (Fin r → Bool)) (hne : good.Nonempty)
    (hgood : ∀ table : Fin r → Fin s → Bool, (∀ j, (fun i ↦ table i j) ∈ good) →
      ∃ H ≤ M, ∃ L : StrictReverseGridData r s H,
        ∀ i j, 0 < outputSign (table i j) * L.score (localGrid i j))
    (table : Fin r → Fin s → Bool) (sign : Fin r → Bool)
    (C : Finset (Fin s))
    (hC : ∀ j ∈ C, rowSignTranslate (fun i ↦ table i j) sign ∈ good) :
    ∃ H ≤ 12 * M + 21, ∃ L : ReverseAxisData r s H,
      (∀ i j, j ∈ C → 0 < outputSign (table i j) * L.score (localGrid i j)) ∧
      (∀ i j, j ∉ C → L.score (localGrid i j) = 0) := by
  classical
  obtain ⟨v, hv⟩ := hne
  let table' : Fin r → Fin s → Bool := fun i j ↦
    if j ∈ C then rowSignTranslate (fun k ↦ table k j) sign i else v i
  have ht : ∀ j, (fun i ↦ table' i j) ∈ good := by
    intro j
    by_cases hj : j ∈ C
    · simpa [table', hj] using hC j hj
    · simpa [table', hj] using hv
  obtain ⟨H, hH, L, hL⟩ := hgood table' ht
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_row_flip_column_mask L sign
    (fun j ↦ decide (j ∈ C))
  obtain ⟨R, hR⟩ := exists_reverse_axis_repair Q
  refine ⟨3 * (4 * H + 6) + 3, by omega, R, ?_, ?_⟩
  · intro i j hj
    rw [hR, hQ]
    have h := hL i j
    cases hs : sign i <;> cases ht : table i j <;>
      simpa [table', rowSignTranslate, outputSign, hj, hs, ht] using h
  · intro i j hj
    rw [hR, hQ]
    simp [hj]

private noncomputable def emptyAxisData (r s : ℕ) : ReverseAxisData r s 0 where
  a₀ := Fin.elim0
  b₀ := Fin.elim0
  a := Fin.elim0
  b := Fin.elim0
  positive := fun h ↦ Fin.elim0 h
  negative := fun h ↦ Fin.elim0 h
  zero_left := by simp
  zero_right := by simp

/-- After t disjoint batches the exact residual column count is at most
s / 2^t. Previously obtained strict signs are preserved by exact masking. -/
theorem exists_half_dense_reverse_batches {r s M : ℕ}
    (hdense : HasHalfDenseReverseGridFamily r s M)
    (table : Fin r → Fin s → Bool) (t : ℕ) :
    ∃ U : Finset (Fin s), 2 ^ t * U.card ≤ s ∧
      ∃ H ≤ t * (12 * M + 21), ∃ L : ReverseAxisData r s H,
        (∀ i j, j ∉ U → 0 < outputSign (table i j) * L.score (localGrid i j)) ∧
        (∀ i j, j ∈ U → L.score (localGrid i j) = 0) := by
  classical
  obtain ⟨good, hcard, hgood⟩ := hdense
  have hne : good.Nonempty := by
    apply Finset.card_pos.mp
    have hpow : 0 < 2 ^ r := by positivity
    omega
  induction t with
  | zero =>
    refine ⟨Finset.univ, by simp, 0, by simp, emptyAxisData r s, ?_, ?_⟩
    · simp
    · intro i j _
      simp [ReverseAxisData.score]
  | succ t ih =>
    obtain ⟨U, hU, H, hH, L, hL, hzero⟩ := ih
    obtain ⟨sign, hsign⟩ := exists_row_sign_half_remainder good table U hcard
    let V := U.filter (fun j ↦ rowSignTranslate (fun i ↦ table i j) sign ∉ good)
    let C := U \ V
    have hVU : V ⊆ U := Finset.filter_subset _ _
    have hC : ∀ j ∈ C, rowSignTranslate (fun i ↦ table i j) sign ∈ good := by
      intro j hj
      have h := Finset.mem_sdiff.mp hj
      simpa [V, h.1] using h.2
    obtain ⟨G, hG, R, hR, hRzero⟩ :=
      exists_axis_good_batch good hne hgood table sign C hC
    refine ⟨V, ?_, H + G, ?_, L.append R, ?_, ?_⟩
    · have h := Nat.mul_le_mul_left (2 ^ t) hsign
      change 2 ^ t * (2 * V.card) ≤ 2 ^ t * U.card at h
      rw [pow_succ]
      nlinarith
    · nlinarith
    · intro i j hj
      rw [ReverseAxisData.append_score]
      by_cases hjU : j ∈ U
      · have hjC : j ∈ C := Finset.mem_sdiff.mpr ⟨hjU, hj⟩
        rw [hzero i j hjU, zero_add]
        exact hR i j hjC
      · have hjC : j ∉ C := fun h ↦ hjU (Finset.mem_sdiff.mp h).1
        rw [hRzero i j hjC, add_zero]
        exact hL i j hjU
    · intro i j hj
      rw [ReverseAxisData.append_score, hzero i j (hVU hj)]
      have hjC : j ∉ C := fun h ↦ (Finset.mem_sdiff.mp h).2 hj
      rw [hRzero i j hjC]
      simp

/-- An arbitrary real matrix supported on U has an exact axis-zero
realization with at most three heads per surviving column plus six. -/
theorem exists_reverse_axis_column_remainder {r s : ℕ}
    (value : Fin r → Fin s → ℝ) (U : Finset (Fin s)) :
    ∃ L : ReverseAxisData r s (3 * (U.card + 1) + 3), ∀ i j,
      L.score (localGrid i j) = if j ∈ U then value i j else 0 := by
  classical
  let e : Fin U.card ≃ U := U.equivFin.symm
  obtain ⟨L, hL⟩ := exists_reverse_axis_rank_grid
    (fun h i ↦ value i (e h))
    (fun h j ↦ if (e h).val = j then 1 else 0)
    (fun _ ↦ 0) (fun _ ↦ 0) 0
  refine ⟨L, ?_⟩
  intro i j
  rw [hL]
  simp only [zero_add]
  by_cases hj : j ∈ U
  · rw [ite_eq_left hj]
    let h : Fin U.card := e.symm ⟨j, hj⟩
    have heq : e h = ⟨j, hj⟩ := e.apply_symm_apply _
    rw [Finset.sum_eq_single h]
    · simp [heq]
    · intro k _ hk
      have hkj : (e k).val ≠ j := by
        intro hh
        have hek : e k = e h := by rw [heq]; exact Subtype.ext hh
        exact hk (e.injective hek)
      simp [hkj]
    · simp
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k _
    have hkj : (e k).val ≠ j := by
      intro hh
      exact hj (hh ▸ (e k).property)
    simp [hkj]

/-- Half-density joint decoding, repeated in disjoint column batches and
completed by a rank correction, gives a universal strict axis-zero compiler.
Its exact budget is t(12M+21)+3R+6 whenever s ≤ 2^t R. -/
theorem hasReverseAxisCompiler_of_half_dense_family {r s M t R : ℕ}
    (hdense : HasHalfDenseReverseGridFamily r s M)
    (hcover : s ≤ 2 ^ t * R) :
    HasReverseAxisCompiler r s (t * (12 * M + 21) + 3 * R + 6) := by
  intro table
  obtain ⟨U, hU, H, hH, L, hL, hzero⟩ :=
    exists_half_dense_reverse_batches hdense table t
  have hUR : U.card ≤ R := by
    have hp : 0 < 2 ^ t := by positivity
    exact Nat.le_of_mul_le_mul_left (hU.trans hcover) hp
  obtain ⟨Q, hQ⟩ := exists_reverse_axis_column_remainder
    (fun i j ↦ outputSign (table i j)) U
  refine ⟨H + (3 * (U.card + 1) + 3), by omega, L.append Q, ?_⟩
  intro i j
  rw [ReverseAxisData.append_score, hQ]
  by_cases hj : j ∈ U
  · rw [ite_eq_left hj, hzero i j hj, zero_add]
    cases table i j <;> norm_num [outputSign]
  · rw [ite_eq_right hj, add_zero]
    exact hL i j hj

end HeadComplexity.AxisZeroGluing
