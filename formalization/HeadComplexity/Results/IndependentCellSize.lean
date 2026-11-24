import HeadComplexity.Results.JointSparseInteractionCapacity

set_option linter.style.header false

/-! An explicit independent-cell size test in the original head model.
The point map is arbitrary and every labeling must be realizable. This is
not a lower bound for compilers that exploit joint interaction among cells. -/

namespace HeadComplexity

open scoped BigOperators

/-- Every labeling of the specified cell extends to a function computed by
at most H original heads. The input encoding is fixed before its labels. -/
def CellShatteredByHeads {I : Type*} (x : I → (Fin n → Bool)) (H : ℕ) : Prop :=
  ∀ f : I → Bool, ∃ F : (Fin n → Bool) → Bool,
    computableWithHeadsN n H F ∧ ∀ i, F (x i) = f i

/-- Faithful finite-cell specialization of the unconditional Warren theorem. -/
theorem cellShatteredByHeads_warren {I : Type*} [Fintype I]
    (x : I → (Fin n → Bool)) {H : ℕ}
    (hcell : CellShatteredByHeads x H)
    (hsize : 1 + 2 * H * (n + 1) ≤ Fintype.card I) :
    (2 : ℝ) ^ Fintype.card I ≤
      (4 * Real.exp 1 * (H + 1) * Fintype.card I /
        (1 + 2 * H * (n + 1))) ^ (1 + 2 * H * (n + 1)) := by
  classical
  let P := fun i : I ↦ countingClearedPoly (H := H) (x i)
  have hfull : strictPolynomialSignPatterns P = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    obtain ⟨F, hF, heq⟩ := hcell f
    obtain ⟨θ, hθ⟩ := mem_strictPatterns_of_computable hF
    refine ⟨θ, fun i ↦ ?_⟩
    have hi := hθ (x i)
    rw [heq i] at hi
    exact hi
  have hK : 0 < Fintype.card (CountingParameter n H) := by
    rw [card_countingParameter]
    omega
  have hKI : Fintype.card (CountingParameter n H) ≤ Fintype.card I := by
    simpa only [card_countingParameter] using hsize
  have hw := strictPolynomialSignPatterns_card_le (by omega : 0 < H + 1)
    hK hKI P (fun i ↦ countingClearedPoly_totalDegree_le (x i))
  rw [hfull, card_countingParameter] at hw
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hw

/-- A cell of M inputs independently compiled with H heads has efficiency
at most 30 n log(8 e M). This permits fully label-adaptive coefficients. -/
theorem cellShatteredByHeads_log_size {I : Type*} [Fintype I]
    (x : I → (Fin n → Bool)) {H : ℕ}
    (hn : 0 < n) (hH : 0 < H) (hHM : H ≤ Fintype.card I)
    (hcell : CellShatteredByHeads x H) :
    (Fintype.card I : ℝ) ≤
      30 * n * H * Real.log (8 * Real.exp 1 * Fintype.card I) := by
  let M := Fintype.card I
  let P := 1 + 2 * H * (n + 1)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast (lt_of_lt_of_le hH hHM)
  have hPr : (P : ℝ) ≤ 5 * n * H := by
    dsimp [P]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hnr (show (0 : ℝ) ≤ H by positivity)]
  have hlog : 1 ≤ Real.log (8 * Real.exp 1 * M) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    nlinarith [Real.exp_pos 1]
  by_cases hPM : P ≤ M
  · have hw := cellShatteredByHeads_warren x hcell hPM
    have hb := warren_capacity_log_budget (by dsimp [P]; omega : 0 < P)
      hPM (by omega : 0 < H + 1) (by simpa [P, M] using hw)
    have hl : Real.log (4 * Real.exp 1 * ((H + 1 : ℕ) : ℝ)) ≤
        Real.log (8 * Real.exp 1 * M) := by
      apply Real.log_le_log (by positivity)
      have hh : (H : ℝ) ≤ M := by exact_mod_cast hHM
      push_cast
      nlinarith [Real.exp_pos 1]
    calc
      (Fintype.card I : ℝ) ≤ 6 * P * Real.log (4 * Real.exp 1 * ((H + 1 : ℕ) : ℝ)) := hb
      _ ≤ 6 * P * Real.log (8 * Real.exp 1 * M) := by gcongr
      _ ≤ 30 * n * H * Real.log (8 * Real.exp 1 * M) := by
        have hh := mul_le_mul_of_nonneg_right hPr
          (show 0 ≤ Real.log (8 * Real.exp 1 * M) by linarith)
        nlinarith
  · have hMP : (M : ℝ) ≤ P := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hPM))
    have hp0 : (0 : ℝ) ≤ P := by positivity
    have hh := mul_le_mul_of_nonneg_left hlog hp0
    have hh' := mul_le_mul_of_nonneg_right hPr (show 0 ≤ Real.log (8 * Real.exp 1 * M) by linarith)
    dsimp [M] at hMP hh hh'
    nlinarith

/-- A gain G over the linear n-inputs-per-head scale requires a cell with
at least exp(G/60) inputs once G >= 60 log(8e). For G=n^delta this is the
explicit exponential size test; for G=log(n)g(n) it is superpolynomial. -/
theorem cellShatteredByHeads_exponential_size {I : Type*} [Fintype I]
    (x : I → (Fin n → Bool)) {H : ℕ} {G : ℝ}
    (hn : 0 < n) (hH : 0 < H) (hHM : H ≤ Fintype.card I)
    (hcell : CellShatteredByHeads x H)
    (hgain : (n : ℝ) * H * G ≤ Fintype.card I)
    (hG : 60 * Real.log (8 * Real.exp 1) ≤ G) :
    Real.exp (G / 60) ≤ Fintype.card I := by
  have hb := cellShatteredByHeads_log_size x hn hH hHM hcell
  have hnH : (0 : ℝ) < (n : ℝ) * H := by positivity
  have hm : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast (lt_of_lt_of_le hH hHM)
  have hg : G ≤ 30 * Real.log (8 * Real.exp 1 * Fintype.card I) := by
    apply (mul_le_mul_iff_left₀ hnH).mp
    nlinarith
  rw [Real.log_mul (by positivity : (8 : ℝ) * Real.exp 1 ≠ 0) hm.ne'] at hg
  have hlog : G / 60 ≤ Real.log (Fintype.card I) := by linarith
  simpa only [Real.exp_log hm] using Real.exp_le_exp.mpr hlog

/-- Even overlapping independently compiled cells cannot cover more than
30 n log(8 e L) inputs per summed head when every cell has size at most L.
The cover hypothesis explicitly charges overlaps rather than assuming a partition. -/
theorem independentCellFamily_budget {J : Type*} [Fintype J]
    (M H : J → ℕ) (x : (j : J) → Fin (M j) → (Fin n → Bool))
    (hn : 0 < n) (hH : ∀ j, 0 < H j) (hHM : ∀ j, H j ≤ M j)
    (hcell : ∀ j, CellShatteredByHeads (x j) (H j))
    {L : ℝ} (hML : ∀ j, (M j : ℝ) ≤ L)
    (hcover : (2 : ℝ) ^ n ≤ ∑ j, (M j : ℝ)) :
    (2 : ℝ) ^ n ≤ 30 * n * (∑ j, (H j : ℝ)) * Real.log (8 * Real.exp 1 * L) := by
  have hb (j : J) : (M j : ℝ) ≤
      30 * n * H j * Real.log (8 * Real.exp 1 * L) := by
    have hj := cellShatteredByHeads_log_size (x j) hn (hH j)
      (by simpa using hHM j) (hcell j)
    simp only [Fintype.card_fin] at hj
    have hm : (0 : ℝ) < M j := by
      exact_mod_cast (lt_of_lt_of_le (hH j) (hHM j))
    have hl : Real.log (8 * Real.exp 1 * M j) ≤
        Real.log (8 * Real.exp 1 * L) := by
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left (hML j) (by positivity)
    exact hj.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  calc
    (2 : ℝ) ^ n ≤ ∑ j, (M j : ℝ) := hcover
    _ ≤ ∑ j, 30 * n * H j * Real.log (8 * Real.exp 1 * L) :=
      Finset.sum_le_sum (fun j _ ↦ hb j)
    _ = 30 * n * (∑ j, (H j : ℝ)) * Real.log (8 * Real.exp 1 * L) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

end HeadComplexity
