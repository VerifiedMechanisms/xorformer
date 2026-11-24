import HeadComplexity.Results.BernoulliStarCover

set_option linter.style.header false

/-!
Weighted partial covering, with the cost of uncovered targets explicitly
charged. This is a combinatorial helper for a larger local compiler; it does
not assert that such a compiler exists or improve `worstCaseHeadComplexity`.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- Uniform Bernoulli selection with arbitrary positive edge cost and
nonnegative singleton fallback cost. -/
theorem jointCell_exists_weighted_partial_cover
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (neighbors : κ → Finset ι) (d : ℕ)
    (hdegree : ∀ t, (neighbors t).card = d)
    (A B p : ℝ) (hA : 0 < A) (_hB : 0 ≤ B)
    (hp : 0 ≤ p) (hpone : p ≤ 1) :
    ∃ (S : Finset ι) (T : Finset κ),
      (∀ t, t ∉ T → ∃ i ∈ S, i ∈ neighbors t) ∧
      A * S.card + B * T.card ≤
        A * Fintype.card ι * p + B * Fintype.card κ * (1 - p) ^ d := by
  obtain ⟨S, T, hcover, hcost⟩ :=
    FiniteBernoulliCover.exists_patch_card_le neighbors p (B / A) hp hpone
  refine ⟨S, T, hcover, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcost hA.le
  simp_rw [hdegree] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hAne : A ≠ 0 := hA.ne'
  field_simp at h ⊢
  nlinarith

/-- The incidence identity makes the selected-edge cost proportional to the
number of targets even when one edge contains many target inputs. -/
theorem jointCell_exists_regular_weighted_partial_cover
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (neighbors : κ → Finset ι) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e)
    (hdegree : ∀ t, (neighbors t).card = d)
    (hincidence : Fintype.card ι * e = Fintype.card κ * d)
    (K B t : ℝ) (hK : 0 < K) (hB : 0 ≤ B) (ht : 0 ≤ t) :
    ∃ (S : Finset ι) (T : Finset κ),
      (∀ v, v ∉ T → ∃ i ∈ S, i ∈ neighbors v) ∧
      K * e * S.card + B * T.card ≤
        Fintype.card κ * (K * t + B * Real.exp (-t)) := by
  classical
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hiR : (Fintype.card ι : ℝ) * e = (Fintype.card κ : ℝ) * d :=
    by exact_mod_cast hincidence
  by_cases hlarge : (d : ℝ) ≤ t
  · refine ⟨Finset.univ, ∅, ?_, ?_⟩
    · intro v _
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by simpa [hdegree] using hd :
        0 < (neighbors v).card)
      exact ⟨i, Finset.mem_univ i, hi⟩
    · simp only [Finset.card_univ, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
      have hscale := mul_le_mul_of_nonneg_left hlarge hK.le
      have hexp : 0 ≤ B * Real.exp (-t) := mul_nonneg hB (Real.exp_pos _).le
      have h := mul_le_mul_of_nonneg_left (show K * (d : ℝ) ≤
        K * t + B * Real.exp (-t) by linarith) (Nat.cast_nonneg (Fintype.card κ))
      nlinarith [hiR]
  · have hsmall : t < d := lt_of_not_ge hlarge
    let p : ℝ := t / d
    have hp : 0 ≤ p := div_nonneg ht hdR.le
    have hpone : p ≤ 1 := (div_le_one hdR).mpr hsmall.le
    obtain ⟨S, T, hcover, hcost⟩ := jointCell_exists_weighted_partial_cover
      neighbors d hdegree (K * e) B p (mul_pos hK heR) hB hp hpone
    refine ⟨S, T, hcover, hcost.trans ?_⟩
    have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hpone)
      (Real.one_sub_le_exp_neg p) d
    rw [← Real.exp_nat_mul] at hpow
    have hdp : (d : ℝ) * -p = -t := by dsimp [p]; field_simp
    rw [hdp] at hpow
    have hsel : K * e * (Fintype.card ι : ℝ) * p =
        (Fintype.card κ : ℝ) * (K * t) := by
      have hmul := congrArg (fun x : ℝ ↦ K * x * p) hiR
      dsimp [p] at hmul ⊢
      field_simp at hmul ⊢
      nlinarith
    rw [hsel]
    have hscaled := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hB (Nat.cast_nonneg (Fintype.card κ)))
    nlinarith

/-- Exact downward-star incidence identity for the row-layer application. -/
theorem jointCell_downward_layer_incidence (m k c : ℕ) :
    m.choose (k + c) * (k + c).choose c = m.choose k * (m - k).choose c := by
  rw [show (k + c).choose c = (k + c).choose k by
    simpa only [Nat.add_comm] using (Nat.choose_symm_add (a := c) (b := k))]
  simpa only [Nat.add_sub_cancel_left] using
    (Nat.choose_mul (n := m) (k := k + c) (s := k) (Nat.le_add_right k c))

/-- A Hamming layer, represented by its finite set of supports. -/
def JointCellLayer (m k : ℕ) :=
  ↥((Finset.univ : Finset (Fin m)).powersetCard k)

instance (m k : ℕ) : Fintype (JointCellLayer m k) := by
  unfold JointCellLayer
  infer_instance

/-- The possible centers of an exact downward c-star above one row. -/
noncomputable def jointCellLayerNeighbors (m k c : ℕ) (y : JointCellLayer m k) :
    Finset (JointCellLayer m (k + c)) :=
  Finset.univ.filter (fun X ↦ y.val ⊆ X.val)

theorem jointCell_layer_card (m k : ℕ) :
    Fintype.card (JointCellLayer m k) = m.choose k := by
  simp [JointCellLayer, Finset.card_powersetCard]

theorem jointCell_layer_neighbors_card (m k c : ℕ) (y : JointCellLayer m k) :
    (jointCellLayerNeighbors m k c y).card = (m - k).choose c := by
  classical
  have hy : y.val.card = k := (Finset.mem_powersetCard.mp y.property).2
  have hcard : (jointCellLayerNeighbors m k c y).card =
      (((Finset.univ : Finset (Fin m)).powersetCard (k + c)).filter
        (y.val ⊆ ·)).card := by
    apply Finset.card_bij (fun X _ ↦ X.val)
    · intro X hX
      exact Finset.mem_filter.mpr ⟨X.property, (Finset.mem_filter.mp hX).2⟩
    · intro X hX Y hY h
      exact Subtype.ext h
    · intro X hX
      refine ⟨⟨X, (Finset.mem_filter.mp hX).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2⟩
  rw [hcard, Finset.card_filter_powersetCard_subset y.val Finset.univ (k + c)
    (Finset.subset_univ _) (by omega)]
  simp [hy]

/-- Exact row-layer partial-cover budget. Every selected star and every
singleton exception is charged, and no pure-cover density is assumed. -/
theorem jointCell_exists_downward_layer_partial_cover (m k c : ℕ)
    (hkc : k + c ≤ m) (K B t : ℝ) (hK : 0 < K) (hB : 0 ≤ B) (ht : 0 ≤ t) :
    ∃ (S : Finset (JointCellLayer m (k + c))) (T : Finset (JointCellLayer m k)),
      (∀ y, y ∉ T → ∃ X ∈ S, y.val ⊆ X.val) ∧
      K * (k + c).choose c * S.card + B * T.card ≤
        m.choose k * (K * t + B * Real.exp (-t)) := by
  have hd : 0 < (m - k).choose c := Nat.choose_pos (by omega)
  have he : 0 < (k + c).choose c := Nat.choose_pos (by omega)
  have hinc : Fintype.card (JointCellLayer m (k + c)) * (k + c).choose c =
      Fintype.card (JointCellLayer m k) * (m - k).choose c := by
    simp only [jointCell_layer_card]
    exact jointCell_downward_layer_incidence m k c
  obtain ⟨S, T, hc, hb⟩ := jointCell_exists_regular_weighted_partial_cover
    (jointCellLayerNeighbors m k c) ((m - k).choose c) ((k + c).choose c)
    hd he (jointCell_layer_neighbors_card m k c) hinc K B t hK hB ht
  refine ⟨S, T, ?_, ?_⟩
  · intro y hy
    obtain ⟨X, hX, hn⟩ := hc y hy
    exact ⟨X, hX, (Finset.mem_filter.mp hn).2⟩
  · simpa only [jointCell_layer_card] using hb

/-- The loss is logarithmic in the fallback cost B, rather than in the
number of inputs covered by a star. -/
theorem jointCell_exists_downward_layer_log_cost (m k c : ℕ)
    (hkc : k + c ≤ m) (K B : ℝ) (hK : 0 < K) (hB : 1 ≤ B) :
    ∃ (S : Finset (JointCellLayer m (k + c))) (T : Finset (JointCellLayer m k)),
      (∀ y, y ∉ T → ∃ X ∈ S, y.val ⊆ X.val) ∧
      K * (k + c).choose c * S.card + B * T.card ≤
        m.choose k * (K * Real.log B + 1) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨S, T, hc, hb⟩ := jointCell_exists_downward_layer_partial_cover
    m k c hkc K B (Real.log B) hK hBpos.le (Real.log_nonneg hB)
  refine ⟨S, T, hc, ?_⟩
  simpa only [Real.exp_neg, Real.exp_log hBpos, mul_inv_cancel₀ hBpos.ne'] using hb

end HeadComplexity.AxisZeroGluing
