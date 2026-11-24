import HeadComplexity.Results.JointCellRankRepair

set_option linter.style.header false

/-! Two actual reverse heads realize a weighted squared Cauchy term in the
limit. Row and column weights are arbitrary and independent. Both Boolean
axes vanish exactly at every finite stage. No shattering claim is made. -/

namespace HeadComplexity.AxisZeroGluing

open Filter Topology
open scoped BigOperators

private theorem square_exists_axis_sum_family {r s G H : ℕ}
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

noncomputable def squaredCauchyScore {r s G : ℕ}
    (A D : Fin G → Fin r → ℝ) (T c : Fin G → Fin s → ℝ)
    (i : Fin r) (j : Fin s) : ℝ :=
  ∑ h, A h i * c h j / (D h i - T h j) ^ 2

noncomputable def squaredCauchyApprox {r s G : ℕ}
    (A D : Fin G → Fin r → ℝ) (T c : Fin G → Fin s → ℝ)
    (t : ℝ) (i : Fin r) (j : Fin s) : ℝ :=
  ∑ h, A h i * c h j /
    ((D h i - (T h j + c h j / t)) * (D h i - T h j))

/-- The exact algebraic difference quotient has a finite squared-kernel limit. -/
theorem squaredCauchyApprox_tendsto {r s G : ℕ}
    (A D : Fin G → Fin r → ℝ) (T c : Fin G → Fin s → ℝ)
    (hne : ∀ h i j, D h i - T h j ≠ 0) (i : Fin r) (j : Fin s) :
    Tendsto (fun t : ℝ ↦ squaredCauchyApprox A D T c t i j) atTop
      (𝓝 (squaredCauchyScore A D T c i j)) := by
  unfold squaredCauchyApprox squaredCauchyScore
  apply tendsto_finsetSum
  intro h _
  have ht : Tendsto (fun t : ℝ ↦ D h i - (T h j + c h j / t)) atTop
      (𝓝 (D h i - T h j)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.add
      ((tendsto_const_nhds (x := c h j)).div_atTop
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop)))
  have hf : Tendsto (fun t : ℝ ↦ A h i * c h j /
      ((D h i - (T h j + c h j / t)) * (D h i - T h j))) atTop
      (𝓝 (A h i * c h j / ((D h i - T h j) * (D h i - T h j)))) :=
    tendsto_const_nhds.div (ht.mul_const (D h i - T h j))
      (mul_ne_zero (hne h i j) (hne h i j))
  simpa only [pow_two] using hf

/-- Compact column offsets give two heads per weighted kernel, with positivity
on the entire Boolean cube and exact zeros on both entire Boolean axes. -/
theorem exists_squaredCauchyApprox_data {r s G : ℕ}
    (δ : ℝ) (A D : Fin G → Fin r → ℝ) (T c : Fin G → Fin s → ℝ)
    (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (hD : ∀ h i, 1 - δ < D h i ∧ D h i < 1)
    (hT : ∀ h j, 0 < T h j ∧ T h j < δ)
    (t : ℝ) (ht : 0 < t)
    (hTc : ∀ h j, 0 < T h j + c h j / t ∧ T h j + c h j / t < δ) :
    ∃ Q : ReverseAxisData r s (2 * G), ∀ i j,
      Q.score (localGrid i j) = squaredCauchyApprox A D T c t i j := by
  let u : Fin G → Fin 2 → Fin s → ℝ :=
    fun h ↦ ![fun j ↦ T h j + c h j / t, T h]
  let a : Fin G → Fin 2 → Fin r → ℝ :=
    fun h ↦ ![fun i ↦ t * A h i, fun i ↦ -(t * A h i)]
  have hε (h : Fin G) (i : Fin r) : 0 < 1 - D h i := by linarith [(hD h i).2]
  have hu (h : Fin G) (k : Fin 2) (j : Fin s) : 0 < u h k j := by
    fin_cases k
    · exact (hTc h j).1
    · exact (hT h j).1
  have hule (h : Fin G) (k : Fin 2) (j : Fin s) : u h k j ≤ δ := by
    fin_cases k
    · exact (hTc h j).2.le
    · exact (hT h j).2.le
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
  have hex := square_exists_axis_sum_family Q
  rw [Nat.mul_comm G 2] at hex
  obtain ⟨R, hR⟩ := hex
  refine ⟨R, fun i j ↦ ?_⟩
  rw [hR]
  unfold squaredCauchyApprox
  apply Finset.sum_congr rfl
  intro h _
  change (balancedRowsAxisData _ _ _ _ _ _ _ _).score _ = _
  rw [balancedRowsAxisData_grid]
  simp only [a, u, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have heq : 1 - (1 - D h i) = D h i := by ring
  rw [heq]
  have hdim : (2 : ℝ) ≤ ((r + s : ℕ) : ℝ) := by
    have hr : 1 ≤ r := Fin.pos_iff_nonempty.mpr ⟨i⟩
    have hs : 1 ≤ s := Fin.pos_iff_nonempty.mpr ⟨j⟩
    exact_mod_cast (show 2 ≤ r + s by omega)
  have hδsmall : 2 * δ < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdim hδ.le) hsize
  have hd : D h i - T h j ≠ 0 := by
    have := (hD h i).1
    have := (hT h j).2
    have : 0 < D h i - T h j := by linarith
    exact this.ne'
  have hdc : D h i - (T h j + c h j / t) ≠ 0 := by
    have := (hD h i).1
    have := (hTc h j).2
    have : 0 < D h i - (T h j + c h j / t) := by linarith
    exact this.ne'
  rw [div_add_div _ _ hdc hd]
  congr 1
  field_simp [ht.ne']
  ring

/-- Any finite strict sign specification, including an arbitrary prior score,
is preserved by one actual admissible two-bank family. -/
theorem squaredCauchy_preserves_signs {r s G : ℕ}
    (δ : ℝ) (A D : Fin G → Fin r → ℝ) (T c : Fin G → Fin s → ℝ)
    (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (hD : ∀ h i, 1 - δ < D h i ∧ D h i < 1)
    (hT : ∀ h j, 0 < T h j ∧ T h j < δ)
    (σ prior : Fin r → Fin s → ℝ)
    (hstrict : ∀ i j, 0 < σ i j * (prior i j + squaredCauchyScore A D T c i j)) :
    ∃ Q : ReverseAxisData r s (2 * G), ∀ i j,
      0 < σ i j * (prior i j + Q.score (localGrid i j)) := by
  have hne : ∀ h i j, D h i - T h j ≠ 0 := by
    intro h i j
    have hdim : (2 : ℝ) ≤ ((r + s : ℕ) : ℝ) := by
      have hr : 1 ≤ r := Fin.pos_iff_nonempty.mpr ⟨i⟩
      have hs : 1 ≤ s := Fin.pos_iff_nonempty.mpr ⟨j⟩
      exact_mod_cast (show 2 ≤ r + s by omega)
    have hδsmall := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdim hδ.le) hsize
    have : 0 < D h i - T h j := by linarith [(hD h i).1, (hT h j).2]
    exact this.ne'
  have hadm : ∀ᶠ t : ℝ in atTop, ∀ h j,
      0 < T h j + c h j / t ∧ T h j + c h j / t < δ := by
    apply Filter.eventually_all.mpr
    intro h
    apply Filter.eventually_all.mpr
    intro j
    have ht : Tendsto (fun t : ℝ ↦ T h j + c h j / t) atTop (𝓝 (T h j)) := by
      simpa using tendsto_const_nhds.add
        ((tendsto_const_nhds (x := c h j)).div_atTop
          (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
    exact (ht.eventually (eventually_gt_nhds (hT h j).1)).and
      (ht.eventually (eventually_lt_nhds (hT h j).2))
  have hsign : ∀ᶠ t : ℝ in atTop, ∀ i j,
      0 < σ i j * (prior i j + squaredCauchyApprox A D T c t i j) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact ((tendsto_const_nhds.add (squaredCauchyApprox_tendsto A D T c hne i j)).const_mul
      (σ i j)).eventually (eventually_gt_nhds (hstrict i j))
  obtain ⟨t, ht, hadm, hsign⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hadm.and hsign)).exists
  obtain ⟨Q, hQ⟩ := exists_squaredCauchyApprox_data δ A D T c hδ hsize hD hT t ht hadm
  refine ⟨Q, fun i j ↦ ?_⟩
  rw [hQ]
  exact hsign i j

end HeadComplexity.AxisZeroGluing
