import HeadComplexity.Analysis.RoPEInterpolation

set_option linter.style.header false

/-! # The sharp finite-width rotary interpolation bound

Both signs of each standard frequency give distinct complex nodes. Combining
the two real Fourier expansions proves that `m` real rotary pairs interpolate
arbitrary logits at any `n ≤ 2m` consecutive positions.
-/

namespace HeadComplexity.RoPEPairedInterpolation
noncomputable section
open scoped BigOperators
open RoPEFrequencies

abbrev coord {m : ℕ} (r : Fin m) (a : Fin 2) : Fin (m * 2) :=
  finProdFinEquiv (r,a)

@[simp] private theorem coord_divNat {m : ℕ} (r : Fin m) (a : Fin 2) :
    (coord r a).divNat = r :=
  congrArg Prod.fst ((finProdFinEquiv (m := m) (n := 2)).symm_apply_apply (r,a))

@[simp] private theorem coord_modNat {m : ℕ} (r : Fin m) (a : Fin 2) :
    (coord r a).modNat = a :=
  congrArg Prod.snd ((finProdFinEquiv (m := m) (n := 2)).symm_apply_apply (r,a))

/-- Positive and negative copies of every standard frequency. -/
def signedFrequency (m : ℕ) (j : Fin (m * 2)) : ℝ :=
  if j.modNat = 0 then frequency m j.divNat else -frequency m j.divNat

@[simp] theorem signedFrequency_zero {m : ℕ} (r : Fin m) :
    signedFrequency m (coord r 0) = frequency m r := by simp [signedFrequency]

@[simp] theorem signedFrequency_one {m : ℕ} (r : Fin m) :
    signedFrequency m (coord r 1) = -frequency m r := by simp [signedFrequency]

theorem signedFrequency_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (signedFrequency m) := by
  intro i j hij
  obtain ⟨⟨r,a⟩,rfl⟩ := (finProdFinEquiv (m := m) (n := 2)).surjective i
  obtain ⟨⟨s,b⟩,rfl⟩ := (finProdFinEquiv (m := m) (n := 2)).surjective j
  change signedFrequency m (coord r a) = signedFrequency m (coord s b) at hij
  fin_cases a <;> fin_cases b
  · have hrs := frequency_injective hm (by simpa using hij)
    subst s
    rfl
  · have hh : frequency m r = -frequency m s := by simpa using hij
    linarith [frequency_pos m r, frequency_pos m s]
  · have hh : -frequency m r = frequency m s := by simpa using hij
    linarith [frequency_pos m r, frequency_pos m s]
  · have hrs := frequency_injective hm (by simpa using hij)
    subst s
    rfl

theorem signedFrequency_bounds {m : ℕ} (hm : 0 < m) (j : Fin (m * 2)) :
    -1 ≤ signedFrequency m j ∧ signedFrequency m j ≤ 1 := by
  unfold signedFrequency
  split_ifs <;> constructor <;>
    linarith [frequency_pos m j.divNat, frequency_le_one hm j.divNat]

theorem signed_node_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun j ↦ Complex.exp ((signedFrequency m j : ℂ) * Complex.I)) := by
  intro i j hij
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hi := signedFrequency_bounds hm i
  have hj := signedFrequency_bounds hm j
  have he : (signedFrequency m i : ℂ) * Complex.I =
      (signedFrequency m j : ℂ) * Complex.I := by
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi
    · simpa using (show -Real.pi < signedFrequency m i by linarith)
    · simpa using (show signedFrequency m i ≤ Real.pi by linarith)
    · simpa using (show -Real.pi < signedFrequency m j by linarith)
    · simpa using (show signedFrequency m j ≤ Real.pi by linarith)
    · exact hij
  apply signedFrequency_injective hm
  simpa using congrArg Complex.im he

/-- An even rotary head width at least the number of input positions suffices.
The query position may be any fixed real number. -/
theorem interpolate_standard {n m : ℕ} (hn : n ≤ m * 2) (hm : 0 < m)
    (ℓ : Fin n → ℝ) (q : ℝ) :
    ∃ u v : Fin m → ℝ, ∀ i : Fin n,
      (∑ r, (Real.cos (((i.val : ℝ) - q) * frequency m r) * u r +
        Real.sin (((i.val : ℝ) - q) * frequency m r) * v r)) = ℓ i := by
  obtain ⟨u,v,huv⟩ := RoPEInterpolation.interpolate_of_nodes_injective hn
    (signedFrequency m) (signed_node_injective hm) ℓ q
  refine ⟨fun r ↦ u (coord r 0) + u (coord r 1),
    fun r ↦ v (coord r 0) - v (coord r 1), fun i ↦ ?_⟩
  rw [← huv i, ← (finProdFinEquiv (m := m) (n := 2)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  change _ = ∑ a : Fin 2,
    (Real.cos (((i.val : ℝ) - q) * signedFrequency m (coord r a)) * u (coord r a) +
      Real.sin (((i.val : ℝ) - q) * signedFrequency m (coord r a)) * v (coord r a))
  simp only [Fin.sum_univ_two, signedFrequency_zero, signedFrequency_one,
    mul_neg, Real.cos_neg, Real.sin_neg]
  ring

end
end HeadComplexity.RoPEPairedInterpolation
