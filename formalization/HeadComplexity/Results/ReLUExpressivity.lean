import HeadComplexity.Atoms.ReLUHead

set_option linter.style.header false

/-!
# Exact Boolean expressivity of one head with a residual ReLU MLP

Theorems 2.8 and 2.9(a) of VerifiedMechanisms: the minimum MLP width equals
the minimum shallow ReLU width, and one neuron per point in the smaller label
class suffices. This is exact representation on a finite cube, without a
continuous universal approximation theorem or a sign-pattern counting premise.
-/

namespace HeadComplexity

open scoped BigOperators

variable {n : ℕ}

/-- Constant coefficient of a ReLU point indicator. -/
noncomputable def pointReLUConst (a : Fin n → Bool) : ℝ :=
  1 - 2 * ∑ i, boolToReal (a i)

/-- Linear coefficients of a ReLU point indicator. -/
noncomputable def pointReLUCoeff (a : Fin n → Bool) (i : Fin n) : ℝ :=
  2 * (2 * boolToReal (a i) - 1)

/-- One ReLU unit is exactly the indicator of a chosen Boolean input. -/
theorem relu_point_indicator (a x : Fin n → Bool) :
    relu (affineValue (pointReLUConst a) (pointReLUCoeff a) x) =
      if x = a then 1 else 0 := by
  classical
  let S := Finset.univ.filter (fun i => x i ≠ a i)
  have hterm (i : Fin n) : (if x i ≠ a i then (1 : ℝ) else 0) =
      boolToReal (a i) + (1 - 2 * boolToReal (a i)) * boolToReal (x i) := by
    cases a i <;> cases x i <;> norm_num [boolToReal]
  have hcard : (S.card : ℝ) =
      ∑ i, (boolToReal (a i) + (1 - 2 * boolToReal (a i)) * boolToReal (x i)) := by
    simp only [S, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, hterm]
  have haff : affineValue (pointReLUConst a) (pointReLUCoeff a) x =
      1 - 2 * (S.card : ℝ) := by
    rw [hcard]
    simp only [affineValue, pointReLUConst, pointReLUCoeff, Finset.sum_add_distrib,
      Finset.mul_sum]
    have hs : (∑ i, 2 * (2 * boolToReal (a i) - 1) * boolToReal (x i)) =
        -(∑ i, 2 * ((1 - 2 * boolToReal (a i)) * boolToReal (x i))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hs]
    simp only [← Finset.mul_sum]
    ring
  rw [haff]
  by_cases hx : x = a
  · subst x
    simp [S, relu]
  · have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hpos : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    rw [if_neg hx, relu, max_eq_right (by linarith)]

/-- An exact lookup-table classifier needs one hidden unit per input in either
chosen label class. Constants are included, using the empty label class. -/
theorem shallowReLUComputable_label_count (f : (Fin n → Bool) → Bool) (label : Bool) :
    shallowReLUComputable n (Finset.univ.filter (fun x => f x = label)).card f := by
  classical
  let S := Finset.univ.filter (fun x => f x = label)
  let point := fun j : Fin S.card => (S.equivFin.symm j).val
  refine ⟨if label then -(1 / 2 : ℝ) else 1 / 2, fun _ => 0,
    fun j => pointReLUConst (point j), fun j => pointReLUCoeff (point j),
    fun _ => if label then 1 else -1, fun x => ?_⟩
  have hsum : (∑ j : Fin S.card,
      relu (affineValue (pointReLUConst (point j)) (pointReLUCoeff (point j)) x)) =
        if f x = label then (1 : ℝ) else 0 := by
    simp_rw [relu_point_indicator]
    have hreindex : (∑ j : Fin S.card, if x = point j then (1 : ℝ) else 0) =
        ∑ a ∈ S, if x = a then (1 : ℝ) else 0 := by
      rw [← S.sum_attach, Finset.attach_eq_univ, ← S.equivFin.symm.sum_comp]
    rw [hreindex]
    simp [S]
  rw [show affineValue (if label then -(1 / 2 : ℝ) else 1 / 2) (fun _ => 0) x =
    (if label then -(1 / 2 : ℝ) else 1 / 2) by simp [affineValue]]
  rw [← Finset.mul_sum, hsum]
  cases label <;> cases f x <;> norm_num

/-- Every Boolean function has a finite shallow ReLU representation. -/
theorem exists_shallowReLUComputable (f : (Fin n → Bool) → Bool) :
    ∃ m, shallowReLUComputable n m f :=
  ⟨_, shallowReLUComputable_label_count f true⟩

/-- Every Boolean function has a finite-width MLP representation behind one head. -/
theorem exists_computableWithOneHeadMLP (f : (Fin n → Bool) → Bool) :
    ∃ m, computableWithOneHeadMLP n m f := by
  obtain ⟨m, hm⟩ := exists_shallowReLUComputable f
  exact ⟨m, oneHeadMLP_of_shallowReLUComputable hm⟩

/-- The minimum MLP width is attained. -/
theorem OneHeadMLPWidth_computable (f : (Fin n → Bool) → Bool) :
    computableWithOneHeadMLP n (OneHeadMLPWidth n f) f := by
  classical
  unfold OneHeadMLPWidth
  rw [dif_pos (exists_computableWithOneHeadMLP f)]
  exact Nat.find_spec (exists_computableWithOneHeadMLP f)

/-- A realization bounds the minimum hidden width. -/
theorem OneHeadMLPWidth_le_of_computable {m : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithOneHeadMLP n m f) : OneHeadMLPWidth n f ≤ m := by
  classical
  unfold OneHeadMLPWidth
  rw [dif_pos (exists_computableWithOneHeadMLP f)]
  exact Nat.find_min' _ hf

/-- Theorem 2.8: attention plus a residual ReLU MLP has exactly the shallow
ReLU width complexity, with model width unrestricted. -/
theorem OneHeadMLPWidth_eq_ShallowReLUWidth (f : (Fin n → Bool) → Bool) :
    OneHeadMLPWidth n f = ShallowReLUWidth n f := by
  classical
  unfold OneHeadMLPWidth ShallowReLUWidth
  rw [dif_pos (exists_computableWithOneHeadMLP f), dif_pos (exists_shallowReLUComputable f)]
  apply le_antisymm
  · exact Nat.find_min' _ (oneHeadMLP_of_shallowReLUComputable
      (Nat.find_spec (exists_shallowReLUComputable f)))
  · exact Nat.find_min' _ (shallowReLUComputable_of_oneHeadMLP
      (Nat.find_spec (exists_computableWithOneHeadMLP f)))

/-- With no hidden units, the model computes precisely linear threshold
functions, including constants. -/
theorem OneHeadMLPWidth_eq_zero_iff_isLTF (f : (Fin n → Bool) → Bool) :
    OneHeadMLPWidth n f = 0 ↔ isLTF f := by
  have hzero : shallowReLUComputable n 0 f ↔ isLTF f := by
    constructor
    · rintro ⟨b₀, b, a₀, a, c, h⟩
      exact ⟨b₀, b, fun x => by simpa [affineValue] using h x⟩
    · rintro ⟨b₀, b, h⟩
      exact ⟨b₀, b, Fin.elim0, Fin.elim0, Fin.elim0,
        fun x => by simpa [affineValue] using h x⟩
  constructor
  · intro h
    apply hzero.mp
    have hc := shallowReLUComputable_of_oneHeadMLP (OneHeadMLPWidth_computable f)
    simpa [h] using hc
  · intro h
    exact Nat.eq_zero_of_le_zero (OneHeadMLPWidth_le_of_computable
      (oneHeadMLP_of_shallowReLUComputable (hzero.mpr h)))

/-- Theorem 2.9(a): one neuron per point in the smaller label class suffices. -/
theorem OneHeadMLPWidth_le_min_label_count (f : (Fin n → Bool) → Bool) :
    OneHeadMLPWidth n f ≤ min
      (Finset.univ.filter (fun x => f x = true)).card
      (Finset.univ.filter (fun x => f x = false)).card := by
  apply le_min
  · exact OneHeadMLPWidth_le_of_computable
      (oneHeadMLP_of_shallowReLUComputable (shallowReLUComputable_label_count f true))
  · exact OneHeadMLPWidth_le_of_computable
      (oneHeadMLP_of_shallowReLUComputable (shallowReLUComputable_label_count f false))

/-- Universal hidden-width upper bound. The zero-bit case is also included. -/
theorem OneHeadMLPWidth_le_universal_boolean (f : (Fin n → Bool) → Bool) :
    OneHeadMLPWidth n f ≤ 2 ^ (n - 1) := by
  classical
  have hsum : (Finset.univ.filter (fun x => f x = true)).card +
      (Finset.univ.filter (fun x => f x = false)).card = 2 ^ n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => f x = true)
    simpa using h
  have hle := OneHeadMLPWidth_le_min_label_count f
  cases n with
  | zero => simp only [pow_zero] at hsum; norm_num; omega
  | succ k =>
      simp only [Nat.add_sub_cancel, pow_succ] at hsum ⊢
      omega

/-- Full Boolean expressivity at the stated fixed width, padding with unused
neurons when the function requires fewer. -/
theorem computableWithOneHeadMLP_universal_boolean (f : (Fin n → Bool) → Bool) :
    computableWithOneHeadMLP n (2 ^ (n - 1)) f :=
  oneHeadMLP_of_shallowReLUComputable
    (shallowReLUComputable_mono (OneHeadMLPWidth_le_universal_boolean f)
      (shallowReLUComputable_of_oneHeadMLP (OneHeadMLPWidth_computable f)))

end HeadComplexity
