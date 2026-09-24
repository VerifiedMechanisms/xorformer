import HeadComplexity.Atoms.ShallowReLU

set_option linter.style.header false

/-!
# Realizing shallow ReLU classifiers behind one head

The existing affine head with unit value channels is sufficient. Its channel
`i.succ` contains `(1 + x_i) / D(x)`, where `D(x) = exp 1 + n + sum x_i`.
Affine biases recover every affine numerator over this same denominator. The
score channel is used for the MLP output, with its existing residual contribution
absorbed into the affine skip term.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

variable {n m : ℕ}

/-- One fixed head supplies all the affine features needed by the MLP. -/
noncomputable def reluFeatureHead (n : ℕ) : Head n (n + 1) :=
  affHead (fun _ => 1) (n : ℝ)

/-- A readout of only the private value channels. -/
noncomputable def reluFeatureReadout (cs : Fin n → ℝ) : Vec (n + 1) :=
  WithLp.toLp 2 (Fin.cons 0 cs)

@[simp] theorem reluFeatureReadout_zero (cs : Fin n → ℝ) :
    reluFeatureReadout cs 0 = 0 := rfl

@[simp] theorem reluFeatureReadout_succ (cs : Fin n → ℝ) (i : Fin n) :
    reluFeatureReadout cs i.succ = cs i := rfl

theorem reluFeatureReadout_inner (cs : Fin n → ℝ) (v : Vec (n + 1)) :
    ⟪reluFeatureReadout cs, v⟫_ℝ = ∑ i, cs i * v i.succ := by
  rw [vecN_inner, Fin.sum_univ_succ]
  simp

theorem reluFeatureHead_numread (cs : Fin n → ℝ) (x : Fin n → Bool) :
    ⟪reluFeatureReadout cs, (reluFeatureHead n).numerator x⟫_ℝ =
      ∑ i, cs i * (1 + boolToReal (x i)) := by
  unfold Head.numerator reluFeatureHead
  rw [inner_sum, Fintype.sum_option]
  simp only [inner_smul_right, affHead_value]
  rw [affHead_x_none, EuclideanSpace.inner_single_right]
  simp only [reluFeatureReadout_zero, map_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [affHead_x_some, inner_add_right, EuclideanSpace.inner_single_right,
    reluFeatureReadout_succ, affHead_sigma_some]
  have hc : affCoeff (fun _ : Fin n => (1 : ℝ)) (n : ℝ) i = 1 := by
    simp [affCoeff]
  rw [hc]
  cases x i <;> norm_num [affTok, EuclideanSpace.inner_single_right, boolToReal, mul_comm]

/-- Every affine scalar feature is available from the same head, using a bias
and a readout that vanishes in the score channel. -/
theorem reluFeatureHead_affine (c : ℝ) (cs : Fin n → ℝ) :
    ∃ (v : Vec (n + 1)) (t : ℝ), v 0 = 0 ∧ ∀ x,
      ⟪v, (reluFeatureHead n).residual x⟫_ℝ + t =
        affineValue c cs x / (reluFeatureHead n).denominator x := by
  let τ := affTau cs c
  refine ⟨reluFeatureReadout (affCoeff cs c), -τ, rfl, fun x => ?_⟩
  have hnum :
      ⟪reluFeatureReadout (affCoeff cs c), (reluFeatureHead n).numerator x⟫_ℝ -
        τ * (reluFeatureHead n).denominator x = affineValue c cs x := by
    rw [reluFeatureHead_numread]
    have h := affHead_sign_identity cs c x
    rw [affHead_numread, affHead_denom] at h
    simpa [reluFeatureHead, affHead_denom, affineValue, τ] using h
  have hquery :
      ⟪reluFeatureReadout (affCoeff cs c), (reluFeatureHead n).x x none⟫_ℝ = 0 := by
    rw [show (reluFeatureHead n).x x none = EuclideanSpace.single 0 1 from
      affHead_x_none _ _ x, EuclideanSpace.inner_single_right]
    simp
  simp only [Head.residual, inner_add_right, hquery, zero_add, Head.attnUpdate,
    inner_smul_right]
  rw [← hnum]
  field_simp [(reluFeatureHead n).denominator_ne_zero x]
  ring

/-- Lemma 2.5: shallow ReLU classifiers are realized by one head with the same
hidden width. The residual-stream width is only `n + 1`. -/
theorem oneHeadMLP_of_shallowReLUComputable {f : (Fin n → Bool) → Bool}
    (hf : shallowReLUComputable n m f) : computableWithOneHeadMLP n m f := by
  classical
  obtain ⟨b₀, b, a₀, a, c, hsign⟩ := hf
  let H := reluFeatureHead n
  let e : Vec (n + 1) := EuclideanSpace.single 0 1
  obtain ⟨q₀, q, hq⟩ := H.exists_affine_residual_readout e 0
  obtain ⟨v, t, hv, hvt⟩ := reluFeatureHead_affine (b₀ - q₀) (fun i => b i - q i)
  choose u s _hu hus using fun j => reluFeatureHead_affine (a₀ j) (a j)
  let w := e + v
  let M : ResidualMLP (n + 1) m :=
    { W1 := readoutRows u
      b1 := WithLp.toLp 2 s
      W2 := (LinearMap.toSpanSingleton ℝ (Vec (n + 1)) e).comp
        (innerLeftLin (WithLp.toLp 2 c))
      b2 := 0 }
  have hwe : ⟪w, e⟫_ℝ = 1 := by
    simp [w, e, EuclideanSpace.inner_single_right, hv]
  have hbase (x : Fin n → Bool) :
      ⟪w, H.residual x⟫_ℝ + t = affineValue b₀ b x / H.denominator x := by
    have haff : affineValue (b₀ - q₀) (fun i => b i - q i) x =
        affineValue b₀ b x - affineValue q₀ q x := by
      simp only [affineValue, sub_mul, Finset.sum_sub_distrib]
      ring
    have ht := hvt x
    rw [haff] at ht
    have hqx : ⟪e, H.residual x⟫_ℝ = affineValue q₀ q x / H.denominator x := by
      simpa using hq x
    dsimp [w]
    rw [inner_add_left, hqx]
    calc
      _ = affineValue q₀ q x / H.denominator x +
          (affineValue b₀ b x - affineValue q₀ q x) / H.denominator x := by
            linarith [ht]
      _ = _ := by ring
  refine ⟨n + 1, H, M, w, -t, fun x => ?_⟩
  have hpre (j : Fin m) : (M.W1 (H.residual x) + M.b1) j =
      affineValue (a₀ j) (a j) x / H.denominator x := hus j x
  have hscore : ⟪w, M.eval (H.residual x)⟫_ℝ + t =
      (affineValue b₀ b x + ∑ j, c j * relu (affineValue (a₀ j) (a j) x)) /
        H.denominator x := by
    simp only [ResidualMLP.eval, inner_add_right]
    change ⟪w, H.residual x⟫_ℝ +
      ⟪w, ⟪WithLp.toLp 2 c, reluVec (M.W1 (H.residual x) + M.b1)⟫_ℝ • e⟫_ℝ +
      ⟪w, (0 : Vec (n + 1))⟫_ℝ + t = _
    rw [inner_smul_right, hwe, mul_one, inner_zero_right, add_zero,
      vecN_inner (WithLp.toLp 2 c)]
    simp only [reluVec_apply, hpre,
      relu_div _ _ (H.denominator_pos x)]
    rw [show ⟪w, H.residual x⟫_ℝ +
        (∑ j, c j * (relu (affineValue (a₀ j) (a j) x) / H.denominator x)) + t =
        (⟪w, H.residual x⟫_ℝ + t) +
        ∑ j, c j * (relu (affineValue (a₀ j) (a j) x) / H.denominator x) by ring,
      hbase x]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, ← add_div]
  calc
    _ ↔ 0 < ⟪w, M.eval (H.residual x)⟫_ℝ + t := by constructor <;> intro h <;> linarith
    _ ↔ 0 < affineValue b₀ b x + ∑ j, c j * relu (affineValue (a₀ j) (a j) x) := by
      rw [hscore, div_pos_iff_of_pos_right (H.denominator_pos x)]
    _ ↔ f x = true := hsign x

/-- Theorem 2.8, at each fixed hidden width. -/
theorem computableWithOneHeadMLP_iff_shallowReLUComputable
    (n m : ℕ) (f : (Fin n → Bool) → Bool) :
    computableWithOneHeadMLP n m f ↔ shallowReLUComputable n m f :=
  ⟨shallowReLUComputable_of_oneHeadMLP, oneHeadMLP_of_shallowReLUComputable⟩

end HeadComplexity
