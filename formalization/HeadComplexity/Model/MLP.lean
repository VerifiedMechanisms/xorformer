import HeadComplexity.Model.Head

set_option linter.style.header false

/-!
# A residual ReLU MLP at the query position

The hidden width is independent of the residual-stream width. This is a separate
model from attention-only computability, so the meaning of `HStar` is unchanged.
-/

namespace HeadComplexity

open scoped InnerProductSpace

/-- Scalar rectified linear activation. -/
noncomputable def relu (x : ℝ) : ℝ := max x 0

/-- ReLU commutes with division by a positive scalar. -/
theorem relu_div (x D : ℝ) (hD : 0 < D) : relu (x / D) = relu x / D := by
  unfold relu
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_left (div_nonneg hx hD.le)]
  · have hx' := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_right (div_nonpos_of_nonpos_of_nonneg hx' hD.le),
      zero_div]

/-- Coordinatewise rectified linear activation. -/
noncomputable def reluVec {d : ℕ} (v : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => relu (v i))

@[simp] theorem reluVec_apply {d : ℕ} (v : Vec d) (i : Fin d) :
    reluVec v i = relu (v i) := rfl

/-- Package a family of readout vectors as the rows of a linear map. -/
noncomputable def readoutRows {d m : ℕ} (v : Fin m → Vec d) : Vec d →ₗ[ℝ] Vec m where
  toFun x := WithLp.toLp 2 (fun j => ⟪v j, x⟫_ℝ)
  map_add' x y := by ext j; simp [inner_add_right]
  map_smul' r x := by ext j; simp [inner_smul_right]

@[simp] theorem readoutRows_apply {d m : ℕ} (v : Fin m → Vec d) (x : Vec d)
    (j : Fin m) : readoutRows v x j = ⟪v j, x⟫_ℝ := rfl

/-- One hidden layer, including both biases and the residual connection. -/
structure ResidualMLP (d m : ℕ) where
  W1 : Vec d →ₗ[ℝ] Vec m
  b1 : Vec m
  W2 : Vec m →ₗ[ℝ] Vec d
  b2 : Vec d

namespace ResidualMLP

/-- Post-MLP residual stream. -/
noncomputable def eval {d m : ℕ} (M : ResidualMLP d m) (h : Vec d) : Vec d :=
  h + M.W2 (reluVec (M.W1 h + M.b1)) + M.b2

end ResidualMLP

/-- Boolean computability by one attention head and a width-`m` residual ReLU MLP. -/
def computableWithOneHeadMLP (n m : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ d, ∃ H : Head n d, ∃ M : ResidualMLP d m,
    computesPred f (fun bits => M.eval (H.residual bits))

/-- Least hidden width behind one head. Existence is proved by the Boolean
expressivity theorem, so the fallback does not occur. -/
noncomputable def OneHeadMLPWidth (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact if h : ∃ m, computableWithOneHeadMLP n m f then Nat.find h else 0

end HeadComplexity
