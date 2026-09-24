import HeadComplexity.Results.ReLUExpressivity
import HeadComplexity.Examples.BooleanFunctions

set_option linter.style.header false

/-!
# XOR behind one attention head

The score `x + y - 2 * relu (x + y - 1) - 1/2` computes XOR with one hidden
unit. Zero hidden units cannot compute XOR, by the existing one-head obstruction.
-/

namespace HeadComplexity

/-- One ReLU unit suffices for the two-bit XOR classifier. -/
theorem xor_shallowReLU_width_one : shallowReLUComputable 2 1 xorFn := by
  refine ⟨-(1 / 2), fun _ => 1, fun _ => -1, fun _ _ => 1, fun _ => -2, ?_⟩
  intro x
  simp only [affineValue, Fin.sum_univ_two, Fin.sum_univ_one]
  cases hx : x 0 <;> cases hy : x 1 <;> norm_num [boolToReal, relu, xorFn, hx, hy]

/-- The MLP changes the one-head XOR obstruction: its exact required width is one. -/
theorem OneHeadMLPWidth_xor : OneHeadMLPWidth 2 xorFn = 1 := by
  have hle := OneHeadMLPWidth_le_of_computable
    (oneHeadMLP_of_shallowReLUComputable xor_shallowReLU_width_one)
  have hne : OneHeadMLPWidth 2 xorFn ≠ 0 := by
    intro h
    exact xor_not_computable_with_one_head_count
      (computable_one_of_isLTF xorFn ((OneHeadMLPWidth_eq_zero_iff_isLTF xorFn).mp h))
  omega

/-- Constant classifiers require no hidden neurons, including on the zero-bit cube. -/
theorem OneHeadMLPWidth_const (n : ℕ) (b : Bool) :
    OneHeadMLPWidth n (fun _ => b) = 0 := by
  apply (OneHeadMLPWidth_eq_zero_iff_isLTF _).mpr
  refine ⟨if b then 1 else -1, fun _ => 0, fun _ => ?_⟩
  cases b <;> norm_num

end HeadComplexity
