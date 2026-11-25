import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Physical coordinates for the arbitrary-head source

One physical block is a pair of H-vectors. The denominator directions are
A-B, and the numerator directions are twice the total coordinate sum plus
A. The explicit inverse below proves these are independent coordinates for
every H, including zero.
-/

namespace HeadComplexity.RoPEGeneralCoordinates

open scoped BigOperators

abbrev Space (H : ℕ) := (Fin H → ℝ) × (Fin H → ℝ)

noncomputable def total {H : ℕ} (x : Space H) : ℝ := ∑ i, x.1 i + ∑ i, x.2 i

noncomputable def denominator {H : ℕ} (x : Space H) (i : Fin H) : ℝ := x.1 i - x.2 i
noncomputable def numerator {H : ℕ} (x : Space H) (i : Fin H) : ℝ :=
  2 * (total x + x.1 i)

noncomputable def forward (H : ℕ) : Space H →ₗ[ℝ] Space H where
  toFun x := (denominator x, numerator x)
  map_add' x y := by
    apply Prod.ext <;> funext i
    · simp [denominator]
      ring
    · simp [numerator, total, Finset.sum_add_distrib]
      ring
  map_smul' c x := by
    apply Prod.ext <;> funext i
    · simp [denominator]
      ring
    · simp [numerator, total, ← Finset.mul_sum]
      ring

noncomputable def recoveredTotal {H : ℕ} (y : Space H) : ℝ :=
  ((∑ i, y.2 i) - ∑ i, y.1 i) / (2 * H + 1)

noncomputable def backward {H : ℕ} (y : Space H) : Space H :=
  (fun i ↦ y.2 i / 2 - recoveredTotal y,
    fun i ↦ y.2 i / 2 - recoveredTotal y - y.1 i)

theorem recoveredTotal_forward {H : ℕ} (x : Space H) :
    recoveredTotal (forward H x) = total x := by
  have hn : (2 * (H : ℝ) + 1) ≠ 0 := by positivity
  simp only [recoveredTotal, forward, LinearMap.coe_mk, AddHom.coe_mk,
    numerator, denominator, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  dsimp [total]
  field_simp
  ring

theorem backward_forward {H : ℕ} (x : Space H) : backward (forward H x) = x := by
  apply Prod.ext <;> funext i
  · change (forward H x).2 i / 2 - recoveredTotal (forward H x) = x.1 i
    rw [recoveredTotal_forward]
    change numerator x i / 2 - total x = x.1 i
    dsimp [numerator]
    ring
  · change (forward H x).2 i / 2 - recoveredTotal (forward H x) -
        (forward H x).1 i = x.2 i
    rw [recoveredTotal_forward]
    change numerator x i / 2 - total x - denominator x i = x.2 i
    dsimp [numerator, denominator]
    ring

theorem forward_injective (H : ℕ) : Function.Injective (forward H) :=
  Function.LeftInverse.injective backward_forward

noncomputable def coordinateEquiv (H : ℕ) : Space H ≃ₗ[ℝ] Space H :=
  LinearEquiv.ofBijective (forward H)
    ⟨forward_injective H, LinearMap.surjective_of_injective (forward_injective H)⟩

theorem coordinateEquiv_apply (H : ℕ) (x : Space H) :
    coordinateEquiv H x = (denominator x, numerator x) := rfl

theorem coordinateEquiv_symm_apply (H : ℕ) (y : Space H) :
    (coordinateEquiv H).symm y = backward y := by
  apply (forward_injective H)
  have hright : Function.RightInverse backward (forward H) :=
    (Function.LeftInverse.rightInverse_of_surjective backward_forward
      (LinearMap.surjective_of_injective (forward_injective H)))
  exact (coordinateEquiv H).apply_symm_apply y |>.trans (hright y).symm

theorem denominator_zero_iff {H : ℕ} (x : Space H) :
    denominator x = 0 ↔ x.1 = x.2 := by
  simp only [denominator, funext_iff, Pi.zero_apply, sub_eq_zero]

theorem denominator_all_one (H : ℕ) :
    denominator (H := H) (fun _ ↦ 1, fun _ ↦ 1) = 0 := by
  funext i
  simp [denominator]

noncomputable def denominatorMap (H : ℕ) : Space H →ₗ[ℝ] (Fin H → ℝ) :=
  (LinearMap.fst ℝ (Fin H → ℝ) (Fin H → ℝ)).comp (forward H)

noncomputable def kernelEquiv (H : ℕ) :
    LinearMap.ker (denominatorMap H) ≃ₗ[ℝ] (Fin H → ℝ) where
  toFun x := x.1.1
  invFun v := ⟨(v, v), by
    change denominator (v, v) = 0
    exact (denominator_zero_iff (v, v)).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    change (x.1.1, x.1.1) = x.1
    have hx : denominator x.1 = 0 := x.property
    exact Prod.ext rfl ((denominator_zero_iff x.1).mp hx)
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_denominator_kernel (H : ℕ) :
    Module.finrank ℝ (LinearMap.ker (denominatorMap H)) = H := by
  simpa using (kernelEquiv H).finrank_eq

/-- A linear combination of physical denominator rows has opposite paired coordinates. -/
noncomputable def denominatorCombination {H : ℕ} (c : Fin H → ℝ) : Space H :=
  (c, -c)

theorem denominatorCombination_pairing {H : ℕ} (c : Fin H → ℝ) (x : Space H) :
    (∑ i, c i * denominator x i) =
      (∑ i, (denominatorCombination c).1 i * x.1 i) +
      ∑ i, (denominatorCombination c).2 i * x.2 i := by
  simp only [denominatorCombination, denominator, Pi.neg_apply, mul_sub,
    Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

theorem total_denominatorCombination {H : ℕ} (c : Fin H → ℝ) :
    total (denominatorCombination c) = 0 := by
  simp [total, denominatorCombination, Finset.sum_neg_distrib]

theorem denominatorCombination_nonnegative_iff {H : ℕ} (c : Fin H → ℝ) :
    ((∀ i, 0 ≤ (denominatorCombination c).1 i) ∧
      (∀ i, 0 ≤ (denominatorCombination c).2 i)) ↔ c = 0 := by
  constructor
  · intro h
    funext i
    have hpos := h.1 i
    have hneg := h.2 i
    change 0 ≤ c i at hpos
    change 0 ≤ -c i at hneg
    change c i = 0
    exact le_antisymm (by linarith) hpos
  · rintro rfl
    simp [denominatorCombination]

theorem denominatorCombination_not_unit_sum {H : ℕ} (c : Fin H → ℝ) :
    total (denominatorCombination c) ≠ 1 := by
  rw [total_denominatorCombination]
  norm_num

end HeadComplexity.RoPEGeneralCoordinates
