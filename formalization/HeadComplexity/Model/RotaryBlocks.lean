import HeadComplexity.Model.Head
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-! # Literal two-coordinate rotary blocks -/

namespace HeadComplexity.PureRoPERotation
noncomputable section
open scoped BigOperators InnerProductSpace

abbrev coord {m : ℕ} (r : Fin m) (a : Fin 2) : Fin (m * 2) :=
  finProdFinEquiv (r, a)

@[simp] theorem coord_divNat {m : ℕ} (r : Fin m) (a : Fin 2) :
    (coord r a).divNat = r :=
  congrArg Prod.fst ((finProdFinEquiv (m := m) (n := 2)).symm_apply_apply (r,a))

@[simp] theorem coord_modNat {m : ℕ} (r : Fin m) (a : Fin 2) :
    (coord r a).modNat = a :=
  congrArg Prod.snd ((finProdFinEquiv (m := m) (n := 2)).symm_apply_apply (r,a))

/-- Independent ordinary real rotations in consecutive coordinate pairs. -/
def blockRotate {m : ℕ} (θ : Fin m → ℝ) : Vec (m * 2) →ₗ[ℝ] Vec (m * 2) where
  toFun v := WithLp.toLp 2 (fun j ↦
    let r := (finProdFinEquiv (m := m) (n := 2)).symm j |>.1
    let a := (finProdFinEquiv (m := m) (n := 2)).symm j |>.2
    if a = 0 then Real.cos (θ r) * v (coord r 0) - Real.sin (θ r) * v (coord r 1)
    else Real.sin (θ r) * v (coord r 0) + Real.cos (θ r) * v (coord r 1))
  map_add' x y := by
    ext j
    dsimp
    split_ifs <;> ring
  map_smul' c x := by
    ext j
    dsimp
    split_ifs <;> ring

@[simp] theorem blockRotate_apply_zero {m : ℕ} (θ : Fin m → ℝ)
    (v : Vec (m * 2)) (r : Fin m) :
    blockRotate θ v (coord r 0) =
      Real.cos (θ r) * v (coord r 0) - Real.sin (θ r) * v (coord r 1) := by
  simp [blockRotate]

@[simp] theorem blockRotate_apply_one {m : ℕ} (θ : Fin m → ℝ)
    (v : Vec (m * 2)) (r : Fin m) :
    blockRotate θ v (coord r 1) =
      Real.sin (θ r) * v (coord r 0) + Real.cos (θ r) * v (coord r 1) := by
  simp [blockRotate]

@[simp] theorem blockRotate_zero {m : ℕ} (v : Vec (m * 2)) :
    blockRotate (fun _ ↦ 0) v = v := by
  ext j
  obtain ⟨⟨r,a⟩, rfl⟩ := (finProdFinEquiv (m := m) (n := 2)).surjective j
  change blockRotate (fun _ ↦ 0) v (coord r a) = v (coord r a)
  fin_cases a <;> simp

theorem blockRotate_add {m : ℕ} (θ φ : Fin m → ℝ) (v : Vec (m * 2)) :
    blockRotate θ (blockRotate φ v) = blockRotate (fun r ↦ θ r + φ r) v := by
  ext j
  obtain ⟨⟨r,a⟩, rfl⟩ := (finProdFinEquiv (m := m) (n := 2)).surjective j
  change blockRotate θ (blockRotate φ v) (coord r a) =
    blockRotate (fun r ↦ θ r + φ r) v (coord r a)
  fin_cases a <;> simp [Real.cos_add, Real.sin_add] <;> ring

/-- Coordinate expression for the Euclidean inner product in paired blocks. -/
theorem inner_blocks {m : ℕ} (x y : Vec (m * 2)) :
    ⟪x,y⟫_ℝ = ∑ r, (x (coord r 0) * y (coord r 0) +
      x (coord r 1) * y (coord r 1)) := by
  rw [PiLp.inner_apply, ← (finProdFinEquiv (m := m) (n := 2)).sum_comp,
    Fintype.sum_prod_type]
  simp [coord, Fin.sum_univ_two, mul_comm]

theorem blockRotate_inner {m : ℕ} (θ : Fin m → ℝ) (x y : Vec (m * 2)) :
    ⟪blockRotate θ x, blockRotate θ y⟫_ℝ = ⟪x,y⟫_ℝ := by
  rw [inner_blocks, inner_blocks]
  apply Finset.sum_congr rfl
  intro r _
  simp only [blockRotate_apply_zero, blockRotate_apply_one]
  calc
    _ = (Real.sin (θ r)^2 + Real.cos (θ r)^2) *
      (x (coord r 0) * y (coord r 0) + x (coord r 1) * y (coord r 1)) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

/-- Relative-position identity, with the key vector first as in the original model. -/
theorem blockRotate_inner_relative {m : ℕ} (θ φ : Fin m → ℝ)
    (x y : Vec (m * 2)) :
    ⟪blockRotate θ x, blockRotate φ y⟫_ℝ =
      ⟪blockRotate (fun r ↦ θ r - φ r) x, y⟫_ℝ := by
  have h := blockRotate_inner (fun r ↦ -φ r) (blockRotate θ x) (blockRotate φ y)
  rw [blockRotate_add, blockRotate_add] at h
  simpa only [neg_add_cancel, blockRotate_zero, neg_add_eq_sub] using h.symm

/-- The same query vector `(1,0)` in each rotary coordinate pair. -/
def canonicalQuery (m : ℕ) : Vec (m * 2) :=
  WithLp.toLp 2 (fun j ↦ if j.modNat = 0 then 1 else 0)

/-- Package cosine and sine coefficients. The minus sign matches the key-first
inner-product convention of the attention logits. -/
def packKey {m : ℕ} (u v : Fin m → ℝ) : Vec (m * 2) :=
  WithLp.toLp 2 (fun j ↦ if j.modNat = 0 then u j.divNat else -v j.divNat)

@[simp] theorem canonicalQuery_zero {m : ℕ} (r : Fin m) :
    canonicalQuery m (coord r 0) = 1 := by simp [canonicalQuery]

@[simp] theorem canonicalQuery_one {m : ℕ} (r : Fin m) :
    canonicalQuery m (coord r 1) = 0 := by simp [canonicalQuery]

@[simp] theorem packKey_zero {m : ℕ} (u v : Fin m → ℝ) (r : Fin m) :
    packKey u v (coord r 0) = u r := by simp [packKey]

@[simp] theorem packKey_one {m : ℕ} (u v : Fin m → ℝ) (r : Fin m) :
    packKey u v (coord r 1) = -v r := by simp [packKey]

theorem blockRotate_packKey_inner {m : ℕ} (θ : Fin m → ℝ) (u v : Fin m → ℝ) :
    ⟪blockRotate θ (packKey u v), canonicalQuery m⟫_ℝ =
      ∑ r, (Real.cos (θ r) * u r + Real.sin (θ r) * v r) := by
  simp [inner_blocks]

theorem single_inner_canonicalQuery {m : ℕ} (r : Fin m) (a : ℝ) :
    ⟪EuclideanSpace.single (coord r 0) a, canonicalQuery m⟫_ℝ = a := by
  simp [EuclideanSpace.inner_single_left]

end
end HeadComplexity.PureRoPERotation
