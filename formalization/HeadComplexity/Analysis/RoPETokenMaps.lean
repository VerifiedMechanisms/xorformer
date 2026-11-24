import HeadComplexity.Foundation.Vec

set_option linter.style.header false

/-! # Shared token embeddings and arbitrary linear images

The three token embeddings are the same coordinate vectors for every head.
Any prescribed query, key, or value vectors are obtained by a linear map.
-/

namespace HeadComplexity.RoPETokenMaps

open scoped BigOperators InnerProductSpace

noncomputable def embedding (t : Fin 3) : Vec 3 :=
  EuclideanSpace.single t 1

noncomputable def tokenMap {d : ℕ} (v : Fin 3 → Vec d) : Vec 3 →ₗ[ℝ] Vec d :=
  ∑ t, (LinearMap.toSpanSingleton ℝ (Vec d) (v t)).comp (EuclideanSpace.projₗ t)

@[simp] theorem tokenMap_embedding {d : ℕ} (v : Fin 3 → Vec d) (t : Fin 3) :
    tokenMap v (embedding t) = v t := by
  classical
  simp [tokenMap, embedding, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, EuclideanSpace.projₗ, PiLp.projₗ_apply,
    PiLp.single_apply]

/-- A one-dimensional value channel inside any positive head width. -/
noncomputable def valueVector {d : ℕ} (hd : 0 < d) (a : ℝ) : Vec d :=
  EuclideanSpace.single ⟨0, hd⟩ a

/-- Write that channel into the first model coordinate. -/
noncomputable def outputMap {d : ℕ} (hd : 0 < d) : Vec d →ₗ[ℝ] Vec 3 :=
  (LinearMap.toSpanSingleton ℝ (Vec 3) (embedding 0)).comp
    (EuclideanSpace.projₗ ⟨0, hd⟩)

@[simp] theorem outputMap_valueVector {d : ℕ} (hd : 0 < d) (a : ℝ) :
    outputMap hd (valueVector hd a) = a • embedding 0 := by
  simp [outputMap, valueVector, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    EuclideanSpace.projₗ, PiLp.projₗ_apply]

@[simp] theorem embedding_inner (s t : Fin 3) :
    ⟪embedding s, embedding t⟫_ℝ = if s = t then 1 else 0 := by
  simp [embedding, EuclideanSpace.inner_single_left, PiLp.single_apply]

@[simp] theorem readout_value {d : ℕ} (hd : 0 < d) (a : ℝ) :
    ⟪embedding 0, outputMap hd (valueVector hd a)⟫_ℝ = a := by
  rw [outputMap_valueVector, inner_smul_right, embedding_inner]
  simp

@[simp] theorem readout_smul (a : ℝ) :
    ⟪embedding 0, a • embedding 0⟫_ℝ = a := by
  rw [inner_smul_right, embedding_inner]
  simp

end HeadComplexity.RoPETokenMaps
