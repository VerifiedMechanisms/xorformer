import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Shared width independent of the number of heads

The canonical input embedding has one coordinate for each position, one for
the bit token and one for the query. Head-specific linear maps reconstruct
the existing three-coordinate atom embedding. All query, key and value maps
have one-dimensional images, so scalar heads suffice.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators InnerProductSpace

namespace SharedWidthNormalForm

variable {n H : ℕ}

def bitCoordinate (n : ℕ) : Fin (n + 2) := Fin.natAdd n 0
def queryCoordinate (n : ℕ) : Fin (n + 2) := Fin.natAdd n 1

noncomputable def token (n : ℕ) : Fin 3 → Vec (n + 2) :=
  ![0, EuclideanSpace.single (bitCoordinate n) 1, EuclideanSpace.single (queryCoordinate n) 1]

noncomputable def position (n : ℕ) : SeqPos n → Vec (n + 2)
  | none => 0
  | some i => EuclideanSpace.single (Fin.castAdd 2 i) 1

noncomputable def atomColumn (φ : FracAtom n) : Fin (n + 2) → Vec 3 :=
  Fin.addCases (fun i ↦ fracPos φ (some i))
    (fun j : Fin 2 ↦ if j = 0 then fracTok φ 1 else fracTok φ 2)

noncomputable def reconstruct (φ : FracAtom n) : Vec (n + 2) →ₗ[ℝ] Vec 3 where
  toFun v := ∑ j, v j • atomColumn φ j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, mul_smul]

theorem reconstruct_single (φ : FracAtom n) (j : Fin (n + 2)) :
    reconstruct φ (EuclideanSpace.single j 1) = atomColumn φ j := by
  classical
  simp [reconstruct, PiLp.single_apply]

theorem reconstruct_token (φ : FracAtom n) (t : Fin 3) :
    reconstruct φ (token n t) = fracTok φ t := by
  fin_cases t <;> simp [token, reconstruct_single, atomColumn, bitCoordinate,
    queryCoordinate, fracTok]

theorem reconstruct_position (φ : FracAtom n) (p : SeqPos n) :
    reconstruct φ (position n p) = fracPos φ p := by
  cases p <;> simp [position, reconstruct_single, atomColumn, fracPos]

/-- A map whose image lies in one output coordinate. -/
noncomputable def scalarMap (T : Vec (n + 2) →ₗ[ℝ] Vec 3)
    (input : Fin 3) (output : Fin (n + 2)) : Vec (n + 2) →ₗ[ℝ] Vec (n + 2) :=
  (LinearMap.toSpanSingleton ℝ (Vec (n + 2)) (EuclideanSpace.single output 1)).comp
    ((EuclideanSpace.projₗ input).comp T)

theorem scalarMap_apply (T : Vec (n + 2) →ₗ[ℝ] Vec 3)
    (input : Fin 3) (output : Fin (n + 2)) (v : Vec (n + 2)) :
    scalarMap T input output v = EuclideanSpace.single output (T v input) := by
  simp only [scalarMap, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  ext j
  simp [PiLp.single_apply]

noncomputable def family (φ : Fin H → FracAtom n) : SharedHeadFamily n (n + 2) H where
  tokenEmbed := token n
  posEmbed := position n
  WQ h := scalarMap (reconstruct (φ h)) 2 0
  WK h := scalarMap (reconstruct (φ h)) 0 0
  WV h := scalarMap (reconstruct (φ h)) 1 (queryCoordinate n)

theorem reconstruct_x (φ : Fin H → FracAtom n) (h : Fin H)
    (bits : Fin n → Bool) (p : SeqPos n) :
    reconstruct (φ h) (((family φ).head h).x bits p) = (atomHead' (φ h)).x bits p := by
  simp only [Head.x, SharedHeadFamily.head, family, map_add,
    reconstruct_token, reconstruct_position, atomHead']

theorem sigma_eq (φ : Fin H → FracAtom n) (h : Fin H)
    (bits : Fin n → Bool) (p : SeqPos n) :
    ((family φ).head h).sigma bits p = (atomHead' (φ h)).sigma bits p := by
  simp only [Head.sigma, SharedHeadFamily.head, family]
  rw [scalarMap_apply, scalarMap_apply]
  change Real.exp ⟪EuclideanSpace.single 0
    (reconstruct (φ h) (((family φ).head h).x bits p) 0),
    EuclideanSpace.single 0
    (reconstruct (φ h) (((family φ).head h).x bits none) 2)⟫_ℝ = _
  rw [reconstruct_x, reconstruct_x]
  simp [atomHead', projTo0_apply, EuclideanSpace.inner_single_left]

theorem denominator_eq (φ : Fin H → FracAtom n) (h : Fin H) (bits : Fin n → Bool) :
    ((family φ).head h).denominator bits = (atomHead' (φ h)).denominator bits := by
  simp only [Head.denominator, sigma_eq]

theorem value_readout (φ : Fin H → FracAtom n) (h : Fin H)
    (bits : Fin n → Bool) (p : SeqPos n) :
    ⟪EuclideanSpace.single (queryCoordinate n) 1,
      ((family φ).head h).value bits p⟫_ℝ =
      ⟪fracReadout, (atomHead' (φ h)).value bits p⟫_ℝ := by
  simp only [Head.value, SharedHeadFamily.head, family]
  rw [scalarMap_apply]
  change ⟪EuclideanSpace.single (queryCoordinate n) 1,
    EuclideanSpace.single (queryCoordinate n)
      (reconstruct (φ h) (((family φ).head h).x bits p) 1)⟫_ℝ = _
  rw [reconstruct_x]
  simp [atomHead', fracReadout, EuclideanSpace.inner_single_left]

theorem head_readout (φ : Fin H → FracAtom n) (h : Fin H) (bits : Fin n → Bool) :
    ⟪EuclideanSpace.single (queryCoordinate n) 1,
      ((family φ).head h).attnUpdate bits⟫_ℝ = (φ h).eval bits := by
  rw [← atomHead'_readout (φ h) bits]
  simp only [Head.attnUpdate, inner_smul_right, denominator_eq]
  congr 1
  simp only [Head.numerator, inner_sum, inner_smul_right, sigma_eq, value_readout]

end SharedWidthNormalForm

/-- Every `H`-head function has a shared embedding of width exactly `n+2`.
The explicit construction uses only maps with one-dimensional images. -/
theorem exists_shared_width_n_add_two {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) :
    ∃ M : SharedHeadFamily n (n + 2) H, computesPred f M.attnUpdate := by
  obtain ⟨φ, c, hc⟩ := fracComputable_of_computable hf
  refine ⟨SharedWidthNormalForm.family φ,
    EuclideanSpace.single (SharedWidthNormalForm.queryCoordinate n) 1, -c, fun bits ↦ ?_⟩
  change ⟪_, ∑ h, ((SharedWidthNormalForm.family φ).head h).attnUpdate bits⟫_ℝ > -c ↔ _
  rw [inner_sum]
  simp_rw [SharedWidthNormalForm.head_readout]
  rw [← hc bits]
  constructor <;> intro h <;> linarith

/-- The previous direct-sum construction has exactly `3*H` shared coordinates. -/
theorem exists_shared_width_three_mul {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) :
    ∃ M : SharedHeadFamily n (H * 3) H, computesPred f M.attnUpdate := by
  obtain ⟨φ, c, hc⟩ := fracComputable_of_computable hf
  refine ⟨shareHeadEmbeddings (fun h ↦ atomHead' (φ h)),
    headBlockConcat (fun _ : Fin H ↦ fracReadout), -c, fun bits ↦ ?_⟩
  rw [shareHeadEmbeddings_readout]
  change ⟪fracReadout, ∑ h, (atomHead' (φ h)).attnUpdate bits⟫_ℝ > -c ↔ _
  rw [atomFamily'_readout]
  rw [← hc bits]
  constructor <;> intro h <;> linarith

/-- Minimum shared width at a fixed head count; zero if that count is infeasible. -/
noncomputable def sharedWidthAtHeads (n H : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | ∃ M : SharedHeadFamily n d H, computesPred f M.attnUpdate}

theorem sharedWidthAtHeads_le_three_mul {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) : sharedWidthAtHeads n H f ≤ H * 3 :=
  Nat.sInf_le (exists_shared_width_three_mul hf)

theorem sharedWidthAtHeads_le_min {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) : sharedWidthAtHeads n H f ≤ min (H * 3) (n + 2) :=
  Nat.le_min.mpr ⟨sharedWidthAtHeads_le_three_mul hf,
    Nat.sInf_le (exists_shared_width_n_add_two hf)⟩

end HeadComplexity
