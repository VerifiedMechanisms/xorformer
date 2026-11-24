import HeadComplexity.Model.PureRoPE
import HeadComplexity.Analysis.RoPEPairedInterpolation
import HeadComplexity.Analysis.RoPETokenMaps

set_option linter.style.header false

/-! # Pure atoms realized at every sufficient even head width -/

namespace HeadComplexity.PureRoPEPairedRealization
noncomputable section
open scoped BigOperators InnerProductSpace
open PureRoPERotation RoPETokenMaps

variable {n m H : ℕ}

theorem exists_key (hn : n ≤ m * 2) (hm : 0 < m) (ℓ : Fin n → ℝ) :
    ∃ k : Vec (m * 2), ∀ i : Fin n,
      ⟪rotate m (i.val : ℝ) k, rotate m (n : ℝ) (canonicalQuery m)⟫_ℝ = ℓ i := by
  obtain ⟨u,v,huv⟩ := RoPEPairedInterpolation.interpolate_standard hn hm ℓ (n : ℝ)
  refine ⟨packKey u v, fun i ↦ ?_⟩
  rw [rotate_packKey_inner]
  exact huv i

def queryKey (hm : 0 < m) (ℓ : ℝ) : Vec (m * 2) :=
  EuclideanSpace.single (coord (⟨0,hm⟩ : Fin m) 0) ℓ

theorem queryKey_logit (hm : 0 < m) (ℓ q : ℝ) :
    ⟪rotate m q (queryKey hm ℓ), rotate m q (canonicalQuery m)⟫_ℝ = ℓ := by
  rw [rotate_inner]
  exact single_inner_canonicalQuery _ _

def family (hm : 0 < m) (p : Fin H → PureRoPEAtom n)
    (k₀ k₁ : Fin H → Vec (m * 2)) : PureRoPEFamily n 3 m H where
  tokenEmbed := embedding
  WQ _ := tokenMap (fun _ ↦ canonicalQuery m)
  WK h := tokenMap ![k₀ h,k₁ h,queryKey hm (Real.log (p h).γ)]
  WV h := tokenMap ![valueVector (by omega) (p h).v₀,
    valueVector (by omega) (p h).v₁,
    valueVector (by omega) ((p h).η / (p h).γ)]
  WO _ := outputMap (by omega)

variable (hm : 0 < m) (p : Fin H → PureRoPEAtom n)
  (k₀ k₁ : Fin H → Vec (m * 2))

theorem family_weight_zero
    (hk₀ : ∀ h i, ⟪rotate m (i.val : ℝ) (k₀ h),
      rotate m (n : ℝ) (canonicalQuery m)⟫_ℝ = Real.log ((p h).a i))
    (h : Fin H) (i : Fin n) : (family hm p k₀ k₁).weight h (some i) 0 = (p h).a i := by
  simp only [PureRoPEFamily.weight, family, tokenMap_embedding, Matrix.cons_val_zero,
    pureRoPEPosition, hk₀, Real.exp_log ((p h).ha i)]

theorem family_weight_one
    (hk₁ : ∀ h i, ⟪rotate m (i.val : ℝ) (k₁ h),
      rotate m (n : ℝ) (canonicalQuery m)⟫_ℝ = Real.log ((p h).b i))
    (h : Fin H) (i : Fin n) : (family hm p k₀ k₁).weight h (some i) 1 = (p h).b i := by
  simp only [PureRoPEFamily.weight, family, tokenMap_embedding, Matrix.cons_val_one,
    Matrix.cons_val_zero, pureRoPEPosition, hk₁, Real.exp_log ((p h).hb i)]

@[simp] theorem family_weight_query (h : Fin H) :
    (family hm p k₀ k₁).weight h none 2 = (p h).γ := by
  simp [PureRoPEFamily.weight, family, pureRoPEPosition, queryKey_logit,
    Real.exp_log ((p h).hγ)]

theorem family_readout_head
    (hk₀ : ∀ h i, ⟪rotate m (i.val : ℝ) (k₀ h),
      rotate m (n : ℝ) (canonicalQuery m)⟫_ℝ = Real.log ((p h).a i))
    (hk₁ : ∀ h i, ⟪rotate m (i.val : ℝ) (k₁ h),
      rotate m (n : ℝ) (canonicalQuery m)⟫_ℝ = Real.log ((p h).b i))
    (h : Fin H) (x : Fin n → Bool) :
    ⟪embedding 0, (family hm p k₀ k₁).headUpdate h x⟫_ℝ = (p h).eval x := by
  rw [PureRoPEFamily.readout_head_eq_atom]
  simp only [PureRoPEAtom.eval, PureRoPEFamily.scalarAtom,
    family_weight_zero hm p k₀ k₁ hk₀, family_weight_one hm p k₀ k₁ hk₁,
    family_weight_query]
  simp [family, mul_div_cancel₀ _ (p h).hγ.ne']

/-- Any positive even head dimension at least `n` realizes every pure family,
with three shared model coordinates and no extra heads. Both the attention
update and the residual have exactly the prescribed scalar readout. -/
theorem exists_family_at_width (hn : n ≤ m * 2) (hm : 0 < m)
    (p : Fin H → PureRoPEAtom n) :
    ∃ M : PureRoPEFamily n 3 m H,
      (∀ h i, M.weight h (some i) 0 = (p h).a i) ∧
      (∀ h i, M.weight h (some i) 1 = (p h).b i) ∧
      (∀ h, M.weight h none 2 = (p h).γ) ∧
      (∀ x, ⟪embedding 0,M.attnUpdate x⟫_ℝ = ∑ h, (p h).eval x) ∧
      (∀ x, ⟪embedding 0,M.residual x⟫_ℝ = ∑ h, (p h).eval x) := by
  classical
  choose k₀ hk₀ using fun h ↦ exists_key hn hm (fun i ↦ Real.log ((p h).a i))
  choose k₁ hk₁ using fun h ↦ exists_key hn hm (fun i ↦ Real.log ((p h).b i))
  refine ⟨family hm p k₀ k₁, family_weight_zero hm p k₀ k₁ hk₀,
    family_weight_one hm p k₀ k₁ hk₁, family_weight_query hm p k₀ k₁, ?_, ?_⟩
  · intro x
    simp only [PureRoPEFamily.attnUpdate, inner_sum,
      family_readout_head hm p k₀ k₁ hk₀ hk₁]
  · intro x
    simp only [PureRoPEFamily.residual, inner_add_right,
      show (family hm p k₀ k₁).tokenEmbed 2 = embedding 2 from rfl,
      embedding_inner, show (0 : Fin 3) ≠ 2 by decide, if_false, zero_add,
      PureRoPEFamily.attnUpdate, inner_sum, family_readout_head hm p k₀ k₁ hk₀ hk₁]

end
end HeadComplexity.PureRoPEPairedRealization
