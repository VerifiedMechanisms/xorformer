import HeadComplexity.Model.PureRoPE
import HeadComplexity.Analysis.RoPEInterpolation
import HeadComplexity.Analysis.RoPETokenMaps

set_option linter.style.header false

/-! # Exact realization of pure scalar atoms by literal rotary attention

All heads share three coordinate token embeddings. The standard fixed schedule
uses `n+2` frequency pairs. Query self-attention and unrotated token-only values
are included, and the original number of heads is preserved.
-/

namespace HeadComplexity
noncomputable section
open scoped BigOperators InnerProductSpace

namespace PureRoPERealization
open PureRoPERotation RoPETokenMaps

theorem exists_key {n : ℕ} (ℓ : Fin n → ℝ) :
    ∃ k : Vec ((n + 2) * 2), ∀ i : Fin n,
      ⟪rotate (n + 2) (i.val : ℝ) k,
        rotate (n + 2) (n : ℝ) (canonicalQuery (n + 2))⟫_ℝ = ℓ i := by
  obtain ⟨u, v, huv⟩ := RoPEInterpolation.interpolate_standard_add_two ℓ (n : ℝ)
  refine ⟨packKey u v, fun i ↦ ?_⟩
  rw [rotate_inner_relative]
  exact (blockRotate_packKey_inner _ u v).trans (huv i)

/-- A single fixed query key prescribes its self-attention logit. -/
def queryKey (n : ℕ) (ℓ : ℝ) : Vec ((n + 2) * 2) :=
  EuclideanSpace.single (coord (⟨0, by omega⟩ : Fin (n + 2)) 0) ℓ

theorem queryKey_logit (n : ℕ) (ℓ : ℝ) :
    ⟪rotate (n + 2) (n : ℝ) (queryKey n ℓ),
      rotate (n + 2) (n : ℝ) (canonicalQuery (n + 2))⟫_ℝ = ℓ := by
  rw [rotate_inner]
  exact single_inner_canonicalQuery _ _

/-- Linear maps realizing all heads from one shared token embedding. -/
def family {n H : ℕ} (p : Fin H → PureRoPEAtom n)
    (k₀ k₁ : Fin H → Vec ((n + 2) * 2)) : PureRoPEFamily n 3 (n + 2) H where
  tokenEmbed := embedding
  WQ _ := tokenMap (fun _ ↦ canonicalQuery (n + 2))
  WK h := tokenMap ![k₀ h, k₁ h, queryKey n (Real.log (p h).γ)]
  WV h := tokenMap ![valueVector (by omega) (p h).v₀,
    valueVector (by omega) (p h).v₁,
    valueVector (by omega) ((p h).η / (p h).γ)]
  WO _ := outputMap (by omega)

variable {n H : ℕ} (p : Fin H → PureRoPEAtom n)
  (k₀ k₁ : Fin H → Vec ((n + 2) * 2))

theorem family_weight_zero
    (hk₀ : ∀ h i, ⟪rotate (n + 2) (i.val : ℝ) (k₀ h),
      rotate (n + 2) (n : ℝ) (canonicalQuery (n + 2))⟫_ℝ = Real.log ((p h).a i))
    (h : Fin H) (i : Fin n) : (family p k₀ k₁).weight h (some i) 0 = (p h).a i := by
  simp only [PureRoPEFamily.weight, family, tokenMap_embedding, Matrix.cons_val_zero,
    pureRoPEPosition, hk₀, Real.exp_log ((p h).ha i)]

theorem family_weight_one
    (hk₁ : ∀ h i, ⟪rotate (n + 2) (i.val : ℝ) (k₁ h),
      rotate (n + 2) (n : ℝ) (canonicalQuery (n + 2))⟫_ℝ = Real.log ((p h).b i))
    (h : Fin H) (i : Fin n) : (family p k₀ k₁).weight h (some i) 1 = (p h).b i := by
  simp only [PureRoPEFamily.weight, family, tokenMap_embedding, Matrix.cons_val_one,
    Matrix.cons_val_zero, pureRoPEPosition, hk₁, Real.exp_log ((p h).hb i)]

@[simp] theorem family_weight_query (h : Fin H) :
    (family p k₀ k₁).weight h none 2 = (p h).γ := by
  simp [PureRoPEFamily.weight, family, pureRoPEPosition, queryKey_logit,
    Real.exp_log ((p h).hγ)]

theorem family_readout_head
    (hk₀ : ∀ h i, ⟪rotate (n + 2) (i.val : ℝ) (k₀ h),
      rotate (n + 2) (n : ℝ) (canonicalQuery (n + 2))⟫_ℝ = Real.log ((p h).a i))
    (hk₁ : ∀ h i, ⟪rotate (n + 2) (i.val : ℝ) (k₁ h),
      rotate (n + 2) (n : ℝ) (canonicalQuery (n + 2))⟫_ℝ = Real.log ((p h).b i))
    (h : Fin H) (x : Fin n → Bool) :
    ⟪embedding 0, (family p k₀ k₁).headUpdate h x⟫_ℝ = (p h).eval x := by
  rw [PureRoPEFamily.readout_head_eq_atom]
  simp only [PureRoPEAtom.eval, PureRoPEFamily.scalarAtom,
    family_weight_zero p k₀ k₁ hk₀, family_weight_one p k₀ k₁ hk₁,
    family_weight_query]
  simp [family, mul_div_cancel₀ _ (p h).hγ.ne']

/-- Every prescribed family of pure atoms is realized with exactly the same
head count and exact real scores. The embeddings are shared, the values are
token-only, and the query residual has zero readout. -/
theorem exists_family (p : Fin H → PureRoPEAtom n) :
    ∃ M : PureRoPEFamily n 3 (n + 2) H,
      (∀ h i, M.weight h (some i) 0 = (p h).a i) ∧
      (∀ h i, M.weight h (some i) 1 = (p h).b i) ∧
      (∀ h, M.weight h none 2 = (p h).γ) ∧
      (∀ x, ⟪embedding 0, M.attnUpdate x⟫_ℝ = ∑ h, (p h).eval x) ∧
      (∀ x, ⟪embedding 0, M.residual x⟫_ℝ = ∑ h, (p h).eval x) := by
  classical
  choose k₀ hk₀ using fun h ↦ exists_key (fun i ↦ Real.log ((p h).a i))
  choose k₁ hk₁ using fun h ↦ exists_key (fun i ↦ Real.log ((p h).b i))
  refine ⟨family p k₀ k₁, family_weight_zero p k₀ k₁ hk₀,
    family_weight_one p k₀ k₁ hk₁, family_weight_query p k₀ k₁, ?_, ?_⟩
  · intro x
    simp only [PureRoPEFamily.attnUpdate, inner_sum,
      family_readout_head p k₀ k₁ hk₀ hk₁]
  · intro x
    simp only [PureRoPEFamily.residual, inner_add_right,
      show (family p k₀ k₁).tokenEmbed 2 = embedding 2 from rfl,
      embedding_inner, show (0 : Fin 3) ≠ 2 by decide, if_false, zero_add,
      PureRoPEFamily.attnUpdate, inner_sum, family_readout_head p k₀ k₁ hk₀ hk₁]

end PureRoPERealization

/-- Scalar pure computability is implemented by literal fixed-frequency rotary
attention, preserving every head budget including zero heads. -/
theorem architecture_of_pureRoPEComputable {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : pureRoPEComputable n H f) : computableWithPureRoPEHeadsN n H f := by
  obtain ⟨p, c, hp⟩ := hf
  obtain ⟨M, _, _, _, hM, _⟩ := PureRoPERealization.exists_family p
  refine ⟨3, n + 2, by omega, by omega, M, RoPETokenMaps.embedding 0, -c, ?_⟩
  intro x
  rw [hM]
  exact (show -c < ∑ h, (p h).eval x ↔ 0 < c + ∑ h, (p h).eval x by
    constructor <;> intro h <;> linarith).trans
    (hp x)

end
end HeadComplexity
