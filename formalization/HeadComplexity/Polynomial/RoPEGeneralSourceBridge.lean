import HeadComplexity.Polynomial.RoPEGeneralDerivative
import HeadComplexity.Polynomial.RoPEGeneralIrreducible

/-!
# One source polynomial for the general irreducibility and rank arguments

The derivative rank computation uses the independent denominator and numerator
variables. The irreducibility module also allows unused variables. Renaming
identifies the two sources exactly and preserves the directional-derivative rank.
-/

noncomputable section

namespace HeadComplexity.RoPEGeneralSourceBridge

open MvPolynomial RoPEGeneralDerivative
open scoped BigOperators

def embedIndex {H : ℕ} (K : ℕ) : Var H → RoPEGeneralPolynomial.Var H K
  | Sum.inl i => Sum.inl i
  | Sum.inr i => Sum.inr (Sum.inl i)

theorem embedIndex_injective {H K : ℕ} :
    Function.Injective (embedIndex (H := H) K) := by
  intro i j hij
  cases i <;> cases j <;> simp_all [embedIndex]

theorem rename_source (H K : ℕ) :
    rename (embedIndex K) (source H) = RoPEGeneralPolynomial.core H K := by
  simp [source, denomProduct, D, N, embedIndex,
    RoPEGeneralPolynomial.core, RoPEGeneralPolynomial.omittedProduct,
    RoPEGeneralPolynomial.denominatorIndex, RoPEGeneralPolynomial.numeratorIndex]

theorem rename_directional {σ τ : Type*} (f : σ → τ)
    (v : σ → ℝ) (w : τ → ℝ) (h : ∀ i, w (f i) = v i)
    (P : MvPolynomial σ ℝ) :
    rename f (directional v P) = directional w (rename f P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp [Derivation.leibniz, smul_eq_mul, hp, h]

def coreDirection {H K : ℕ} (d a : Fin H → ℝ) :
    RoPEGeneralPolynomial.Var H K → ℝ
  | Sum.inl i => d i
  | Sum.inr (Sum.inl i) => a i
  | Sum.inr (Sum.inr _) => 0

theorem coreDirection_embed {H K : ℕ} (d a : Fin H → ℝ) (i : Var H) :
    coreDirection (K := K) d a (embedIndex K i) = direction d a i := by
  cases i <;> rfl

def coreSecondMap {H : ℕ} (K : ℕ) (d a : Fin H → ℝ) :
    ((Fin H → ℝ) × (Fin H → ℝ)) →ₗ[ℝ] RoPEGeneralPolynomial.Poly H K :=
  (rename (embedIndex K)).toLinearMap.comp (secondMap d a)

theorem coreSecondMap_apply {H K : ℕ} (d a e b : Fin H → ℝ) :
    coreSecondMap K d a (e, b) =
      directional (coreDirection (K := K) e b)
        (directional (coreDirection (K := K) d a)
          (RoPEGeneralPolynomial.core H K)) := by
  change rename (embedIndex K)
    (directional (direction e b) (directional (direction d a) (source H))) = _
  rw [rename_directional _ _ _ (coreDirection_embed e b)]
  rw [rename_directional _ _ _ (coreDirection_embed d a), rename_source]

theorem coreSecondMap_ker {H K : ℕ} (d a : Fin H → ℝ) :
    (coreSecondMap K d a).ker = (secondMap d a).ker := by
  apply Submodule.ext
  intro w
  change rename (embedIndex K) (secondMap d a w) = 0 ↔ secondMap d a w = 0
  constructor
  · intro h
    apply MvPolynomial.rename_injective (embedIndex K)
      (embedIndex_injective (H := H) (K := K))
    simpa using h
  · intro h
    simp [h]

theorem coreSecondMap_rank {H K : ℕ} (d a : Fin H → ℝ) :
    Module.finrank ℝ (coreSecondMap K d a).range =
      Module.finrank ℝ (secondMap d a).range := by
  have h1 := (coreSecondMap K d a).finrank_range_add_finrank_ker
  have h2 := (secondMap d a).finrank_range_add_finrank_ker
  rw [coreSecondMap_ker] at h1
  omega

theorem coreSecondMap_rank_le_iff {H K : ℕ} (hH : 3 ≤ H)
    (d a : Fin H → ℝ) :
    Module.finrank ℝ (coreSecondMap K d a).range ≤ H ↔ d = 0 := by
  rw [coreSecondMap_rank, secondMap_rank_le_iff hH]

end HeadComplexity.RoPEGeneralSourceBridge
