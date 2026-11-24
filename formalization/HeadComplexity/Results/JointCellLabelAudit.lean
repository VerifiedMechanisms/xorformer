import HeadComplexity.Results.AffinePlaneCompiler

set_option linter.style.header false

/-!
# Label dependence in the affine-plane compiler

These statements isolate a restricted sharing obstruction. Changing one token
changes every incident line sum and changes the corresponding Cauchy denominator.
They do not assert a lower bound for joint compilation by arbitrary heads.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- A fixed exterior pole does not erase information about a token. -/
theorem reciprocal_token_injective {X : Type*} (token : X → ℝ)
    (htoken : Function.Injective token) (pole : ℝ) :
    Function.Injective (fun x ↦ 1 / (pole - token x)) := by
  intro x y h
  have hden : pole - token x = pole - token y :=
    inv_injective (by simpa only [one_div] using h)
  exact htoken (by linarith)

/-- The line sum used by `exists_affinePlane_reverse_grid`, for one column. -/
noncomputable def auditedAffinePlaneLineSum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (pole token : F → ℝ) (memory : (F × F) → F) (L : F × F) : ℝ :=
  ∑ g : F × F, if g.2 = L.1 * g.1 + L.2 then
    1 / (pole L.1 - token (memory g)) else 0

/-- A one-point token change has exactly one summand of influence on a line. -/
theorem auditedAffinePlaneLineSum_update {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (pole token : F → ℝ) (memory : (F × F) → F) (L g : F × F) (z : F) :
    auditedAffinePlaneLineSum pole token (Function.update memory g z) L -
        auditedAffinePlaneLineSum pole token memory L =
      if g.2 = L.1 * g.1 + L.2 then
        1 / (pole L.1 - token z) - 1 / (pole L.1 - token (memory g)) else 0 := by
  classical
  unfold auditedAffinePlaneLineSum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single g]
  · simp only [Function.update_self]
    split <;> simp_all
  · intro h _ hh
    rw [Function.update_of_ne hh]
    simp
  · simp

/-- Every line through a changed point has a different line aggregate. -/
theorem auditedAffinePlaneLineSum_update_ne {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (pole token : F → ℝ) (htoken : Function.Injective token)
    (memory : (F × F) → F) (L g : F × F) (z : F)
    (hincident : g.2 = L.1 * g.1 + L.2) (hchange : z ≠ memory g) :
    auditedAffinePlaneLineSum pole token (Function.update memory g z) L ≠
      auditedAffinePlaneLineSum pole token memory L := by
  intro heq
  have h := auditedAffinePlaneLineSum_update pole token memory L g z
  rw [heq, sub_self, ite_eq_left hincident] at h
  exact hchange (reciprocal_token_injective token htoken (pole L.1)
    (sub_eq_zero.mp h.symm))

/-- A point correction cannot retain the same denominator at a column after
the encoded token changes. This only concerns the audited exact construction. -/
theorem auditedCauchyDenominator_ne {F : Type*} (token : F → ℝ)
    (htoken : Function.Injective token) (pole : ℝ) {x y : F} (hxy : x ≠ y) :
    pole - token x ≠ pole - token y := by
  intro h
  exact hxy (htoken (by linarith))

/-- One shared memory and decoder cannot encode two distinct arbitrary tables.
Sharing their geometry is a weaker condition and is not excluded. -/
theorem audited_shared_memory_table_eq {F : Type*} {a r s : ℕ}
    (decode : F → Fin a → Bool) (point : Fin r → F × F) (bit : Fin r → Fin a)
    (memory : (F × F) → Fin s → F) (table₀ table₁ : Fin r → Fin s → Bool)
    (h₀ : ∀ i j, decode (memory (point i) j) (bit i) = table₀ i j)
    (h₁ : ∀ i j, decode (memory (point i) j) (bit i) = table₁ i j) :
    table₀ = table₁ := by
  funext i j
  exact (h₀ i j).symm.trans (h₁ i j)

end HeadComplexity.AxisZeroGluing
