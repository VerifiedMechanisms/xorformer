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

/-- A common nonnegative coordinate penalty that vanishes on two centers
also vanishes on their coordinate union. Thus it cannot isolate just the
union of their downsets when the centers are incomparable. -/
theorem audited_common_penalty_zero_join {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ k, 0 ≤ q k) (x y : Fin n → Bool)
    (hx : affineValue 0 q x = 0) (hy : affineValue 0 q y = 0) :
    affineValue 0 q (fun k ↦ x k || y k) = 0 := by
  have hnonneg (bits : Fin n → Bool) (k : Fin n) :
      0 ≤ q k * boolToReal (bits k) := by
    cases bits k <;> simp [boolToReal, hq k]
  have hzero (bits : Fin n → Bool) (hbits : affineValue 0 q bits = 0) (k : Fin n) :
      q k * boolToReal (bits k) = 0 := by
    have hs : (∑ i, q i * boolToReal (bits i)) = 0 := by
      simpa only [affineValue, zero_add] using hbits
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hnonneg bits i)).mp hs k
      (Finset.mem_univ k)
  simp only [affineValue, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  have hxk := hzero x hx k
  have hyk := hzero y hy k
  cases hxv : x k <;> cases hyv : y k <;> simp_all [boolToReal]

/-- The exact weight-two defect in extending a one-hot Cauchy memory by
affinely summing its token slopes. Centering the reciprocal does not remove it. -/
theorem audited_cauchy_weight_two_defect (d t u : ℝ)
    (hd : d ≠ 0) (hdt : d - t ≠ 0) (hdu : d - u ≠ 0)
    (hdtu : d - t - u ≠ 0) :
    1 / (d - t - u) - 1 / (d - t) - 1 / (d - u) + 1 / d =
      t * u * (2 * d - t - u) / (d * (d - t) * (d - u) * (d - t - u)) := by
  field_simp [hd, hdt, hdu, hdtu]
  ring

/-- Even with full-cube-positive denominators, the centered reciprocal at
two active memory coordinates strictly exceeds the sum of its one-hot values. -/
theorem audited_cauchy_weight_two_defect_pos {d t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) (hbudget : t + u < d) :
    0 < 1 / (d - t - u) - 1 / (d - t) - 1 / (d - u) + 1 / d := by
  have hd : 0 < d := by linarith
  have hdt : 0 < d - t := by linarith
  have hdu : 0 < d - u := by linarith
  have hdtu : 0 < d - t - u := by linarith
  rw [audited_cauchy_weight_two_defect d t u hd.ne' hdt.ne' hdu.ne' hdtu.ne']
  have hn : 0 < 2 * d - t - u := by linarith
  positivity

end HeadComplexity.AxisZeroGluing
