import HeadComplexity.Results.ReverseGridAxisRepair

set_option linter.style.header false

/-! Two admissible reverse heads approximate an affine selector times an
 affine-over-squared-affine kernel, preserving any finite strict margins.
 This is a local construction, not an improved bound on head complexity. -/

namespace HeadComplexity.LargeDomain

open AxisZeroGluing Filter Topology
open scoped BigOperators

private theorem affine_add {n : ℕ} (a₀ b₀ : ℝ) (a b : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (a₀ + b₀) (fun i ↦ a i + b i) x =
      affineValue a₀ a x + affineValue b₀ b x := by
  simp only [affineValue, add_mul, Finset.sum_add_distrib]
  ring

private theorem affine_div {n : ℕ} (a₀ t : ℝ) (a : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (a₀ / t) (fun i ↦ a i / t) x = affineValue a₀ a x / t := by
  simp only [affineValue, add_div, Finset.sum_div, div_mul_eq_mul_div]

private theorem affine_smul {n : ℕ} (a₀ t : ℝ) (a : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (t * a₀) (fun i ↦ t * a i) x = t * affineValue a₀ a x := by
  simp only [affineValue, mul_add, Finset.mul_sum, mul_assoc]

noncomputable def productGuardSlope {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  -(1 + |f i|)

noncomputable def productGuardBase {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ) : ℝ :=
  1 + |f₀| + ∑ i, (1 + 2 * |f i|)

noncomputable def productGuard {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ)
    (x : Fin n → Bool) : ℝ :=
  affineValue (productGuardBase f₀ f) (productGuardSlope f) x

theorem productGuard_positive {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ)
    (x : Fin n → Bool) : 0 < productGuard f₀ f x := by
  have hterm (i : Fin n) :
      -(1 + |f i|) ≤ productGuardSlope f i * boolToReal (x i) := by
    cases x i <;> simp [boolToReal, productGuardSlope]
    all_goals linarith [abs_nonneg (f i)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
  have hnonneg : 0 ≤ ∑ i : Fin n, |f i| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  simp only [Finset.sum_neg_distrib] at hsum
  have heq : (∑ i : Fin n, (1 + 2 * |f i|)) =
      (∑ i : Fin n, (1 + |f i|)) + ∑ i : Fin n, |f i| := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext i
    ring
  dsimp [productGuard, affineValue, productGuardBase]
  rw [heq]
  linarith [abs_nonneg f₀]

theorem productGuard_add_positive {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ)
    (x : Fin n → Bool) : 0 < productGuard f₀ f x + affineValue f₀ f x := by
  have hterm (i : Fin n) :
      -(1 + 2 * |f i|) ≤ (productGuardSlope f i + f i) * boolToReal (x i) := by
    have hf := neg_abs_le (f i)
    cases x i <;> simp [boolToReal, productGuardSlope]
    all_goals linarith [abs_nonneg (f i)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
  simp only [Finset.sum_neg_distrib, add_mul, Finset.sum_add_distrib] at hsum
  dsimp [productGuard, affineValue, productGuardBase]
  simp only [Finset.sum_add_distrib]
  linarith [neg_abs_le f₀]

private theorem productGuard_negative {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    productGuardSlope f i < 0 := by
  dsimp [productGuardSlope]
  linarith [abs_nonneg (f i)]

private theorem productGuard_add_negative {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    productGuardSlope f i + f i < 0 := by
  dsimp [productGuardSlope]
  linarith [le_abs_self (f i)]

private theorem strict_reverse_perturb {n : ℕ} (R : WeakReverseRatio n)
    (g₀ : ℝ) (g : Fin n → ℝ)
    (hgpos : ∀ x, 0 < affineValue g₀ g x) (hgneg : ∀ i, g i < 0)
    (t scale : ℝ) (ht : 0 < t) :
    ∃ Q : StrictReverseRatio n, ∀ x,
      Q.value x = scale * affineValue R.a₀ R.a x /
        (affineValue R.b₀ R.b x + affineValue g₀ g x / t) := by
  let Q : StrictReverseRatio n :=
    { a₀ := scale * R.a₀
      a := fun i ↦ scale * R.a i
      b₀ := R.b₀ + g₀ / t
      b := fun i ↦ R.b i + g i / t
      positive := by
        intro x
        rw [affine_add, affine_div]
        exact add_pos (R.positive x) (div_pos (hgpos x) ht)
      negative := fun i ↦ add_neg_of_nonpos_of_neg (R.nonpositive i)
        (div_neg_of_neg_of_pos (hgneg i) ht) }
  refine ⟨Q, fun x ↦ ?_⟩
  change affineValue (scale * R.a₀) (fun i ↦ scale * R.a i) x /
    affineValue (R.b₀ + g₀ / t) (fun i ↦ R.b i + g i / t) x = _
  rw [affine_smul, affine_add, affine_div]

/-- Exact two-head formula, admissible for every positive parameter t. -/
theorem exists_strict_reverse_affine_product_pair {n : ℕ}
    (R : WeakReverseRatio n) (f₀ : ℝ) (f : Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) :
    ∃ Q : Fin 2 → StrictReverseRatio n, ∀ x,
      (∑ h, (Q h).value x) =
        affineValue f₀ f x * affineValue R.a₀ R.a x /
          ((affineValue R.b₀ R.b x + productGuard f₀ f x / t) *
            (affineValue R.b₀ R.b x +
              (productGuard f₀ f x + affineValue f₀ f x) / t)) := by
  obtain ⟨P, hP⟩ := strict_reverse_perturb R (productGuardBase f₀ f)
    (productGuardSlope f) (productGuard_positive f₀ f)
    (productGuard_negative f) t t ht
  obtain ⟨Q, hQ⟩ := strict_reverse_perturb R (productGuardBase f₀ f + f₀)
    (fun i ↦ productGuardSlope f i + f i)
    (fun x ↦ by rw [affine_add]; exact productGuard_add_positive f₀ f x)
    (productGuard_add_negative f) t (-t) ht
  refine ⟨![P, Q], fun x ↦ ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    hP, hQ, affine_add]
  change t * affineValue R.a₀ R.a x /
    (affineValue R.b₀ R.b x + productGuard f₀ f x / t) +
    -t * affineValue R.a₀ R.a x /
    (affineValue R.b₀ R.b x + (productGuard f₀ f x + affineValue f₀ f x) / t) = _
  have h₁ : affineValue R.b₀ R.b x + productGuard f₀ f x / t ≠ 0 :=
    (add_pos (R.positive x) (div_pos (productGuard_positive f₀ f x) ht)).ne'
  have h₂ : affineValue R.b₀ R.b x +
      (productGuard f₀ f x + affineValue f₀ f x) / t ≠ 0 :=
    (add_pos (R.positive x) (div_pos (productGuard_add_positive f₀ f x) ht)).ne'
  have hid (a d₁ d₂ : ℝ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
      t * a / d₁ + -t * a / d₂ = t * a * (d₂ - d₁) / (d₁ * d₂) := by
    field_simp
    ring
  rw [hid _ _ _ h₁ h₂]
  congr 1
  have hcancel : (affineValue R.b₀ R.b x +
      (productGuard f₀ f x + affineValue f₀ f x) / t) -
      (affineValue R.b₀ R.b x + productGuard f₀ f x / t) =
      affineValue f₀ f x / t := by ring
  rw [hcancel]
  field_simp [ht.ne']

/-- The exact formula converges to the affine-over-square product. -/
theorem strict_reverse_affine_product_pair_limit {n : ℕ}
    (R : WeakReverseRatio n) (f₀ : ℝ) (f : Fin n → ℝ) (x : Fin n → Bool) :
    Tendsto (fun t : ℝ ↦ affineValue f₀ f x * affineValue R.a₀ R.a x /
      ((affineValue R.b₀ R.b x + productGuard f₀ f x / t) *
        (affineValue R.b₀ R.b x +
          (productGuard f₀ f x + affineValue f₀ f x) / t)))
      atTop (𝓝 (affineValue f₀ f x * affineValue R.a₀ R.a x /
        (affineValue R.b₀ R.b x) ^ 2)) := by
  have h₁ : Tendsto (fun t : ℝ ↦ affineValue R.b₀ R.b x + productGuard f₀ f x / t)
      atTop (𝓝 (affineValue R.b₀ R.b x)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds (x := productGuard f₀ f x)).div_atTop
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
  have h₂ : Tendsto (fun t : ℝ ↦ affineValue R.b₀ R.b x +
      (productGuard f₀ f x + affineValue f₀ f x) / t)
      atTop (𝓝 (affineValue R.b₀ R.b x)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds (x := productGuard f₀ f x + affineValue f₀ f x)).div_atTop
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
  have hden : affineValue R.b₀ R.b x * affineValue R.b₀ R.b x ≠ 0 :=
    mul_ne_zero (R.positive x).ne' (R.positive x).ne'
  have hlim := (tendsto_const_nhds
    (x := affineValue f₀ f x * affineValue R.a₀ R.a x)).div (h₁.mul h₂) hden
  convert hlim using 1
  simp [pow_two]

/-- One parameter preserves every requested strict margin of an arbitrary
prior score plus the product, on any finite set of required cube inputs. -/
theorem affine_product_pair_preserves_signs {n : ℕ}
    (R : WeakReverseRatio n) (f₀ : ℝ) (f : Fin n → ℝ)
    (σ prior : (Fin n → Bool) → ℝ)
    (required : Finset (Fin n → Bool))
    (hstrict : ∀ x ∈ required, 0 < σ x * (prior x +
      affineValue f₀ f x * affineValue R.a₀ R.a x / (affineValue R.b₀ R.b x) ^ 2)) :
    ∃ Q : Fin 2 → StrictReverseRatio n, ∀ x ∈ required,
      0 < σ x * (prior x + ∑ h, (Q h).value x) := by
  have hev : ∀ᶠ t : ℝ in atTop, ∀ x ∈ required, 0 < σ x * (prior x +
      affineValue f₀ f x * affineValue R.a₀ R.a x /
        ((affineValue R.b₀ R.b x + productGuard f₀ f x / t) *
          (affineValue R.b₀ R.b x +
            (productGuard f₀ f x + affineValue f₀ f x) / t))) := by
    apply (Finset.eventually_all required).mpr
    intro x hx
    exact ((tendsto_const_nhds.add
      (strict_reverse_affine_product_pair_limit R f₀ f x)).const_mul (σ x)).eventually
        (eventually_gt_nhds (hstrict x hx))
  obtain ⟨t, ht, hsign⟩ := ((eventually_gt_atTop (0 : ℝ)).and hev).exists
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_affine_product_pair R f₀ f t ht
  exact ⟨Q, fun x hx ↦ by rw [hQ]; exact hsign x hx⟩

end HeadComplexity.LargeDomain
