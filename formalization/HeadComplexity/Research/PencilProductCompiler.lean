import HeadComplexity.Research.FiniteDifferenceProductCompiler
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option linter.style.header false

/-!
A margin-free compiler for affine numerators and denominators in one affine
pencil. The replacement directions may change. This is a restricted positive
result and supplies no compiler for an arbitrary original denominator family.
-/

noncomputable section
namespace HeadComplexity.PencilProductCompiler
open Finset Filter Polynomial
open scoped BigOperators Topology
open CoefficientOrderChart FiniteDifferenceProductCompiler

variable {n H : ℕ}

/-- Polynomial kernel for one forward-difference power. -/
def kernel (t : ℝ) (r : ℕ) : Polynomial ℝ :=
  (C t⁻¹ * (X - 1)) ^ r

lemma kernel_natDegree (t : ℝ) (r : ℕ) : (kernel t r).natDegree ≤ r := by
  calc
    _ ≤ (C t⁻¹ * (X - 1)).natDegree * r := by
      simpa only [kernel, Nat.mul_comm] using
        (natDegree_pow_le (p := C t⁻¹ * (X - 1)) (n := r))
    _ ≤ 1 * r := Nat.mul_le_mul_right _ (by
      calc
        _ ≤ (C t⁻¹).natDegree + (X - 1 : Polynomial ℝ).natDegree :=
          natDegree_mul_le
        _ ≤ 0 + 1 := Nat.add_le_add (by simp) (by
          exact (natDegree_sub_le _ _).trans (by simp))
        _ = 1 := by omega)
    _ = r := one_mul r

lemma kernel_eval (t u : ℝ) (r : ℕ) :
    (kernel t r).eval u = ((u - 1) / t) ^ r := by
  simp [kernel, div_eq_mul_inv, mul_comm]

lemma kernel_expansion (t u : ℝ) (r : Fin H) :
    ((u - 1) / t) ^ (r : ℕ) =
      ∑ j : Fin H, (kernel t r).coeff j * u ^ (j : ℕ) := by
  rw [← kernel_eval]
  rw [eval_eq_sum_range' ((kernel_natDegree t r).trans_lt r.isLt)]
  exact (Fin.sum_univ_eq_sum_range _ H).symm

/-- Affine coefficients after grouping equal exponential directions. -/
def compiledA (a : Fin H → Option (Fin n) → ℝ)
    (l : Option (Fin n) → ℝ) (t : ℝ) (j : Fin H) (i : Option (Fin n)) : ℝ :=
  Real.exp ((j : ℝ) * t * l none) *
    ∑ r : Fin H, (kernel t r).coeff j * a r i

def compiledZ (l : Option (Fin n) → ℝ) (t : ℝ) (j : Fin H) (i : Fin n) : ℝ :=
  Real.exp ((j : ℝ) * t * l (some i))

lemma compiled_term (a : Fin H → Option (Fin n) → ℝ)
    (l : Option (Fin n) → ℝ) (t : ℝ) (j : Fin H) (x : Fin n → Bool) :
    affineValue (compiledA a l t j) x *
      (∏ i, if x i then compiledZ l t j i else 1) =
      (∑ r : Fin H, (kernel t r).coeff j * affineValue (a r) x) *
        Real.exp ((j : ℝ) * t * affineValue l x) := by
  have he : Real.exp ((j : ℝ) * t * affineValue l x) =
      Real.exp ((j : ℝ) * t * l none) *
        ∏ i, if x i then compiledZ l t j i else 1 := by
    rw [← affineValue_mul, exp_affineValue]
    rfl
  rw [he]
  unfold compiledA
  rw [affineValue_mul, affineValue_sum]
  simp_rw [affineValue_mul]
  ring

lemma compiled_score (a : Fin H → Option (Fin n) → ℝ)
    (l : Option (Fin n) → ℝ) (t : ℝ) (x : Fin n → Bool) :
    (∑ j : Fin H, affineValue (compiledA a l t j) x *
      (∏ i, if x i then compiledZ l t j i else 1)) =
      ∑ r : Fin H, affineValue (a r) x *
        ((Real.exp (t * affineValue l x) - 1) / t) ^ (r : ℕ) := by
  simp_rw [compiled_term, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [kernel_expansion, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [← Real.exp_nat_mul]
  have he : Real.exp ((j : ℝ) * t * affineValue l x) =
      Real.exp ((j : ℝ) * (t * affineValue l x)) := by congr 1; ring
  rw [he]
  ring

/-- A polynomial in one affine statistic with affine coefficients compiles
into one affine-product term per power, without a margin hypothesis. -/
theorem mem_represented_of_affine_polynomial
    (a : Fin H → Option (Fin n) → ℝ) (l : Option (Fin n) → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, if f x then 0 < ∑ r : Fin H,
      affineValue (a r) x * (affineValue l x) ^ (r : ℕ)
      else (∑ r : Fin H, affineValue (a r) x *
        (affineValue l x) ^ (r : ℕ)) < 0) :
    f ∈ AffineProductCapacity.represented n H := by
  let D (t : ℝ) (x : Fin n → Bool) := ∑ r : Fin H,
    affineValue (a r) x *
      ((Real.exp (t * affineValue l x) - 1) / t) ^ (r : ℕ)
  have hlimit (x : Fin n → Bool) : Tendsto (fun t => D t x) (𝓝[>] 0)
      (𝓝 (∑ r : Fin H, affineValue (a r) x *
        (affineValue l x) ^ (r : ℕ))) := by
    exact tendsto_finsetSum _ fun r _ =>
      tendsto_const_nhds.mul ((exp_difference_quotient_limit _).pow _)
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x,
      if f x then 0 < D t x else D t x < 0 := by
    rw [Filter.eventually_all]
    intro x
    have hx := hf x
    cases he : f x <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    · exact (hlimit x).eventually_lt_const hx
    · exact (hlimit x).eventually_const_lt hx
  obtain ⟨t, ht⟩ := hevent.exists
  apply AffineProductCapacity.mem_represented_of_score 0
    (compiledA a l t) (compiledZ l t) f
  intro x
  change if f x then 0 < 0 + ∑ j, affineValue (compiledA a l t j) x *
    (∏ i, if x i then compiledZ l t j i else 1)
    else (0 + ∑ j, affineValue (compiledA a l t j) x *
      (∏ i, if x i then compiledZ l t j i else 1)) < 0
  simpa only [zero_add, compiled_score] using ht x

/-- Scalar factors in a common affine pencil. -/
def pencilFactor (α β : ℝ) : Polynomial ℝ := C α + C β * X

lemma pencilFactor_natDegree (α β : ℝ) : (pencilFactor α β).natDegree ≤ 1 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact natDegree_mul_le.trans (by simp)

@[simp] lemma pencilFactor_eval (α β u : ℝ) :
    (pencilFactor α β).eval u = α + β * u := by simp [pencilFactor]

/-- Affine coefficient vector of the globally cleared numerator. -/
def clearedPolynomial (a : Fin H → Option (Fin n) → ℝ) (α β : Fin H → ℝ)
    (i : Option (Fin n)) : Polynomial ℝ :=
  ∑ h : Fin H, C (a h i) * ∏ g ∈ univ.erase h, pencilFactor (α g) (β g)

lemma clearedPolynomial_natDegree (a : Fin H → Option (Fin n) → ℝ)
    (α β : Fin H → ℝ) (i : Option (Fin n)) :
    (clearedPolynomial a α β i).natDegree ≤ H - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro h _
  calc
    _ ≤ (C (a h i)).natDegree +
        (∏ g ∈ univ.erase h, pencilFactor (α g) (β g)).natDegree := natDegree_mul_le
    _ = (∏ g ∈ univ.erase h, pencilFactor (α g) (β g)).natDegree := by simp
    _ ≤ ∑ g ∈ univ.erase h, (pencilFactor (α g) (β g)).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ _g ∈ univ.erase h, 1 := sum_le_sum fun g _ => pencilFactor_natDegree _ _
    _ = H - 1 := by simp [card_erase_of_mem (mem_univ h)]

lemma clearedPolynomial_eval (a : Fin H → Option (Fin n) → ℝ)
    (α β : Fin H → ℝ) (u : ℝ) (x : Fin n → Bool) :
    affineValue (fun i => (clearedPolynomial a α β i).eval u) x =
      ∑ h : Fin H, affineValue (a h) x *
        ∏ g ∈ univ.erase h, (α g + β g * u) := by
  simp only [clearedPolynomial, eval_finsetSum, eval_mul, eval_C, eval_prod,
    pencilFactor_eval]
  rw [affineValue_sum]
  apply sum_congr rfl
  intro h _
  simpa only [mul_comm] using
    (affineValue_mul (∏ g ∈ univ.erase h, (α g + β g * u)) (a h) x)

lemma affinePolynomial_eval (q : Option (Fin n) → Polynomial ℝ)
    (hdeg : ∀ i, (q i).natDegree < H) (u : ℝ) (x : Fin n → Bool) :
    affineValue (fun i => (q i).eval u) x =
      ∑ r : Fin H, affineValue (fun i => (q i).coeff r) x * u ^ (r : ℕ) := by
  have he (i : Option (Fin n)) : (q i).eval u =
      ∑ r : Fin H, (q i).coeff r * u ^ (r : ℕ) := by
    rw [eval_eq_sum_range' (hdeg i)]
    exact (Fin.sum_univ_eq_sum_range _ H).symm
  simp_rw [he]
  rw [affineValue_sum]
  apply sum_congr rfl
  intro r _
  simpa only [mul_comm] using
    (affineValue_mul (u ^ (r : ℕ)) (fun i => (q i).coeff r) x)

/-- Positive global clearing, followed by a grouped finite difference,
compiles an arbitrary strict one-pencil rational score into exactly H terms.
No coefficient, pole separation, or relative-margin bound is assumed. -/
theorem mem_represented_of_pencil
    (hH : 0 < H) (a : Fin H → Option (Fin n) → ℝ)
    (l : Option (Fin n) → ℝ) (α β : Fin H → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hb : ∀ h x, 0 < α h + β h * affineValue l x)
    (hf : ∀ x, if f x then 0 < ∑ h : Fin H,
      affineValue (a h) x / (α h + β h * affineValue l x)
      else (∑ h : Fin H, affineValue (a h) x /
        (α h + β h * affineValue l x)) < 0) :
    f ∈ AffineProductCapacity.represented n H := by
  apply mem_represented_of_affine_polynomial
    (fun r i => (clearedPolynomial a α β i).coeff r) l f
  intro x
  rw [← affinePolynomial_eval (clearedPolynomial a α β)
    (fun i => (clearedPolynomial_natDegree a α β i).trans_lt (by omega)),
    clearedPolynomial_eval, cleared_score_eq _ _ (fun h => ne_of_gt (hb h x))]
  have hp : 0 < ∏ h : Fin H, (α h + β h * affineValue l x) :=
    prod_pos fun h _ => hb h x
  have hx := hf x
  cases he : f x <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_neg_of_pos hx hp
  · exact mul_pos hx hp

/-- Original admissible heads with a shared affine statistic satisfy the
compiler, including arbitrary bias and signed affine numerators. The premise
concerns the actual full denominators, not a changed head model. -/
theorem mem_represented_of_original_pencil
    (hH : 0 < H) (phi : Fin H → FracAtom n) (c : ℝ)
    (l : Option (Fin n) → ℝ) (α β : Fin H → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hpencil : ∀ h x, (phi h).γ + ∑ i, (phi h).wt x i =
      α h + β h * affineValue l x)
    (hf : ∀ x, if f x then 0 < c + ∑ h, (phi h).eval x
      else (c + ∑ h, (phi h).eval x) < 0) :
    f ∈ AffineProductCapacity.represented n H := by
  let j : Fin H := ⟨0, hH⟩
  let a := OriginalMarginCapacity.numeratorCoefficients ∘ phi
  let b := OriginalMarginCapacity.denominatorCoefficients ∘ phi
  let a' : Fin H → Option (Fin n) → ℝ := fun h i =>
    a h i + if h = j then c * b h i else 0
  have hb (h : Fin H) (x : Fin n → Bool) :
      affineValue (b h) x = α h + β h * affineValue l x := by
    simpa only [b, Function.comp_apply,
      OriginalMarginCapacity.affineValue_denominatorCoefficients] using hpencil h x
  have hpos (h : Fin H) (x : Fin n → Bool) :
      0 < α h + β h * affineValue l x := by
    rw [← hpencil]
    exact (phi h).denom_pos x
  apply mem_represented_of_pencil hH a' l α β f hpos
  intro x
  have hterm (h : Fin H) :
      affineValue (a' h) x / (α h + β h * affineValue l x) =
        (phi h).eval x + if h = j then c else 0 := by
    rw [← hb]
    by_cases hh : h = j
    · have ha : affineValue (a' h) x =
          affineValue (a h) x + c * affineValue (b h) x := by
        simp only [a', hh, ↓reduceIte]
        rw [affineValue_add, affineValue_mul]
      rw [ha, add_div, mul_div_cancel_right₀ _ (by rw [hb]; exact ne_of_gt (hpos h x))]
      simp only [hh, ↓reduceIte]
      congr 1
      simpa only [a, b, Function.comp_apply, hh] using
        OriginalMarginCapacity.affineRatio_eq_eval (phi h) x
    · simp only [a', hh, ↓reduceIte, add_zero]
      exact OriginalMarginCapacity.affineRatio_eq_eval (phi h) x
  have hs : (∑ h, affineValue (a' h) x / (α h + β h * affineValue l x)) =
      c + ∑ h, (phi h).eval x := by
    simp_rw [hterm]
    rw [sum_add_distrib]
    simp [add_comm]
  rw [hs]
  exact hf x

end HeadComplexity.PencilProductCompiler
