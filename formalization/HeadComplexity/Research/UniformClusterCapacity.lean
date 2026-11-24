import HeadComplexity.Polynomial.WeightedPolynomialSignCount
import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false
set_option maxRecDepth 1500

/-! Finite weighted capacity for equal-length reciprocal-jet clusters.
This is a comparison class, not an access theorem for original xorformers. -/

noncomputable section
namespace HeadComplexity.UniformClusterCapacity
open MvPolynomial PolynomialRootCount
open scoped BigOperators

section Reciprocal
variable {R : Type*} [CommRing R]

/-- Numerator of the r-th reciprocal coefficient after clearing B₀^(r+1). -/
def reciprocalNumerator (B : ℕ → R) : ℕ → R
  | 0 => 1
  | r + 1 => -∑ j : Fin (r + 1), B (j + 1) *
      reciprocalNumerator B (r - j) * B 0 ^ (j : ℕ)
termination_by r => r

theorem reciprocalNumerator_zero (B : ℕ → R) : reciprocalNumerator B 0 = 1 := by
  rw [reciprocalNumerator]

theorem reciprocalNumerator_succ (B : ℕ → R) (r : ℕ) :
    reciprocalNumerator B (r + 1) = -∑ j : Fin (r + 1), B (j + 1) *
      reciprocalNumerator B (r - j) * B 0 ^ (j : ℕ) := by
  rw [reciprocalNumerator]

theorem reciprocalNumerator_map {S : Type*} [CommRing S] (f : R →+* S)
    (B : ℕ → R) (r : ℕ) :
    f (reciprocalNumerator B r) = reciprocalNumerator (fun j ↦ f (B j)) r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [reciprocalNumerator_zero]
    | succ r =>
      simp only [reciprocalNumerator_succ, map_neg, map_sum, map_mul, map_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (r - j) (by omega)]
end Reciprocal

/-- These are the formal reciprocal-series coefficients. -/
def reciprocalCoefficient (B : ℕ → ℝ) (r : ℕ) : ℝ :=
  reciprocalNumerator B r / B 0 ^ (r + 1)

theorem reciprocalCoefficient_zero (B : ℕ → ℝ) : reciprocalCoefficient B 0 = 1 / B 0 := by
  simp [reciprocalCoefficient, reciprocalNumerator_zero]

theorem reciprocalCoefficient_succ (B : ℕ → ℝ) (hB : B 0 ≠ 0) (r : ℕ) :
    reciprocalCoefficient B (r + 1) =
      -(∑ j : Fin (r + 1), B (j + 1) * reciprocalCoefficient B (r - j)) / B 0 := by
  unfold reciprocalCoefficient
  rw [reciprocalNumerator_succ, neg_div, neg_div]
  congr 1
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have he : r + 1 + 1 = (r - (j : ℕ) + 1) + (j + 1) := by omega
  rw [he, pow_add, pow_succ (B 0) (j : ℕ)]
  field_simp

section WeightedReciprocal
variable {K : Type*} [Fintype K]

theorem reciprocalNumerator_weightedDegreeLE (w : K → ℕ) (G : ℕ)
    (B : ℕ → MvPolynomial K ℝ)
    (hB : ∀ j, WeightedDegreeLE w (B j) (G * j + 1)) (r : ℕ) :
    WeightedDegreeLE w (reciprocalNumerator B r) ((G + 1) * r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simpa [reciprocalNumerator_zero] using weightedDegreeLE_C w (1 : ℝ)
    | succ r =>
      rw [reciprocalNumerator_succ]
      apply weightedDegreeLE_neg
      apply weightedDegreeLE_sum Finset.univ
      intro j _
      have hrec := ih (r - j) (by omega)
      have hbase : WeightedDegreeLE w (B 0) 1 := by simpa using hB 0
      have hh := weightedDegreeLE_mul (weightedDegreeLE_mul (hB (j + 1)) hrec)
        (weightedDegreeLE_pow hbase j)
      convert hh using 1
      have he : r - (j : ℕ) + j = r := by omega
      nlinarith [congrArg (fun k ↦ (G + 1) * k) he]
end WeightedReciprocal

abbrev Parameter (n G q : ℕ) := Unit ⊕ (Bool × Fin G × Fin q × Option (Fin n))

@[simp] theorem card_parameter (n G q : ℕ) :
    Fintype.card (Parameter n G q) = 1 + 2 * (n + 1) * (G * q) := by
  simp [Parameter]
  ring

def weight (n G q : ℕ) : Parameter n G q → ℕ
  | Sum.inl _ => G * q
  | Sum.inr (false, _, j, _) => G * j + 1
  | Sum.inr (true, _, j, _) => G * (q - j)

variable {n G q : ℕ}

def affinePoly (kind : Bool) (g : Fin G) (j : Fin q) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inr (kind, g, j, none)) +
    ∑ i, C (boolToReal (x i)) * X (Sum.inr (kind, g, j, some i))

def denominatorPoly (g : Fin G) (x : Fin n → Bool) (j : ℕ) :
    MvPolynomial (Parameter n G q) ℝ :=
  if hj : j < q then affinePoly false g ⟨j, hj⟩ x else 0

def clusterNumerator (g : Fin G) (r : Fin q) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  affinePoly true g r x * reciprocalNumerator (denominatorPoly g x) r *
    denominatorPoly g x 0 ^ (q - r - 1)

def clearingPoly (x : Fin n → Bool) : MvPolynomial (Parameter n G q) ℝ :=
  ∏ g : Fin G, denominatorPoly g x 0 ^ q

def scorePoly (x : Fin n → Bool) : MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inl ()) * clearingPoly x +
    ∑ g : Fin G, (∑ r : Fin q, clusterNumerator g r x) *
      ∏ h ∈ Finset.univ.erase g, denominatorPoly h x 0 ^ q

theorem affinePoly_weightedDegreeLE (kind : Bool) (g : Fin G) (j : Fin q)
    (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q) (affinePoly kind g j x)
      (if kind then G * (q - j) else G * j + 1) := by
  unfold affinePoly
  apply weightedDegreeLE_add
  · cases kind <;> exact weightedDegreeLE_X _ _
  · apply weightedDegreeLE_sum Finset.univ
    intro i _
    apply weightedDegreeLE_C_mul
    cases kind <;> exact weightedDegreeLE_X _ _

theorem denominatorPoly_weightedDegreeLE (g : Fin G) (x : Fin n → Bool) (j : ℕ) :
    WeightedDegreeLE (weight n G q) (denominatorPoly g x j) (G * j + 1) := by
  unfold denominatorPoly
  split
  · simpa using affinePoly_weightedDegreeLE false g ⟨j, by assumption⟩ x
  · exact weightedDegreeLE_zero _ _

theorem clusterNumerator_weightedDegreeLE (g : Fin G) (r : Fin q)
    (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q) (clusterNumerator g r x) (G * q + q - 1) := by
  have h₁ := affinePoly_weightedDegreeLE true g r x
  have h₂ := reciprocalNumerator_weightedDegreeLE (weight n G q) G
    (denominatorPoly g x) (denominatorPoly_weightedDegreeLE g x) r
  have h₃ := weightedDegreeLE_pow (denominatorPoly_weightedDegreeLE (q := q) g x 0) (q - r - 1)
  have hh := weightedDegreeLE_mul (weightedDegreeLE_mul h₁ h₂) h₃
  apply weightedDegreeLE_mono hh
  have := r.isLt
  simp only [↓reduceIte, mul_zero, zero_add, one_mul]
  have he : q - (r : ℕ) + r = q := by omega
  have heq : G * (q - (r : ℕ)) + (G + 1) * r = G * q + r := by
    nlinarith [congrArg (fun k ↦ G * k) he]
  rw [heq]
  omega

theorem clearingPoly_weightedDegreeLE (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q) (clearingPoly x) (G * q) := by
  have hh := weightedDegreeLE_prod Finset.univ
    (fun g (_ : g ∈ (Finset.univ : Finset (Fin G))) ↦
      weightedDegreeLE_pow (denominatorPoly_weightedDegreeLE (q := q) g x 0) q)
  simpa [clearingPoly] using hh

theorem scorePoly_weightedDegreeLE (hq : 0 < q) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q) (scorePoly x) (2 * (G * q)) := by
  unfold scorePoly
  apply weightedDegreeLE_add
  · simpa [weight, two_mul] using weightedDegreeLE_mul
      (weightedDegreeLE_X (weight n G q) (Sum.inl ())) (clearingPoly_weightedDegreeLE x)
  · apply weightedDegreeLE_sum Finset.univ
    intro g _
    have hsum := weightedDegreeLE_sum Finset.univ
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin q))) ↦ clusterNumerator_weightedDegreeLE g r x)
    have hprod := weightedDegreeLE_prod (Finset.univ.erase g)
      (fun h (_ : h ∈ (Finset.univ.erase g)) ↦
        weightedDegreeLE_pow (denominatorPoly_weightedDegreeLE (q := q) h x 0) q)
    have hh := weightedDegreeLE_mul hsum hprod
    apply weightedDegreeLE_mono hh
    simp only [mul_zero, zero_add, one_mul, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ g), Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hg : G - 1 + 1 = G := by have := g.isLt; omega
    have heq : (G - 1) * q + q = G * q := by
      nlinarith [congrArg (fun k ↦ k * q) hg]
    omega

theorem weight_pos (hG : 0 < G) (hq : 0 < q) (i : Parameter n G q) :
    0 < weight n G q i := by
  rcases i with _ | ⟨b, g, j, i⟩
  · exact Nat.mul_pos hG hq
  · cases b
    · simp [weight]
    · exact Nat.mul_pos hG (by have := j.isLt; omega)

theorem weight_le (hG : 0 < G) (_hq : 0 < q) (i : Parameter n G q) :
    weight n G q i ≤ 2 * (G * q) := by
  rcases i with _ | ⟨b, g, j, i⟩
  · simp only [weight]; omega
  · cases b
    · simp only [weight]
      have hj : G * (j : ℕ) + G ≤ G * q := by nlinarith [j.isLt]
      omega
    · simp only [weight]
      have : G * (q - (j : ℕ)) ≤ G * q := Nat.mul_le_mul_left G (Nat.sub_le _ _)
      omega

def represented (n G q : ℕ) : Set ((Fin n → Bool) → Bool) :=
  strictPolynomialSignPatterns (scorePoly (n := n) (G := G) (q := q))

/-- Exact finite capacity with the complete product of the integer weights. -/
theorem card_represented_le (hG : 0 < G) (hq : 0 < q)
    (hparameters : 1 + 2 * (n + 1) * (G * q) ≤ 2 ^ n) :
    ((represented n G q).ncard : ℝ) ≤
      (4 * Real.exp 1 * (2 * (G * q) : ℕ) * (2 : ℝ) ^ n /
        (1 + 2 * (n + 1) * (G * q) : ℕ)) ^ (1 + 2 * (n + 1) * (G * q)) /
        ∏ i : Parameter n G q, (weight n G q i : ℝ) := by
  have hh := weightedStrictPolynomialSignPatterns_card_le
    (show 0 < Fintype.card (Parameter n G q) by simp)
    (show Fintype.card (Parameter n G q) ≤ Fintype.card (Fin n → Bool) by
      simpa only [card_parameter, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin] using hparameters)
    (weight n G q) (weight_pos hG hq) (weight_le hG hq)
    (scorePoly (n := n) (G := G) (q := q)) (scorePoly_weightedDegreeLE hq)
  simpa only [represented, card_parameter, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hh

/-- Actual reciprocal-jet score associated to arbitrary real parameter values. -/
def score (θ : Parameter n G q → ℝ) (x : Fin n → Bool) : ℝ :=
  θ (Sum.inl ()) + ∑ g : Fin G, ∑ r : Fin q,
    eval θ (affinePoly true g r x) *
      reciprocalCoefficient (fun j ↦ eval θ (denominatorPoly g x j)) r

theorem eval_clusterNumerator (θ : Parameter n G q → ℝ) (g : Fin G)
    (r : Fin q) (x : Fin n → Bool)
    (hB : eval θ (denominatorPoly g x 0) ≠ 0) :
    eval θ (clusterNumerator g r x) =
      eval θ (affinePoly true g r x) *
        reciprocalCoefficient (fun j ↦ eval θ (denominatorPoly g x j)) r *
          eval θ (denominatorPoly g x 0) ^ q := by
  simp only [clusterNumerator, map_mul, map_pow, reciprocalNumerator_map,
    reciprocalCoefficient]
  have he : q = (r : ℕ) + 1 + (q - r - 1) := by have := r.isLt; omega
  have hp : eval θ (denominatorPoly g x 0) ^ q =
      eval θ (denominatorPoly g x 0) ^ ((r : ℕ) + 1) *
        eval θ (denominatorPoly g x 0) ^ (q - r - 1) := by
    rw [← pow_add, ← he]
  rw [hp]
  field_simp

/-- Clearing positive base denominators preserves the entire score up to
an everywhere-positive multiplier. No bound on coefficients is imposed. -/
theorem eval_scorePoly (θ : Parameter n G q → ℝ) (x : Fin n → Bool)
    (hB : ∀ g, eval θ (denominatorPoly g x 0) ≠ 0) :
    eval θ (scorePoly x) = score θ x * eval θ (clearingPoly x) := by
  simp only [scorePoly, map_add, map_sum, map_mul, map_prod, map_pow, eval_X]
  rw [score, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  simp_rw [eval_clusterNumerator θ g _ x (hB g)]
  rw [← Finset.sum_mul, mul_assoc]
  congr 1
  simp only [clearingPoly, map_prod, map_pow]
  exact Finset.mul_prod_erase Finset.univ
    (fun h : Fin G ↦ eval θ (denominatorPoly h x 0) ^ q) (Finset.mem_univ g)

theorem eval_clearingPoly_pos (θ : Parameter n G q → ℝ) (x : Fin n → Bool)
    (hB : ∀ g, 0 < eval θ (denominatorPoly g x 0)) :
    0 < eval θ (clearingPoly x) := by
  simp only [clearingPoly, map_prod, map_pow]
  exact Finset.prod_pos (fun g _ ↦ pow_pos (hB g) _)

/-- Every strict reciprocal-jet truth table with positive bases belongs to
our polynomial comparison class, so the finite bound applies to it. -/
theorem mem_represented_of_score (θ : Parameter n G q → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hB : ∀ x g, 0 < eval θ (denominatorPoly g x 0))
    (hf : ∀ x, if f x then 0 < score θ x else score θ x < 0) :
    f ∈ represented n G q := by
  refine ⟨θ, fun x ↦ ?_⟩
  rw [eval_scorePoly θ x (fun g ↦ (hB x g).ne')]
  have hQ := eval_clearingPoly_pos θ x (hB x)
  have hx := hf x
  cases hfval : f x
  · simp only [hfval, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact mul_neg_of_neg_of_pos hx hQ
  · simp only [hfval, ↓reduceIte] at hx ⊢
    exact mul_pos hx hQ

/-- Arbitrary affine numerator and denominator coefficients are retained. -/
def parameterPoint (c : ℝ) (B L : Fin G → Fin q → Option (Fin n) → ℝ) :
    Parameter n G q → ℝ
  | Sum.inl _ => c
  | Sum.inr (false, g, j, i) => B g j i
  | Sum.inr (true, g, j, i) => L g j i

theorem eval_affinePoly (c : ℝ) (B L : Fin G → Fin q → Option (Fin n) → ℝ)
    (g : Fin G) (j : Fin q) (x : Fin n → Bool) (kind : Bool) :
    eval (parameterPoint c B L) (affinePoly kind g j x) =
      if kind then affineValue (L g j none) (fun i ↦ L g j (some i)) x
      else affineValue (B g j none) (fun i ↦ B g j (some i)) x := by
  cases kind <;> simp [affinePoly, parameterPoint, affineValue, mul_comm]

/-- The complete weight product, grouped by coefficient blocks. -/
theorem prod_weight (n G q : ℕ) :
    (∏ i : Parameter n G q, (weight n G q i : ℝ)) =
      (G * q : ℕ) *
        ((∏ j : Fin q, ((G * (j : ℕ) + 1 : ℕ) : ℝ)) *
          (∏ j : Fin q, ((G * (q - (j : ℕ)) : ℕ) : ℝ))) ^ ((n + 1) * G) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool,
    Fintype.card_unique, pow_one, weight, Finset.prod_const, Finset.card_univ,
    Fintype.card_option, Fintype.card_fin]
  simp only [Finset.prod_pow, ← pow_mul, ← mul_pow]
  rw [mul_comm (∏ j : Fin q, ((G * (q - (j : ℕ)) : ℕ) : ℝ))]

/-- Closed finite formula for the uniform cluster comparison class. -/
theorem card_represented_le_product (hG : 0 < G) (hq : 0 < q)
    (hparameters : 1 + 2 * (n + 1) * (G * q) ≤ 2 ^ n) :
    ((represented n G q).ncard : ℝ) ≤
      (4 * Real.exp 1 * (2 * (G * q) : ℕ) * (2 : ℝ) ^ n /
        (1 + 2 * (n + 1) * (G * q) : ℕ)) ^ (1 + 2 * (n + 1) * (G * q)) /
      ((G * q : ℕ) *
        ((∏ j : Fin q, ((G * (j : ℕ) + 1 : ℕ) : ℝ)) *
          (∏ j : Fin q, ((G * (q - (j : ℕ)) : ℕ) : ℝ))) ^ ((n + 1) * G)) := by
  simpa only [prod_weight] using card_represented_le (n := n) hG hq hparameters

end HeadComplexity.UniformClusterCapacity
