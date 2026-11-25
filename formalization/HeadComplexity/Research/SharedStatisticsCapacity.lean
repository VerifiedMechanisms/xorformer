import HeadComplexity.Research.WeightedNormalizedCounting
import HeadComplexity.Research.MarginCapacityEstimates

set_option linter.style.header false

/-!
Margin-free weighted counting when the normalized denominator slopes factor
through `r` shared linear statistics. All numerator coefficients stay free.
The rank/factorization premise is explicit; no such reduction is asserted for
arbitrary original representations.
-/

noncomputable section
namespace HeadComplexity.SharedStatisticsCapacity
open Finset MvPolynomial PolynomialRootCount
open scoped BigOperators

variable {n H r : ℕ}

abbrev Parameter (n H r : ℕ) :=
  (Fin H × Fin n) ⊕ ((Fin H × Fin r) ⊕ (Fin r × Fin n))

@[simp] theorem card_parameter :
    Fintype.card (Parameter n H r) = n * H + r * H + n * r := by
  simp [Parameter]
  ring

def parameterWeight (k : ℕ) : Parameter n H r → ℕ
  | Sum.inl _ => k
  | Sum.inr _ => 1

def numPoly (h : Fin H) (x : Fin n → Bool) : MvPolynomial (Parameter n H r) ℝ :=
  ∑ i, C (boolToReal (x i)) * X (Sum.inl (h, i))

def statisticPoly (j : Fin r) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H r) ℝ :=
  ∑ i, C (boolToReal (x i)) * X (Sum.inr (Sum.inr (j, i)))

def denPoly (h : Fin H) (x : Fin n → Bool) : MvPolynomial (Parameter n H r) ℝ :=
  1 + ∑ j, X (Sum.inr (Sum.inl (h, j))) * statisticPoly j x

def clearedPoly (s : Bool) (x : Fin n → Bool) : MvPolynomial (Parameter n H r) ℝ :=
  C (if s then 1 else -1) * ∏ h, denPoly h x +
    ∑ h, numPoly h x * ∏ g ∈ Finset.univ.erase h, denPoly g x

theorem numPoly_weighted (k : ℕ) (h : Fin H) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (numPoly (r := r) h x) k := by
  apply weightedDegreeLE_sum
  intro i _
  apply weightedDegreeLE_C_mul
  simpa [parameterWeight] using
    (weightedDegreeLE_X (R := ℝ) (parameterWeight (n := n) (H := H) (r := r) k)
      (Sum.inl (h, i)))

theorem statisticPoly_weighted (k : ℕ) (j : Fin r) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (statisticPoly (H := H) j x) 1 := by
  apply weightedDegreeLE_sum
  intro i _
  apply weightedDegreeLE_C_mul
  simpa [parameterWeight] using
    (weightedDegreeLE_X (R := ℝ) (parameterWeight (n := n) (H := H) (r := r) k)
      (Sum.inr (Sum.inr (j, i))))

theorem denPoly_weighted (k : ℕ) (h : Fin H) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (denPoly (r := r) h x) 2 := by
  apply weightedDegreeLE_add
  · simpa using weightedDegreeLE_mono
      (weightedDegreeLE_C (R := ℝ) (parameterWeight k) 1) (show 0 ≤ 2 by omega)
  · apply weightedDegreeLE_sum
    intro j _
    have hu : WeightedDegreeLE (parameterWeight k)
        (X (Sum.inr (Sum.inl (h, j))) : MvPolynomial (Parameter n H r) ℝ) 1 := by
      simpa [parameterWeight] using
        (weightedDegreeLE_X (R := ℝ) (parameterWeight (n := n) (H := H) (r := r) k)
          (Sum.inr (Sum.inl (h, j))))
    simpa using weightedDegreeLE_mul hu (statisticPoly_weighted k j x)

theorem denProd_weighted (k : ℕ) (I : Finset (Fin H)) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (∏ h ∈ I, denPoly (r := r) h x)
      (2 * I.card) := by
  simpa [Nat.mul_comm] using weightedDegreeLE_prod I (D := fun _ ↦ 2)
    (fun h _ ↦ denPoly_weighted k h x)

theorem clearedPoly_weighted (k : ℕ) (hk : 2 ≤ k) (hH : 0 < H)
    (s : Bool) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (clearedPoly (H := H) (r := r) s x)
      (2 * H + k - 2) := by
  classical
  apply weightedDegreeLE_add
  · apply weightedDegreeLE_mono
      (weightedDegreeLE_C_mul _ (denProd_weighted k Finset.univ x))
    simp only [Finset.card_fin]
    omega
  · apply weightedDegreeLE_sum
    intro h _
    have hd := denProd_weighted (r := r) k (Finset.univ.erase h) x
    rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin] at hd
    exact weightedDegreeLE_mono (weightedDegreeLE_mul (numPoly_weighted k h x) hd)
      (by omega)

theorem product_parameter_weights (k : ℕ) :
    (∏ i : Parameter n H r, (parameterWeight k i : ℝ)) = (k : ℝ) ^ (n * H) := by
  simp only [Fintype.prod_sum_type, parameterWeight, Nat.cast_one,
    Finset.prod_const_one, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  rw [Nat.mul_comm]

def represented (n H r : ℕ) : Set ((Fin n → Bool) → Bool) :=
  strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) (r := r) false) ∪
    strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) (r := r) true)

def parameterPoint (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ) : Parameter n H r → ℝ
  | Sum.inl (h, i) => a h i
  | Sum.inr (Sum.inl (h, j)) => v h j
  | Sum.inr (Sum.inr (j, i)) => u j i

def normalizedPoint (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ) :
    NormalizedCounting.Parameter n H → ℝ
  | (h, false, i) => a h i
  | (h, true, i) => ∑ j, v h j * u j i

theorem eval_numPoly (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint a v u) (numPoly h x) =
      eval (normalizedPoint a v u) (NormalizedCounting.linearPoly false h x) := by
  simp [numPoly, NormalizedCounting.linearPoly, parameterPoint, normalizedPoint]

theorem eval_denPoly (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint a v u) (denPoly h x) =
      eval (normalizedPoint a v u) (NormalizedCounting.denPoly h x) := by
  simp only [denPoly, statisticPoly, NormalizedCounting.denPoly,
    NormalizedCounting.linearPoly, map_add, map_one, map_sum, map_mul,
    eval_X, eval_C, parameterPoint, normalizedPoint, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem eval_clearedPoly (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ)
    (s : Bool) (x : Fin n → Bool) :
    eval (parameterPoint a v u) (clearedPoly s x) =
      eval (normalizedPoint a v u) (NormalizedCounting.clearedPoly s x) := by
  simp only [clearedPoly, NormalizedCounting.clearedPoly, map_add,
    map_mul, map_prod, map_sum, eval_C, eval_numPoly, eval_denPoly]

/-- A normalized chart with a factored denominator-slope matrix belongs to
the counted comparison class. Positivity is not needed for this inclusion. -/
theorem mem_represented_of_normalized (θ : NormalizedCounting.Parameter n H → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ)
    (hfactor : ∀ h i, θ (h, true, i) = ∑ j, v h j * u j i)
    (s : Bool) (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then
      0 < eval θ (NormalizedCounting.clearedPoly s x)
      else eval θ (NormalizedCounting.clearedPoly s x) < 0) :
    f ∈ represented n H r := by
  let a : Fin H → Fin n → ℝ := fun h i ↦ θ (h, false, i)
  have hpoint : normalizedPoint a v u = θ := by
    funext z
    rcases z with ⟨h, kind, i⟩
    cases kind
    · rfl
    · exact (hfactor h i).symm
  have hmem : f ∈ strictPolynomialSignPatterns (clearedPoly (H := H) (r := r) s) := by
    refine ⟨parameterPoint a v u, fun x ↦ ?_⟩
    rw [eval_clearedPoly, hpoint]
    exact hstrict x
  cases s
  · exact Or.inl hmem
  · exact Or.inr hmem

/-- Exact bridge for an original positive-denominator affine family. The
factorization concerns normalized denominator slopes and has no margin premise. -/
theorem mem_represented_of_affine (A : AffineFractionFamily n H) (c : ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ)
    (hfactor : ∀ h i, (A.den h).coeff (Finsupp.single i 1) / (A.den h).coeff 0 =
      ∑ j, v h j * u j i)
    (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then
      0 < c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)
      else c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) < 0) :
    f ∈ represented n H r := by
  classical
  let t : ℝ := c + ∑ h, (A.num h).coeff 0 / (A.den h).coeff 0
  have hzero := hstrict (fun _ ↦ false)
  simp only [NormalizedCounting.eval_affine_zero _ (A.num_degree _),
    NormalizedCounting.eval_affine_zero _ (A.den_degree _)] at hzero
  have htne : t ≠ 0 := by
    cases hval : f (fun _ ↦ false) <;> simp only [hval, Bool.false_eq_true,
      ↓reduceIte] at hzero
    · exact ne_of_lt hzero
    · exact ne_of_gt hzero
  have ht : 0 < |t| := abs_pos.mpr htne
  have hsign : (if f (fun _ ↦ false) then (1 : ℝ) else -1) = t / |t| := by
    cases hval : f (fun _ ↦ false) <;> simp only [hval, Bool.false_eq_true,
      ↓reduceIte] at hzero ⊢
    · rw [abs_of_neg (show t < 0 from hzero)]
      field_simp
    · rw [abs_of_pos (show 0 < t from hzero), div_self htne]
  have hscore (x : Fin n → Bool) :
      NormalizedCounting.score (NormalizedCounting.parameterPoint A |t|)
        (f (fun _ ↦ false)) x =
        (c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)) / |t| := by
    unfold NormalizedCounting.score
    rw [hsign]
    simp_rw [NormalizedCounting.normalized_head_eval A ht.ne']
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    dsimp [t]
    ring
  apply mem_represented_of_normalized (NormalizedCounting.parameterPoint A |t|)
    v u hfactor (f (fun _ ↦ false)) f
  intro x
  rw [NormalizedCounting.eval_clearedPoly _ _ _
    (fun h ↦ (NormalizedCounting.eval_denPoly_pos A |t| h x).ne'), hscore]
  have hp : 0 < ∏ h : Fin H, eval (NormalizedCounting.parameterPoint A |t|)
      (NormalizedCounting.denPoly h x) :=
    Finset.prod_pos (fun h _ ↦ NormalizedCounting.eval_denPoly_pos A |t| h x)
  have hx := hstrict x
  cases hfx : f x <;> simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_pos_of_neg hp (div_neg_of_neg_of_pos hx ht)
  · exact mul_pos hp (div_pos hx ht)

/-- Original admissible atoms are included whenever their normalized slopes
factor through the indicated shared statistics. The atoms are not replaced. -/
theorem mem_represented_of_original (φ : Fin H → FracAtom n) (c : ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin r → Fin n → ℝ)
    (hfactor : ∀ h i, ((FracAtom.affineFamily φ).den h).coeff (Finsupp.single i 1) /
      ((FracAtom.affineFamily φ).den h).coeff 0 = ∑ j, v h j * u j i)
    (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then 0 < c + ∑ h, (φ h).eval x
      else c + ∑ h, (φ h).eval x < 0) : f ∈ represented n H r := by
  apply mem_represented_of_affine (FracAtom.affineFamily φ) c v u hfactor f
  intro x
  simpa only [FracAtom.affineFamily, ← FracAtom.eval_eq_numPoly_div_denPoly] using hstrict x

/-- The finite count preserves the full numerator dimension and arbitrary
signed cancellation. Its only restriction is the shared-statistics chart. -/
theorem card_represented_le (k : ℕ) (hk : 2 ≤ k)
    (hn : 0 < n) (hH : 0 < H) (hp : n * H + r * H + n * r ≤ 2 ^ n) :
    ((represented n H r).ncard : ℝ) ≤
      2 * (4 * Real.exp 1 * (2 * H + k - 2 : ℕ) * (2 : ℝ) ^ n /
        (n * H + r * H + n * r)) ^ (n * H + r * H + n * r) /
          (k : ℝ) ^ (n * H) := by
  have hc (s : Bool) := weightedStrictPolynomialSignPatterns_card_le
    (K := Parameter n H r) (by rw [card_parameter]; positivity)
    (by rw [card_parameter]
        simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hp)
    (parameterWeight k)
    (fun i ↦ by rcases i with i | i <;> simp [parameterWeight]; omega)
    (fun i ↦ by rcases i with i | i <;> simp [parameterWeight] <;> omega)
    (clearedPoly (H := H) (r := r) s) (clearedPoly_weighted k hk hH s)
  have hb (s : Bool) :
      ((strictPolynomialSignPatterns
        (clearedPoly (n := n) (H := H) (r := r) s)).ncard : ℝ) ≤
        (4 * Real.exp 1 * (2 * H + k - 2 : ℕ) * (2 : ℝ) ^ n /
          (n * H + r * H + n * r)) ^ (n * H + r * H + n * r) /
            (k : ℝ) ^ (n * H) := by
    simpa only [card_parameter, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, product_parameter_weights, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow] using hc s
  have ht : ((represented n H r).ncard : ℝ) ≤
      ((strictPolynomialSignPatterns
        (clearedPoly (n := n) (H := H) (r := r) false)).ncard : ℝ) +
      ((strictPolynomialSignPatterns
        (clearedPoly (n := n) (H := H) (r := r) true)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_union_le
      (strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) (r := r) false))
      (strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) (r := r) true))
  calc
    _ ≤ _ := ht.trans (add_le_add (hb false) (hb true))
    _ = _ := by ring

/-- The unrestricted numerator dimension contributes only the sparse-entropy
term. The degree in the head count is charged to denominator parameters. -/
theorem card_represented_le_exp (hn : 0 < n) (hH : 0 < H)
    (hp : n * H + r * H + n * r ≤ 2 ^ n) :
    ((represented n H r).ncard : ℝ) ≤
      Real.exp (Real.log 2 + ((r : ℝ) * H + n * r) *
        Real.log (16 * Real.exp 1 * (2 : ℝ) ^ n / n) +
        ((n : ℝ) * H) * Real.log (8 * Real.exp 1 * (2 : ℝ) ^ n / (n * H))) := by
  let p := n * H + r * H + n * r
  let q := n * H
  let B := 16 * Real.exp 1 * (2 : ℝ) ^ n / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hpR : (0 : ℝ) < p := by dsimp [p]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hpmin : (n : ℝ) * H ≤ p := by
    dsimp [p]
    push_cast
    nlinarith [show 0 ≤ (r : ℝ) * H by positivity,
      show 0 ≤ (n : ℝ) * r by positivity]
  have hD : ((2 * H + 2 * H - 2 : ℕ) : ℝ) ≤ 4 * (H : ℝ) := by
    exact_mod_cast (show 2 * H + 2 * H - 2 ≤ 4 * H by omega)
  have hb : 4 * Real.exp 1 * (2 * H + 2 * H - 2 : ℕ) * (2 : ℝ) ^ n /
      (p : ℝ) ≤ B := by
    apply (div_le_iff₀ hpR).mpr
    dsimp [B]
    have hh := mul_le_mul_of_nonneg_left hpmin
      (show 0 ≤ 16 * Real.exp 1 * (2 : ℝ) ^ n / n by positivity)
    have heq : (16 * Real.exp 1 * (2 : ℝ) ^ n / n) * ((n : ℝ) * H) =
        16 * Real.exp 1 * (2 : ℝ) ^ n * H := by field_simp
    rw [heq] at hh
    have hd := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ 4 * Real.exp 1 * (2 : ℝ) ^ n by positivity)
    nlinarith
  have hc := card_represented_le (r := r) (2 * H) (by omega) hn hH hp
  have hc' : ((represented n H r).ncard : ℝ) ≤
      2 * B ^ p / (2 * (H : ℝ)) ^ q := by
    refine hc.trans ?_
    change 2 * _ ^ p / ((2 * H : ℕ) : ℝ) ^ q ≤ _
    push_cast
    gcongr
    simpa [p] using hb
  have heq : Real.exp (Real.log 2 + (p : ℝ) * Real.log B -
      (q : ℝ) * Real.log (2 * (H : ℝ))) = 2 * B ^ p / (2 * (H : ℝ)) ^ q := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log hB, Real.exp_log (by positivity)]
  rw [← heq] at hc'
  have hratio : B / (2 * (H : ℝ)) =
      8 * Real.exp 1 * (2 : ℝ) ^ n / ((n : ℝ) * H) := by dsimp [B]; field_simp; ring
  have hl : Real.log (8 * Real.exp 1 * (2 : ℝ) ^ n / ((n : ℝ) * H)) =
      Real.log B - Real.log (2 * (H : ℝ)) := by
    rw [← hratio, Real.log_div hB.ne' (by positivity)]
  convert hc' using 1
  congr 1
  rw [hl]
  dsimp [p, q, B]
  push_cast
  ring

/-- A simple logarithmic upper bound for the denominator-parameter base. -/
theorem log_base_le (hn : 32 ≤ n) :
    Real.log (16 * Real.exp 1 * (2 : ℝ) ^ n / n) ≤ 2 * n := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [Real.log_div (by positivity) hnpos.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp, Real.log_pow,
    show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- The low-statistic class has fewer than half the truth-table exponent at
either requested scale. This is a restricted count, not an access theorem. -/
theorem card_represented_le_exp_at_budget {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hr : (r : ℝ) ≤ t) (hHn : n ≤ H)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (200 * n * t)) :
    ((represented n H r).ncard : ℝ) ≤ Real.exp (8 * (2 : ℝ) ^ n / 25) := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hHR : (n : ℝ) ≤ H := by exact_mod_cast hHn
  have hHpos : 0 < H := by omega
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have htpos : 0 < t := by linarith
  have hbudget := (le_div_iff₀ (by positivity : 0 < 200 * (n : ℝ) * t)).mp hwidth
  have hq : (n : ℝ) * H ≤ (2 : ℝ) ^ n / (25 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 25 * t)).mpr
    nlinarith [show 0 ≤ (n : ℝ) * H * t by positivity]
  have hp : n * H + r * H + n * r ≤ 2 ^ n := by
    have hrn : (r : ℝ) ≤ n := hr.trans hthi
    have hnr : (n : ℝ) * r ≤ n * H :=
      mul_le_mul_of_nonneg_left (hrn.trans hHR) hnpos.le
    have hrH : (r : ℝ) * H ≤ n * H := by gcongr
    have hqN : 3 * ((n : ℝ) * H) ≤ (2 : ℝ) ^ n := by
      nlinarith [mul_le_mul_of_nonneg_left ht1 (show 0 ≤ (n : ℝ) * H by positivity)]
    exact_mod_cast (show (n : ℝ) * H + r * H + n * r ≤ (2 : ℝ) ^ n by linarith)
  have he := MarginCapacityEstimates.entropy_bound (K := 0) hnR
    (by positivity : 0 < (2 : ℝ) ^ n) (le_refl 0)
    (by positivity : 0 < (n : ℝ) * H) (by norm_num : (0 : ℝ) < 2)
    htlo hthi (by positivity) hq (by
      have hexp : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr htpos.le
      nlinarith : (2 : ℝ) ≤ 6 * ((n : ℝ) + 1) * Real.exp t)
  simp only [zero_mul, zero_add] at he
  have hfirst : ((r : ℝ) * H + n * r) *
      Real.log (16 * Real.exp 1 * (2 : ℝ) ^ n / n) ≤ (2 : ℝ) ^ n / 50 := by
    have hsum : (r : ℝ) * H + n * r ≤ 2 * t * H := by
      have h1 : (r : ℝ) * H ≤ t * H := by gcongr
      have h2 : (n : ℝ) * r ≤ t * H := by
        calc
          _ = (r : ℝ) * n := by ring
          _ ≤ t * H := mul_le_mul hr hHR (Nat.cast_nonneg n) htpos.le
      linarith
    have hm := mul_le_mul_of_nonneg_left (log_base_le hn)
      (show 0 ≤ (r : ℝ) * H + n * r by positivity)
    have hm2 := mul_le_mul_of_nonneg_right hsum (show 0 ≤ 2 * (n : ℝ) by positivity)
    nlinarith
  have hlog2 : Real.log (2 : ℝ) ≤ (2 : ℝ) ^ n / 50 := by
    have hN : (64 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
        (show 6 ≤ n by omega))
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  refine (card_represented_le_exp (by omega) hHpos hp).trans (Real.exp_le_exp.mpr ?_)
  have harg : 4 * Real.exp 1 * 2 * (2 : ℝ) ^ n =
      8 * Real.exp 1 * (2 : ℝ) ^ n := by ring
  rw [harg] at he
  linarith

theorem card_represented_le_half_tables {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hr : (r : ℝ) ≤ t) (hHn : n ≤ H)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (200 * n * t)) :
    (represented n H r).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hc := card_represented_le_exp_at_budget hn htlo hthi hr hHn hwidth
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hlog : (16 : ℝ) / 25 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : 8 * (2 : ℝ) ^ n / 25 ≤ ((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (n - 1) by positivity)]
  have hreal : ((represented n H r).ncard : ℝ) ≤ (2 : ℝ) ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := hc
      _ ≤ Real.exp (((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hreal

theorem card_represented_sqrt_scale (hn : 32 ≤ n)
    (hr : (r : ℝ) ≤ Real.sqrt n) (hHn : n ≤ H)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (200 * n * Real.sqrt n)) :
    (represented n H r).ncard ≤ 2 ^ (2 ^ (n - 1)) :=
  card_represented_le_half_tables hn (MarginCapacityEstimates.sqrt_test_range hn).1
    (MarginCapacityEstimates.sqrt_test_range hn).2 hr hHn hwidth

theorem card_represented_logarithmic_scale (hn : 32 ≤ n)
    (hr : (r : ℝ) ≤ (n : ℝ) / Real.log n) (hHn : n ≤ H)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (200 * (n : ℝ) ^ 2)) :
    (represented n H r).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  apply card_represented_le_half_tables hn
    (MarginCapacityEstimates.logarithmic_test_range hn).1
    (MarginCapacityEstimates.logarithmic_test_range hn).2 hr hHn
  convert hwidth using 1
  field_simp

/-- A precise remaining structural alternative. Each target must have a
high-margin representation or belong to the low-statistic chart at the
comparable width. This covering hypothesis is not proved here. -/
theorem worstCase_gt_of_rank_or_margin {K : ℕ} {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hr : (r : ℝ) ≤ t) (hKn : n ≤ K)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n / (200 * n * t))
    (hcover : headComputableFunctions n H ⊆
      RelativeMarginQuantifiers.highMarginFunctions n K (MarginCapacityEstimates.testMargin t) ∪
        represented n K r) : H < worstCaseHeadComplexity n := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hwidth' : (K : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * t) := hwidth.trans (by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith)
  have hhigh := MarginCapacityEstimates.card_highMargin_test_at_width hn htlo hthi hwidth'
  have hlow := card_represented_le_half_tables hn htlo hthi hr hKn hwidth
  have hc : (headComputableFunctions n H).ncard ≤ 2 * 2 ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := Set.ncard_le_ncard hcover
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 2 ^ (2 ^ (n - 1)) + 2 ^ (2 ^ (n - 1)) := Nat.add_le_add hhigh hlow
      _ = _ := by omega
  have hpower : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hNhalf : 1 < (2 : ℕ) ^ (n - 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hstrict : 2 * (2 : ℕ) ^ (2 ^ (n - 1)) < 2 ^ (2 ^ n) := by
    rw [show 2 * (2 : ℕ) ^ (2 ^ (n - 1)) = 2 ^ (2 ^ (n - 1) + 1) by
      rw [pow_succ]; omega]
    apply Nat.pow_lt_pow_right (by norm_num)
    omega
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt (hc.trans_lt hstrict)
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

/-- Equivalent exceptional-table formulation: the premise quantifies over
targets for which every comparison-width representation has small margin. -/
theorem worstCase_gt_of_low_margin_shared_statistics {K : ℕ} {t : ℝ}
    (hn : 32 ≤ n) (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hr : (r : ℝ) ≤ t) (hKn : n ≤ K)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n / (200 * n * t))
    (hlow : RelativeMarginQuantifiers.allRepresentationsLowMargin n H K
      (MarginCapacityEstimates.testMargin t) ⊆ represented n K r) :
    H < worstCaseHeadComplexity n := by
  apply worstCase_gt_of_rank_or_margin hn htlo hthi hr hKn hwidth
  intro f hf
  by_cases hg : f ∈ RelativeMarginQuantifiers.highMarginFunctions n K
      (MarginCapacityEstimates.testMargin t)
  · exact Or.inl hg
  · exact Or.inr (hlow ⟨hf, hg⟩)

end HeadComplexity.SharedStatisticsCapacity
