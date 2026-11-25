import HeadComplexity.Research.SharedStatisticsCapacity

set_option linter.style.header false

/-!
Weighted capacity for polynomially parameterized denominators. This is a
comparison-class theorem. It does not assert access from unrestricted heads.
-/

noncomputable section
namespace HeadComplexity.LowParameterDenominatorCapacity
open Finset MvPolynomial PolynomialRootCount
open scoped BigOperators
variable {n H q : ℕ}

abbrev Parameter (n H q : ℕ) := (Fin H × Fin n) ⊕ Fin q

@[simp] theorem card_parameter : Fintype.card (Parameter n H q) = n * H + q := by
  simp [Parameter, Nat.mul_comm]

def parameterWeight (k : ℕ) : Parameter n H q → ℕ
  | Sum.inl _ => k
  | Sum.inr _ => 1

def numPoly (h : Fin H) (x : Fin n → Bool) : MvPolynomial (Parameter n H q) ℝ :=
  ∑ i, C (boolToReal (x i)) * X (Sum.inl (h, i))

def clearedPoly (D : Fin H → (Fin n → Bool) → MvPolynomial (Parameter n H q) ℝ)
    (s : Bool) (x : Fin n → Bool) : MvPolynomial (Parameter n H q) ℝ :=
  C (if s then 1 else -1) * ∏ h, D h x +
    ∑ h, numPoly h x * ∏ g ∈ Finset.univ.erase h, D g x

theorem numPoly_weighted (k : ℕ) (h : Fin H) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (numPoly (q := q) h x) k := by
  apply weightedDegreeLE_sum
  intro i _
  apply weightedDegreeLE_C_mul
  simpa [parameterWeight] using
    (weightedDegreeLE_X (R := ℝ) (parameterWeight (n := n) (H := H) (q := q) k)
      (Sum.inl (h, i)))

variable (D : Fin H → (Fin n → Bool) → MvPolynomial (Parameter n H q) ℝ)

theorem denProd_weighted (k : ℕ)
    (hD : ∀ h x, WeightedDegreeLE (parameterWeight k) (D h x) 2)
    (I : Finset (Fin H)) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (∏ h ∈ I, D h x) (2 * I.card) := by
  simpa [Nat.mul_comm] using weightedDegreeLE_prod I (D := fun _ ↦ 2)
    (fun h _ ↦ hD h x)

theorem clearedPoly_weighted (k : ℕ) (hk : 2 ≤ k) (hH : 0 < H)
    (hD : ∀ h x, WeightedDegreeLE (parameterWeight k) (D h x) 2)
    (s : Bool) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (clearedPoly D s x) (2 * H + k - 2) := by
  classical
  apply weightedDegreeLE_add
  · apply weightedDegreeLE_mono
      (weightedDegreeLE_C_mul _ (denProd_weighted D k hD Finset.univ x))
    simp only [Finset.card_fin]
    omega
  · apply weightedDegreeLE_sum
    intro h _
    have hd := denProd_weighted D k hD (Finset.univ.erase h) x
    rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin] at hd
    exact weightedDegreeLE_mono (weightedDegreeLE_mul (numPoly_weighted k h x) hd)
      (by omega)

theorem product_parameter_weights (k : ℕ) :
    (∏ i : Parameter n H q, (parameterWeight k i : ℝ)) = (k : ℝ) ^ (n * H) := by
  simp [Parameter, Fintype.prod_sum_type, parameterWeight, Nat.mul_comm]

def represented : Set ((Fin n → Bool) → Bool) :=
  strictPolynomialSignPatterns (clearedPoly D false) ∪
    strictPolynomialSignPatterns (clearedPoly D true)

theorem card_represented_le (k : ℕ) (hk : 2 ≤ k)
    (hD : ∀ h x, WeightedDegreeLE (parameterWeight k) (D h x) 2)
    (hn : 0 < n) (hH : 0 < H) (hp : n * H + q ≤ 2 ^ n) :
    ((represented D).ncard : ℝ) ≤
      2 * (4 * Real.exp 1 * (2 * H + k - 2 : ℕ) * (2 : ℝ) ^ n /
        (n * H + q)) ^ (n * H + q) /
          (k : ℝ) ^ (n * H) := by
  have hc (s : Bool) := weightedStrictPolynomialSignPatterns_card_le
    (K := Parameter n H q) (by rw [card_parameter]; positivity)
    (by rw [card_parameter]
        simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hp)
    (parameterWeight k)
    (fun i ↦ by rcases i with i | i <;> simp [parameterWeight]; omega)
    (fun i ↦ by rcases i with i | i <;> simp [parameterWeight] <;> omega)
    (clearedPoly D s) (clearedPoly_weighted D k hk hH hD s)
  have hb (s : Bool) :
      ((strictPolynomialSignPatterns
        (clearedPoly D s)).ncard : ℝ) ≤
        (4 * Real.exp 1 * (2 * H + k - 2 : ℕ) * (2 : ℝ) ^ n /
          (n * H + q)) ^ (n * H + q) /
            (k : ℝ) ^ (n * H) := by
    simpa only [card_parameter, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, product_parameter_weights, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow] using hc s
  have ht : ((represented D).ncard : ℝ) ≤
      ((strictPolynomialSignPatterns
        (clearedPoly D false)).ncard : ℝ) +
      ((strictPolynomialSignPatterns
        (clearedPoly D true)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_union_le
      (strictPolynomialSignPatterns (clearedPoly D false))
      (strictPolynomialSignPatterns (clearedPoly D true))
  calc
    _ ≤ _ := ht.trans (add_le_add (hb false) (hb true))
    _ = _ := by ring

theorem card_represented_le_exp
    (hD : ∀ h x, WeightedDegreeLE (parameterWeight (2 * H)) (D h x) 2)
    (hn : 0 < n) (hH : 0 < H)
    (hp : n * H + q ≤ 2 ^ n) :
    ((represented D).ncard : ℝ) ≤
      Real.exp (Real.log 2 + (q : ℝ) *
        Real.log (16 * Real.exp 1 * (2 : ℝ) ^ n / n) +
        ((n : ℝ) * H) * Real.log (8 * Real.exp 1 * (2 : ℝ) ^ n / (n * H))) := by
  let p := n * H + q
  let m := n * H
  let B := 16 * Real.exp 1 * (2 : ℝ) ^ n / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hpR : (0 : ℝ) < p := by dsimp [p]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hpmin : (n : ℝ) * H ≤ p := by
    dsimp [p]
    push_cast
    exact le_add_of_nonneg_right (Nat.cast_nonneg q)
  have hdegree : ((2 * H + 2 * H - 2 : ℕ) : ℝ) ≤ 4 * (H : ℝ) := by
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
    have hd := mul_le_mul_of_nonneg_left hdegree
      (show 0 ≤ 4 * Real.exp 1 * (2 : ℝ) ^ n by positivity)
    nlinarith
  have hc := card_represented_le D (2 * H) (by omega) hD hn hH hp
  have hc' : ((represented D).ncard : ℝ) ≤
      2 * B ^ p / (2 * (H : ℝ)) ^ m := by
    refine hc.trans ?_
    change 2 * _ ^ p / ((2 * H : ℕ) : ℝ) ^ m ≤ _
    push_cast
    gcongr
    simpa [p] using hb
  have heq : Real.exp (Real.log 2 + (p : ℝ) * Real.log B -
      (m : ℝ) * Real.log (2 * (H : ℝ))) = 2 * B ^ p / (2 * (H : ℝ)) ^ m := by
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
  dsimp [p, m, B]
  push_cast
  ring


theorem card_represented_le_exp_at_budget {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hqpar : (q : ℝ) ≤ 2 * t * H) (hH : 0 < H)
    (hD : ∀ h x, WeightedDegreeLE (parameterWeight (2 * H)) (D h x) 2)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t)) :
    ((represented D).ncard : ℝ) ≤ Real.exp (3 * (2 : ℝ) ^ n / 10) := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have htpos : 0 < t := by linarith
  have hbudget := (le_div_iff₀ (by positivity : 0 < 400 * (n : ℝ) * t)).mp hwidth
  have hq : (n : ℝ) * H ≤ (2 : ℝ) ^ n / (25 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 25 * t)).mpr
    nlinarith [show 0 ≤ (n : ℝ) * H * t by positivity]
  have hp : n * H + q ≤ 2 ^ n := by
    have hpar : (q : ℝ) ≤ 2 * n * H := hqpar.trans (by gcongr)
    have hqN : 3 * ((n : ℝ) * H) ≤ (2 : ℝ) ^ n := by
      nlinarith [mul_le_mul_of_nonneg_left ht1 (show 0 ≤ (n : ℝ) * H by positivity)]
    exact_mod_cast (show (n : ℝ) * H + q ≤ (2 : ℝ) ^ n by linarith)
  have he := MarginCapacityEstimates.entropy_bound (K := 0) hnR
    (by positivity : 0 < (2 : ℝ) ^ n) (le_refl 0)
    (by positivity : 0 < (n : ℝ) * H) (by norm_num : (0 : ℝ) < 2)
    htlo hthi (by positivity) hq (by
      have hexp : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr htpos.le
      nlinarith : (2 : ℝ) ≤ 6 * ((n : ℝ) + 1) * Real.exp t)
  simp only [zero_mul, zero_add] at he
  have hfirst : (q : ℝ) *
      Real.log (16 * Real.exp 1 * (2 : ℝ) ^ n / n) ≤ (2 : ℝ) ^ n / 100 := by
    have hm := mul_le_mul_of_nonneg_left (SharedStatisticsCapacity.log_base_le hn)
      (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    have hm2 := mul_le_mul_of_nonneg_right hqpar (show 0 ≤ 2 * (n : ℝ) by positivity)
    nlinarith
  have hlog2 : Real.log (2 : ℝ) ≤ (2 : ℝ) ^ n / 100 := by
    have hN : (128 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
        (show 7 ≤ n by omega))
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  refine (card_represented_le_exp D hD (by omega) hH hp).trans (Real.exp_le_exp.mpr ?_)
  have harg : 4 * Real.exp 1 * 2 * (2 : ℝ) ^ n =
      8 * Real.exp 1 * (2 : ℝ) ^ n := by ring
  rw [harg] at he
  linarith

theorem card_represented_le_half_tables {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hqpar : (q : ℝ) ≤ 2 * t * H) (hH : 0 < H)
    (hD : ∀ h x, WeightedDegreeLE (parameterWeight (2 * H)) (D h x) 2)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t)) :
    (represented D).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hc := card_represented_le_exp_at_budget D hn htlo hthi hqpar hH hD hwidth
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hlog : (3 : ℝ) / 5 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : 3 * (2 : ℝ) ^ n / 10 ≤ ((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (n - 1) by positivity)]
  have hreal : ((represented D).ncard : ℝ) ≤ (2 : ℝ) ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := hc
      _ ≤ Real.exp (((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hreal


/-- A union over target-dependent denominator charts costs their number. -/
theorem card_chart_union_le_exp {ι : Type*} [Fintype ι]
    (Ds : ι → Fin H → (Fin n → Bool) → MvPolynomial (Parameter n H q) ℝ)
    {t : ℝ} (hn : 32 ≤ n) (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hqpar : (q : ℝ) ≤ 2 * t * H) (hH : 0 < H)
    (hD : ∀ a h x, WeightedDegreeLE (parameterWeight (2 * H)) (Ds a h x) 2)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t))
    (hcharts : (Fintype.card ι : ℝ) ≤ Real.exp ((2 : ℝ) ^ n / 50)) :
    ((⋃ a, represented (Ds a)).ncard : ℝ) ≤ Real.exp (8 * (2 : ℝ) ^ n / 25) := by
  classical
  have hc (a : ι) := card_represented_le_exp_at_budget (Ds a) hn htlo hthi
    hqpar hH (hD a) hwidth
  have hu : ((⋃ a, represented (Ds a)).ncard : ℝ) ≤
      ∑ a, ((represented (Ds a)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_iUnion_le_of_fintype (fun a ↦ represented (Ds a))
  calc
    _ ≤ _ := hu
    _ ≤ ∑ _a : ι, Real.exp (3 * (2 : ℝ) ^ n / 10) := Finset.sum_le_sum (fun a _ ↦ hc a)
    _ = (Fintype.card ι : ℝ) * Real.exp (3 * (2 : ℝ) ^ n / 10) := by simp
    _ ≤ Real.exp ((2 : ℝ) ^ n / 50) * Real.exp (3 * (2 : ℝ) ^ n / 10) := by gcongr
    _ = Real.exp (8 * (2 : ℝ) ^ n / 25) := by rw [← Real.exp_add]; congr 1; ring

end HeadComplexity.LowParameterDenominatorCapacity
