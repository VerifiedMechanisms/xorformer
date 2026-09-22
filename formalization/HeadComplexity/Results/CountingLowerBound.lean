import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Atoms.FracComputableMonotone
import HeadComplexity.Results.LowComplexity
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false

/-!
# Finite counting reduction for worst-case head complexity

The analytic sign-pattern estimate used in the paper is isolated below as a
reusable proposition, not an axiom.  Everything from the exact head model to
the finite family of bounded-degree parameter polynomials, and every ensuing
finite cardinal inequality, is kernel checked.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

/-- Parameters of the relaxed `H`-fraction family: one bias, and a constant
plus `n` linear coefficients for each numerator and denominator. -/
abbrev CountingParameter (n H : ℕ) :=
  Unit ⊕ (Fin H × Bool × Option (Fin n))

theorem card_countingParameter :
    Fintype.card (CountingParameter n H) = 1 + 2 * H * (n + 1) := by
  simp [CountingParameter]
  ring

/-- The universal parameter-affine form evaluated at a fixed cube point.
`kind = false` denotes a numerator and `kind = true` a denominator. -/
noncomputable def countingAffinePoly (kind : Bool) (h : Fin H)
    (x : Fin n → Bool) : MvPolynomial (CountingParameter n H) ℝ :=
  X (Sum.inr (h, kind, none)) +
    ∑ i, C (boolToReal (x i)) * X (Sum.inr (h, kind, some i))

private theorem totalDegree_C_mul_X_le_one
    {m : Type*} (c : ℝ) (i : m) :
    (C c * X i : MvPolynomial m ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

private theorem totalDegree_prod_le_card_general
    {m ι : Type*} (s : Finset ι) (D : ι → MvPolynomial m ℝ)
    (hD : ∀ i, (D i).totalDegree ≤ 1) :
    (∏ i ∈ s, D i).totalDegree ≤ s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun i _ ↦ hD i)).trans ?_
  rw [smul_eq_mul, mul_one]

theorem countingAffinePoly_totalDegree_le (kind : Bool) (h : Fin H)
    (x : Fin n → Bool) :
    (countingAffinePoly kind h x).totalDegree ≤ 1 := by
  unfold countingAffinePoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · exact totalDegree_finsetSum_le fun i _ ↦
      totalDegree_C_mul_X_le_one (boolToReal (x i)) _

/-- The denominator-cleared score, now regarded as a polynomial in the
family coefficients rather than in the Boolean input. -/
noncomputable def countingClearedPoly (x : Fin n → Bool) :
    MvPolynomial (CountingParameter n H) ℝ :=
  X (Sum.inl ()) * ∏ h, countingAffinePoly true h x +
    ∑ h, countingAffinePoly false h x *
      ∏ g ∈ Finset.univ.erase h, countingAffinePoly true g x

/-- Each fixed-input parameter polynomial has degree at most `H + 1`. -/
theorem countingClearedPoly_totalDegree_le (x : Fin n → Bool) :
    (countingClearedPoly (H := H) x).totalDegree ≤ H + 1 := by
  classical
  unfold countingClearedPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have hprod :
        (∏ h : Fin H, countingAffinePoly true h x).totalDegree ≤ H := by
      simpa using totalDegree_prod_le_card_general Finset.univ
        (fun h : Fin H ↦ countingAffinePoly true h x)
        (fun h ↦ countingAffinePoly_totalDegree_le true h x)
    rw [totalDegree_X]
    omega
  · refine totalDegree_finsetSum_le fun h _ ↦ ?_
    refine (totalDegree_mul _ _).trans ?_
    have hprod :
        (∏ g ∈ Finset.univ.erase h,
          countingAffinePoly true g x).totalDegree ≤ H - 1 := by
      refine (totalDegree_prod_le_card_general (Finset.univ.erase h)
        (fun g ↦ countingAffinePoly true g x)
        (fun g ↦ countingAffinePoly_totalDegree_le true g x)).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin]
    have ha := countingAffinePoly_totalDegree_le false h x
    omega

/-- Coefficient vector associated with an abstract affine fraction family. -/
noncomputable def countingParameterPoint
    (A : AffineFractionFamily n H) (c : ℝ) : CountingParameter n H → ℝ
  | Sum.inl _ => c
  | Sum.inr (h, false, none) => (A.num h).coeff 0
  | Sum.inr (h, false, some i) =>
      (A.num h).coeff (Finsupp.single i 1)
  | Sum.inr (h, true, none) => (A.den h).coeff 0
  | Sum.inr (h, true, some i) =>
      (A.den h).coeff (Finsupp.single i 1)

theorem eval_countingAffinePoly_false
    (A : AffineFractionFamily n H) (c : ℝ) (h : Fin H)
    (x : Fin n → Bool) :
    eval (countingParameterPoint A c) (countingAffinePoly false h x) =
      eval (cubePoint x) (A.num h) := by
  rw [eval_cubePoint_affine (A.num h) (A.num_degree h)]
  simp [countingAffinePoly, countingParameterPoint, mul_comm]

theorem eval_countingAffinePoly_true
    (A : AffineFractionFamily n H) (c : ℝ) (h : Fin H)
    (x : Fin n → Bool) :
    eval (countingParameterPoint A c) (countingAffinePoly true h x) =
      eval (cubePoint x) (A.den h) := by
  rw [eval_cubePoint_affine (A.den h) (A.den_degree h)]
  simp [countingAffinePoly, countingParameterPoint, mul_comm]

/-- The universal parameter polynomial specializes exactly to the cleared
affine score. -/
theorem eval_countingClearedPoly
    (A : AffineFractionFamily n H) (c : ℝ) (x : Fin n → Bool) :
    eval (countingParameterPoint A c) (countingClearedPoly x) =
      eval (cubePoint x) (clearedAffinePoly A c) := by
  classical
  simp only [countingClearedPoly, clearedAffinePoly, map_add, map_mul,
    map_prod, map_sum, eval_X, eval_C]
  simp_rw [eval_countingAffinePoly_false A c]
  simp_rw [eval_countingAffinePoly_true A c]
  simp [countingParameterPoint]

/-- A Boolean vector is a strict sign pattern of a polynomial family. -/
def StrictPolynomialSignPattern {I K : Type*}
    (P : I → MvPolynomial K ℝ) (f : I → Bool) : Prop :=
  ∃ θ : K → ℝ, ∀ x,
    if f x then 0 < eval θ (P x) else eval θ (P x) < 0

/-- Set of all strict sign patterns realized by a polynomial family.  It is
finite whenever the input type is finite. -/
def strictPolynomialSignPatterns {I K : Type*}
    (P : I → MvPolynomial K ℝ) : Set (I → Bool) :=
  {f | StrictPolynomialSignPattern P f}

/-- Set of Boolean functions computable with at most `H` heads. -/
def headComputableFunctions (n H : ℕ) :
    Set ((Fin n → Bool) → Bool) :=
  {f | computableWithHeadsN n H f}

theorem mem_strictPatterns_of_computable
    {f : (Fin n → Bool) → Bool} (hf : computableWithHeadsN n H f) :
    f ∈ strictPolynomialSignPatterns
      (fun x ↦ countingClearedPoly (H := H) x) := by
  classical
  obtain ⟨phi, c, hscore⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hf)
  let A := FracAtom.affineFamily phi
  refine ⟨countingParameterPoint A c, fun x ↦ ?_⟩
  rw [eval_countingClearedPoly A c]
  change if f x then 0 < eval (cubePoint x) (clearedAtomPoly phi c)
    else eval (cubePoint x) (clearedAtomPoly phi c) < 0
  rw [clearedAtomPoly_eval]
  cases hfx : f x with
  | false =>
      have hs := hscore x
      rw [hfx] at hs
      exact mul_neg_of_pos_of_neg (atomDenProduct_eval_pos phi x) hs
  | true =>
      have hs := hscore x
      rw [hfx] at hs
      exact mul_pos (atomDenProduct_eval_pos phi x) hs

/-- The exact unconditional reduction: head-computable functions inject into
strict sign patterns of `2^n` degree-`H+1` polynomials in
`1 + 2H(n+1)` variables. -/
theorem card_headComputableFunctions_le_strictPatterns :
    (headComputableFunctions n H).ncard ≤
      (strictPolynomialSignPatterns
        (fun x : Fin n → Bool ↦ countingClearedPoly (H := H) x)).ncard := by
  classical
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro f hf
  exact mem_strictPatterns_of_computable hf

/-- A reusable, axiom-free interface for an external multivariate strict
sign-pattern estimate. -/
def StrictSignPatternBound (N d p B : ℕ) : Prop :=
  ∀ (I K : Type) [Fintype I] [Fintype K]
    (P : I → MvPolynomial K ℝ),
    Fintype.card I = N → Fintype.card K = p →
    (∀ x, (P x).totalDegree ≤ d) →
    (strictPolynomialSignPatterns P).ncard ≤ B

/-- Exact real-valued interface for the missing analytic theorem.  Supplying a
proof of this proposition is precisely supplying Warren's strict sign-pattern
bound; no such proof or axiom is introduced here. -/
def WarrenStrictSignPatternBound : Prop :=
  ∀ N d p, 0 < d → 0 < p → p ≤ N →
    ∀ (I K : Type) [Fintype I] [Fintype K]
      (P : I → MvPolynomial K ℝ),
      Fintype.card I = N → Fintype.card K = p →
      (∀ x, (P x).totalDegree ≤ d) →
      ((strictPolynomialSignPatterns P).ncard : ℝ) ≤
        ((4 * Real.exp 1 * d * N / p : ℝ) ^ p)

/-- A convenient coarse Warren interface.  The standard theorem with
`(4 e d N / p)^p`, for `p ≤ N`, implies this integer bound because
`e < 3` and `p ≥ 1`. -/
def CoarseWarrenSignPatternBound : Prop :=
  ∀ N d p, 0 < d → 0 < p → p ≤ N →
    StrictSignPatternBound N d p ((12 * d * N) ^ p)

/-- The exact Warren estimate implies the coarse natural-number interface
used for the elementary power-of-two bookkeeping below. -/
theorem coarseWarrenSignPatternBound_of_warren
    (hWarren : WarrenStrictSignPatternBound) :
    CoarseWarrenSignPatternBound := by
  intro N d p hd hp hpN I K _ _ P hI hK hdegree
  have hreal := hWarren N d p hd hp hpN I K P hI hK hdegree
  have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnonneg : 0 ≤ 4 * Real.exp 1 * (d : ℝ) * (N : ℝ) := by positivity
  have hpNonneg : (0 : ℝ) ≤ p := by positivity
  have hbase :
      4 * Real.exp 1 * (d : ℝ) * (N : ℝ) / (p : ℝ) ≤
        12 * (d : ℝ) * (N : ℝ) := by
    calc
      4 * Real.exp 1 * (d : ℝ) * (N : ℝ) / (p : ℝ) ≤
          4 * Real.exp 1 * (d : ℝ) * (N : ℝ) :=
        div_le_self hnonneg hpReal
      _ ≤ 4 * 3 * (d : ℝ) * (N : ℝ) := by
        gcongr
        exact Real.exp_one_lt_three.le
      _ = 12 * (d : ℝ) * (N : ℝ) := by ring
  have hreal' :
      ((strictPolynomialSignPatterns P).ncard : ℝ) ≤
        (12 * (d : ℝ) * (N : ℝ)) ^ p :=
    hreal.trans (pow_le_pow_left₀ (div_nonneg hnonneg hpNonneg) hbase p)
  exact_mod_cast hreal'

/-- Any supplied sign-pattern certificate immediately bounds the number of
head-computable Boolean functions. -/
theorem card_headComputableFunctions_le_of_signPatternBound
    {B : ℕ}
    (hbound : StrictSignPatternBound (2 ^ n) (H + 1)
      (1 + 2 * H * (n + 1)) B) :
    (headComputableFunctions n H).ncard ≤ B := by
  refine card_headComputableFunctions_le_strictPatterns.trans ?_
  apply hbound (Fin n → Bool) (CountingParameter n H)
    (fun x ↦ countingClearedPoly (H := H) x)
  · simp [Fintype.card_bool]
  · exact card_countingParameter
  · exact countingClearedPoly_totalDegree_le

/-- Faithful specialization of Warren's theorem to the relaxed head family,
before any coarse integer estimates are made. -/
theorem card_headComputableFunctions_le_warren
    (hWarren : WarrenStrictSignPatternBound)
    (hparameters : 1 + 2 * H * (n + 1) ≤ 2 ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      ((4 * Real.exp 1 * ((H + 1 : ℕ) : ℝ) * ((2 ^ n : ℕ) : ℝ) /
        ((1 + 2 * H * (n + 1) : ℕ) : ℝ)) ^
        (1 + 2 * H * (n + 1))) := by
  let P : (Fin n → Bool) → MvPolynomial (CountingParameter n H) ℝ :=
    fun x ↦ countingClearedPoly (H := H) x
  calc
    ((headComputableFunctions n H).ncard : ℝ) ≤
        ((strictPolynomialSignPatterns P).ncard : ℝ) := by
      exact_mod_cast card_headComputableFunctions_le_strictPatterns
    _ ≤ ((4 * Real.exp 1 * ((H + 1 : ℕ) : ℝ) * ((2 ^ n : ℕ) : ℝ) /
          ((1 + 2 * H * (n + 1) : ℕ) : ℝ)) ^
          (1 + 2 * H * (n + 1))) := by
      apply hWarren (2 ^ n) (H + 1) (1 + 2 * H * (n + 1))
      · omega
      · omega
      · exact hparameters
      · simp [Fintype.card_bool]
      · exact card_countingParameter
      · intro x
        exact countingClearedPoly_totalDegree_le x

/-- The direct finite Warren consequence in the parameter regime where the
number of fixed-input polynomials dominates the number of parameters. -/
theorem card_headComputableFunctions_le_coarseWarren
    (hWarren : CoarseWarrenSignPatternBound)
    (hparameters : 1 + 2 * H * (n + 1) ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard ≤
      (12 * (H + 1) * 2 ^ n) ^ (1 + 2 * H * (n + 1)) := by
  apply card_headComputableFunctions_le_of_signPatternBound
  exact hWarren (2 ^ n) (H + 1) (1 + 2 * H * (n + 1))
    (by omega) (by omega) hparameters

/-- There are exactly `2^(2^n)` Boolean functions on the `n`-cube. -/
theorem card_all_booleanFunctions (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  simp [Fintype.card_bool]

/-- The unconditional fallback used outside the Warren regime. -/
theorem card_headComputableFunctions_le_all :
    (headComputableFunctions n H).ncard ≤ 2 ^ (2 ^ n) := by
  classical
  calc
    (headComputableFunctions n H).ncard ≤
        Nat.card ((Fin n → Bool) → Bool) :=
      Set.ncard_le_card (headComputableFunctions n H)
    _ = 2 ^ (2 ^ n) := by
      rw [Nat.card_eq_fintype_card, card_all_booleanFunctions]

private theorem countingParameterCount_le (hn : 1 ≤ n) (hH : 1 ≤ H) :
    1 + 2 * H * (n + 1) ≤ 5 * n * H := by
  have hone : 1 ≤ n * H := Nat.mul_pos (by omega) (by omega)
  have hnadd : n + 1 ≤ 2 * n := by omega
  have hmain : 2 * H * (n + 1) ≤ 4 * n * H := by
    calc
      2 * H * (n + 1) ≤ 2 * H * (2 * n) :=
        Nat.mul_le_mul_left (2 * H) hnadd
      _ = 4 * n * H := by ring
  calc
    1 + 2 * H * (n + 1) ≤ n * H + 4 * n * H :=
      Nat.add_le_add hone hmain
    _ = 5 * n * H := by ring

private theorem coarseWarrenBase_le (hHpow : H ≤ 2 ^ n) :
    12 * (H + 1) * 2 ^ n ≤ 2 ^ (2 * n + 5) := by
  have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hsucc : H + 1 ≤ 2 ^ (n + 1) := by
    calc
      H + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right hHpow 1
      _ ≤ 2 ^ n * 2 := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]
  calc
    12 * (H + 1) * 2 ^ n ≤ 16 * 2 ^ (n + 1) * 2 ^ n := by
      gcongr
      norm_num
    _ = 2 ^ (2 * n + 5) := by
      rw [show 16 = 2 ^ 4 by norm_num, ← pow_add, ← pow_add]
      congr 1
      omega

private theorem coarseWarrenExponent_le (hn : 1 ≤ n) (hH : 1 ≤ H) :
    (2 * n + 5) * (1 + 2 * H * (n + 1)) ≤ 35 * n * n * H := by
  calc
    (2 * n + 5) * (1 + 2 * H * (n + 1)) ≤
        (7 * n) * (5 * n * H) :=
      Nat.mul_le_mul (by omega) (countingParameterCount_le hn hH)
    _ = 35 * n * n * H := by ring

/-- Conditional quantitative counting theorem, with an explicit absolute
constant.  This is the finite statement behind the paper's
`2^(O(n^2 H))` estimate. -/
theorem card_headComputableFunctions_le_two_pow
    (hWarren : CoarseWarrenSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard ≤ 2 ^ (35 * n * n * H) := by
  by_cases hp : 1 + 2 * H * (n + 1) ≤ 2 ^ n
  · refine (card_headComputableFunctions_le_coarseWarren hWarren hp).trans ?_
    calc
      (12 * (H + 1) * 2 ^ n) ^ (1 + 2 * H * (n + 1)) ≤
          (2 ^ (2 * n + 5)) ^ (1 + 2 * H * (n + 1)) :=
        Nat.pow_le_pow_left (coarseWarrenBase_le hHpow) _
      _ = 2 ^ ((2 * n + 5) * (1 + 2 * H * (n + 1))) := by
        rw [pow_mul]
      _ ≤ 2 ^ (35 * n * n * H) :=
        Nat.pow_le_pow_right (by norm_num) (coarseWarrenExponent_le hn hH)
  · refine card_headComputableFunctions_le_all.trans ?_
    apply Nat.pow_le_pow_right (by norm_num)
    have hp' : 2 ^ n < 1 + 2 * H * (n + 1) := Nat.lt_of_not_ge hp
    calc
      2 ^ n ≤ 1 + 2 * H * (n + 1) := hp'.le
      _ ≤ 5 * n * H := countingParameterCount_le hn hH
      _ = 5 * (n * H) := by ring
      _ ≤ (35 * n) * (n * H) :=
        Nat.mul_le_mul_right (n * H) (by omega)
      _ = 35 * n * n * H := by ring

theorem card_headComputableFunctions_le_two_pow_of_warren
    (hWarren : WarrenStrictSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard ≤ 2 ^ (35 * n * n * H) :=
  card_headComputableFunctions_le_two_pow
    (coarseWarrenSignPatternBound_of_warren hWarren) hn hH hHpow

/-- Multiplicative form of the density estimate.  Dividing both sides by the
exact total `2^(2^n)` says that the computable fraction is at most
`2^(-(2^n - 35 n^2 H))`. -/
theorem card_headComputableFunctions_mul_deficit_le_all
    (hWarren : CoarseWarrenSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hexponent : 35 * n * n * H ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard *
        2 ^ (2 ^ n - 35 * n * n * H) ≤ 2 ^ (2 ^ n) := by
  calc
    (headComputableFunctions n H).ncard *
          2 ^ (2 ^ n - 35 * n * n * H) ≤
        2 ^ (35 * n * n * H) *
          2 ^ (2 ^ n - 35 * n * n * H) :=
      Nat.mul_le_mul_right _
        (card_headComputableFunctions_le_two_pow hWarren hn hH hHpow)
    _ = 2 ^ (35 * n * n * H + (2 ^ n - 35 * n * n * H)) := by
      rw [pow_add]
    _ = 2 ^ (2 ^ n) := by rw [Nat.add_sub_of_le hexponent]

theorem card_headComputableFunctions_mul_deficit_le_all_of_warren
    (hWarren : WarrenStrictSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hexponent : 35 * n * n * H ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard *
        2 ^ (2 ^ n - 35 * n * n * H) ≤ 2 ^ (2 ^ n) :=
  card_headComputableFunctions_mul_deficit_le_all
    (coarseWarrenSignPatternBound_of_warren hWarren)
    hn hH hHpow hexponent

/-- If fewer than all truth tables are `H`-head computable, one truth table
has head complexity strictly greater than `H`. -/
theorem exists_HStar_gt_of_card_lt
    (hcard : (headComputableFunctions n H).ncard < 2 ^ (2 ^ n)) :
    ∃ f : (Fin n → Bool) → Bool, H < HStar n f := by
  classical
  have hmissing : ∃ f : (Fin n → Bool) → Bool,
      ¬ computableWithHeadsN n H f := by
    by_contra hall
    push Not at hall
    have hset : headComputableFunctions n H = Set.univ :=
      Set.eq_univ_of_forall hall
    have hfull : (headComputableFunctions n H).ncard = 2 ^ (2 ^ n) := by
      rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card,
        card_all_booleanFunctions]
    omega
  obtain ⟨f, hf⟩ := hmissing
  refine ⟨f, ?_⟩
  by_contra hle
  exact hf (computableWithHeadsN_mono (Nat.le_of_not_gt hle)
    (HStar_computable f))

/-- Explicit finite worst-case consequence of the coarse Warren estimate. -/
theorem exists_HStar_gt_of_coarseWarren
    (hWarren : CoarseWarrenSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hsmall : 35 * n * n * H < 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, H < HStar n f := by
  apply exists_HStar_gt_of_card_lt
  exact (card_headComputableFunctions_le_two_pow hWarren hn hH hHpow).trans_lt
    (Nat.pow_lt_pow_right (by norm_num) hsmall)

theorem exists_HStar_gt_of_warren
    (hWarren : WarrenStrictSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hsmall : 35 * n * n * H < 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, H < HStar n f :=
  exists_HStar_gt_of_coarseWarren
    (coarseWarrenSignPatternBound_of_warren hWarren)
    hn hH hHpow hsmall

/-- Maximum head complexity among all Boolean functions on the `n`-cube. -/
noncomputable def worstCaseHeadComplexity (n : ℕ) : ℕ :=
  Finset.univ.sup (HStar n)

theorem HStar_le_worstCaseHeadComplexity
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ worstCaseHeadComplexity n := by
  classical
  exact Finset.le_sup (f := HStar n) (Finset.mem_univ f)

/-- The universal interpolation construction gives the matching elementary
worst-case upper bound used in the theorem note. -/
theorem worstCaseHeadComplexity_le :
    worstCaseHeadComplexity n ≤ 2 ^ n - 1 := by
  classical
  apply Finset.sup_le
  intro f _
  exact HStar_le_of_computableWithHeadsN (universal_computable f)

/-- Explicit finite version of the worst-case `Omega(2^n/n^2)` conclusion.
The sole non-kernel analytic premise remains `hWarren`. -/
theorem worstCaseHeadComplexity_gt_of_coarseWarren
    (hWarren : CoarseWarrenSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hsmall : 35 * n * n * H < 2 ^ n) :
    H < worstCaseHeadComplexity n := by
  obtain ⟨f, hf⟩ :=
    exists_HStar_gt_of_coarseWarren hWarren hn hH hHpow hsmall
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

/-- Same finite lower bound with precisely Warren's theorem as its only
external premise. -/
theorem worstCaseHeadComplexity_gt_of_warren
    (hWarren : WarrenStrictSignPatternBound)
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hsmall : 35 * n * n * H < 2 ^ n) :
    H < worstCaseHeadComplexity n :=
  worstCaseHeadComplexity_gt_of_coarseWarren
    (coarseWarrenSignPatternBound_of_warren hWarren) hn hH hHpow hsmall

/-- A direct division-form lower bound.  The mild size hypothesis only says
that the displayed integer lower bound is nonzero. -/
theorem worstCaseHeadComplexity_gt_div_of_warren
    (hWarren : WarrenStrictSignPatternBound)
    (hn : 1 ≤ n)
    (hsize : 35 * n * n ≤ 2 ^ n - 1) :
    (2 ^ n - 1) / (35 * n * n) < worstCaseHeadComplexity n := by
  have hdenom : 0 < 35 * n * n := by positivity
  have hheads : 1 ≤ (2 ^ n - 1) / (35 * n * n) := by
    apply (Nat.le_div_iff_mul_le hdenom).2
    simpa using hsize
  have hheadsPow : (2 ^ n - 1) / (35 * n * n) ≤ 2 ^ n :=
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hsmall :
      35 * n * n * ((2 ^ n - 1) / (35 * n * n)) < 2 ^ n := by
    calc
      35 * n * n * ((2 ^ n - 1) / (35 * n * n)) =
          ((2 ^ n - 1) / (35 * n * n)) * (35 * n * n) := by ring
      _ ≤ 2 ^ n - 1 := Nat.div_mul_le_self _ _
      _ < 2 ^ n := by
        have : 0 < 2 ^ n := pow_pos (by norm_num) _
        omega
  exact worstCaseHeadComplexity_gt_of_warren hWarren hn hheads hheadsPow hsmall

end HeadComplexity
