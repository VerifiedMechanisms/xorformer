import HeadComplexity.Atoms.AtomicSampling
import HeadComplexity.Research.PositiveReciprocalExpansion
import HeadComplexity.Research.RelativeMarginQuantifiers
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.ProbabilityMixtureApproximation
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- A two-sided uniform version of the finite empirical sampling theorem.
The coordinate duplication accounts explicitly for the factor two. -/
theorem exists_empirical_approximation
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    [Fintype K] (v : J → K → ℝ) (hv : ∀ j k, |v j k| ≤ 1)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbudget : (2 * Fintype.card K : ℝ) *
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 2) < 1) :
    ∃ sample : Fin m → J, ∀ k : K,
      |finiteProbabilityAverage mu v k -
        (∑ i : Fin m, v (sample i) k) / m| < epsilon := by
  classical
  let v' : J → K × Bool → ℝ := fun j k => v j k.1
  let y : K × Bool → ℝ := fun k => if k.2 then 1 else -1
  have hv' : ∀ j k, |v' j k| ≤ 1 := fun j k => hv j k.1
  have hy : ∀ k, |y k| = 1 := by
    intro k
    rcases k with ⟨k,b⟩
    cases b <;> norm_num [y]
  have hbudget' : (Fintype.card (K × Bool) : ℝ) *
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 2) < 1 := by
    simpa [Fintype.card_prod, mul_comm] using hbudget
  obtain ⟨sample, hs⟩ := exists_empirical_oneSided_approximation_sharp
    mu v' hv' m hm y hy epsilon hepsilon hbudget'
  refine ⟨sample, fun k => ?_⟩
  have hp := hs (k,true)
  have hn := hs (k,false)
  have havg (b : Bool) : finiteProbabilityAverage mu v' (k,b) =
      finiteProbabilityAverage mu v k := rfl
  simp only [y, v', ite_true, one_mul, havg, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hp
  simp only [y, v', Bool.false_eq_true, ite_false, neg_one_mul, havg,
    Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have heq : finiteProbabilityAverage mu v k - (∑ i, v (sample i) k) / m =
      (finiteProbabilityAverage mu v k * m - ∑ i, v (sample i) k) / m := by
    field_simp
  rw [abs_lt]
  rw [heq]
  constructor
  · apply (lt_div_iff₀ hm').mpr
    linarith
  · apply (div_lt_iff₀ hm').mpr
    linarith

/-- The coefficient form of the sampling theorem. All probability and
measurability witnesses are constructed from the finite nonnegative weights. -/
theorem exists_weighted_empirical_approximation
    {J K : Type*} [Fintype J] [Fintype K]
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hcsum : ∑ j, c j = 1)
    (v : J → K → ℝ) (hv : ∀ j k, |v j k| ≤ 1)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbudget : (2 * Fintype.card K : ℝ) *
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 2) < 1) :
    ∃ sample : Fin m → J, ∀ k : K,
      |(∑ j, c j * v j k) - (∑ i : Fin m, v (sample i) k) / m| < epsilon := by
  classical
  let : MeasurableSpace J := ⊤
  have : MeasurableSingletonClass J := ⟨fun _ => trivial⟩
  have hc' : ∑ j, ENNReal.ofReal (c j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hc j), hcsum]
    norm_num
  let p : PMF J := PMF.ofFintype (fun j => ENNReal.ofReal (c j)) hc'
  have ha (k : K) : finiteProbabilityAverage p.toMeasure v k = ∑ j, c j * v j k := by
    rw [finiteProbabilityAverage, PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [p, ENNReal.toReal_ofReal (hc j)]
  obtain ⟨sample, hs⟩ := exists_empirical_approximation
    p.toMeasure v hv m hm epsilon hepsilon hbudget
  exact ⟨sample, fun k => by simpa only [ha] using hs k⟩

/-- Centering unit-interval features gives the sharp range constant in the
two-sided probability budget. -/
theorem exists_weighted_empirical_approximation_unitInterval
    {J K : Type*} [Fintype J] [Fintype K]
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hcsum : ∑ j, c j = 1)
    (v : J → K → ℝ) (hv : ∀ j k, 0 ≤ v j k ∧ v j k ≤ 1)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbudget : (2 * Fintype.card K : ℝ) *
      Real.exp (-2 * (m : ℝ) * epsilon ^ 2) < 1) :
    ∃ sample : Fin m → J, ∀ k : K,
      |(∑ j, c j * v j k) - (∑ i : Fin m, v (sample i) k) / m| < epsilon := by
  classical
  let u : J → K → ℝ := fun j k => 2 * v j k - 1
  have hu : ∀ j k, |u j k| ≤ 1 := by
    intro j k
    rw [abs_le]
    dsimp [u]
    constructor <;> linarith [(hv j k).1, (hv j k).2]
  have hb : (2 * Fintype.card K : ℝ) *
      Real.exp (-((m : ℝ) * (2*epsilon) ^ 2) / 2) < 1 := by
    convert hbudget using 2
    congr 1
    ring
  obtain ⟨sample,hs⟩ := exists_weighted_empirical_approximation
    c hc hcsum u hu m hm (2*epsilon) (by positivity) hb
  refine ⟨sample,fun k => ?_⟩
  have hsum : (∑ j, c j * u j k) = 2*(∑ j,c j*v j k)-1 := by
    dsimp [u]
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hcsum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have heq : (∑ j,c j*u j k)-(∑ i,u (sample i) k)/m =
      2*((∑ j,c j*v j k)-(∑ i,v (sample i) k)/m) := by
    rw [hsum]
    simp only [u, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    field_simp
    ring
  have hh := hs k
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  linarith

/-- Product length does not enter the sample count. Every sampled feature
is an anchored Boolean face, and its average stays in the unit interval. -/
theorem normalized_product_empirical_faces {n : ℕ} {J : Type*} [Fintype J]
    (w : J → Fin n → ℝ) (hw : ∀ j i, 0 ≤ w j i)
    (c : J → ℝ) (hc : ∀ j, 0 < c j)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbudget : (2 * 2 ^ n : ℝ) *
      Real.exp (-2 * (m : ℝ) * epsilon ^ 2) < 1) :
    ∃ sample : Fin m → Finset (Fin n), ∀ x : Fin n → Bool,
      |(∏ j, c j / (c j + ∑ i, w j i * (if x i then 1 else 0))) -
        (∑ i : Fin m, PositiveReciprocalExpansion.face (sample i) x) / m| < epsilon := by
  classical
  obtain ⟨κ,hκ,hκsum,he⟩ :=
    PositiveReciprocalExpansion.normalized_product_probability_expansion w hw c hc
  have hf : ∀ s : Finset (Fin n), ∀ x : Fin n → Bool,
      0 ≤ PositiveReciprocalExpansion.face s x ∧
        PositiveReciprocalExpansion.face s x ≤ 1 := by
    intro s x
    unfold PositiveReciprocalExpansion.face
    split_ifs <;> norm_num
  have hb : (2 * Fintype.card (Fin n → Bool) : ℝ) *
      Real.exp (-2 * (m : ℝ) * epsilon ^ 2) < 1 := by
    simpa using hbudget
  obtain ⟨sample,hs⟩ := exists_weighted_empirical_approximation_unitInterval κ hκ hκsum
    PositiveReciprocalExpansion.face hf m hm epsilon hepsilon hb
  exact ⟨sample,fun x => by rw [he]; exact hs x⟩

/-- Output normalization preserves genuine admissibility and allows
arbitrarily accurate approximation without exceeding unit full-cube norm. -/
theorem exists_normalized_atom {n : ℕ} (g : (Fin n → Bool) → ℝ)
    (hg : UniformlyOneAtomApproximable g) (hbound : ∀ x, |g x| ≤ 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ φ : FracAtom n, (∀ x, |φ.eval x| ≤ 1) ∧
      ∀ x, |φ.eval x - g x| < epsilon := by
  let η := epsilon / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hd : 0 < 1 + η := by linarith
  obtain ⟨θ,hθ⟩ := hg η hη
  let φ := θ.scale (1 / (1 + η))
  have he (x : Fin n → Bool) : φ.eval x = θ.eval x / (1 + η) := by
    simp [φ, div_eq_mul_inv, mul_comm]
  have hθbound (x : Fin n → Bool) : |θ.eval x| ≤ 1 + η := by
    have htriangle := abs_add_le (θ.eval x - g x) (g x)
    rw [sub_add_cancel] at htriangle
    linarith [hθ x, hbound x]
  refine ⟨φ,?_,?_⟩
  · intro x
    rw [he, abs_div, abs_of_pos hd, div_le_one hd]
    exact hθbound x
  · intro x
    have hid : θ.eval x / (1+η) - g x =
        ((θ.eval x-g x)-η*g x)/(1+η) := by field_simp; ring
    rw [he, hid, abs_div, abs_of_pos hd, div_lt_iff₀ hd]
    have hb : |η*g x| ≤ η := by
      rw [abs_mul, abs_of_pos hη]
      simpa using mul_le_mul_of_nonneg_left (hbound x) hη.le
    have ht : |(θ.eval x-g x)-η*g x| ≤ |θ.eval x-g x|+|η*g x| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (θ.eval x-g x) (-(η*g x))
    have hp := mul_pos hepsilon hη
    dsimp [η] at *
    linarith [hθ x]

/-- Averaging finitely many normalized one-head approximants uses exactly
one genuine head per feature and total amplitude at most one. -/
theorem empirical_faces_to_heads {n m : ℕ} (hm : 0 < m)
    (sample : Fin m → Finset (Fin n)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ φ : Fin m → FracAtom n,
      RelativeMarginQuantifiers.amplitude φ 0 ≤ 1 ∧
      ∀ x : Fin n → Bool,
        |RelativeMarginQuantifiers.score φ 0 x -
          (∑ i, PositiveReciprocalExpansion.face (sample i) x) / m| < epsilon := by
  classical
  have hg (i : Fin m) : UniformlyOneAtomApproximable
      (PositiveReciprocalExpansion.face (sample i)) := by
    simpa [affineValue] using
      PositiveReciprocalExpansion.uniformlyOneAtomApproximable_face_affine
        (sample i) 1 (fun _ => 0)
  have hb (i : Fin m) (x : Fin n → Bool) :
      |PositiveReciprocalExpansion.face (sample i) x| ≤ 1 := by
    unfold PositiveReciprocalExpansion.face
    split_ifs <;> norm_num
  choose θ hθnorm hθerr using fun i =>
    exists_normalized_atom _ (hg i) (hb i) epsilon hepsilon
  let φ : Fin m → FracAtom n := fun i => (θ i).scale (1 / m)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have he (i : Fin m) (x : Fin n → Bool) :
      (φ i).eval x = (θ i).eval x / m := by simp [φ, div_eq_mul_inv, mul_comm]
  have hnorm (i : Fin m) : RelativeMarginQuantifiers.atomSup (φ i) ≤ 1 / m := by
    unfold RelativeMarginQuantifiers.atomSup
    apply Finset.sup'_le
    intro x hx
    rw [he, abs_div, abs_of_pos hm']
    exact div_le_div_of_nonneg_right (hθnorm i x) hm'.le
  refine ⟨φ,?_,?_⟩
  · unfold RelativeMarginQuantifiers.amplitude
    simp only [abs_zero, zero_add]
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ)/m := Finset.sum_le_sum fun i _ => hnorm i
      _ = 1 := by simp [hm'.ne']
  · intro x
    have heq : RelativeMarginQuantifiers.score φ 0 x -
        (∑ i, PositiveReciprocalExpansion.face (sample i) x) / m =
        (∑ i, ((θ i).eval x-PositiveReciprocalExpansion.face (sample i) x))/m := by
      simp only [RelativeMarginQuantifiers.score, zero_add, he,
        ← Finset.sum_div, Finset.sum_sub_distrib, sub_div]
    rw [heq, abs_div, abs_of_pos hm', div_lt_iff₀ hm']
    calc
      _ ≤ ∑ i, |(θ i).eval x-PositiveReciprocalExpansion.face (sample i) x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i : Fin m, epsilon := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨⟨0,hm⟩,Finset.mem_univ _⟩
        · intro i hi
          exact hθerr i x
      _ = epsilon * m := by simp [mul_comm]

/-- Arbitrarily many normalized positive-orientation constant-numerator
factors admit a genuine width-`m`, zero-bias approximation of amplitude at
most one. The complete cube, not a sampled set of inputs, is controlled. -/
theorem normalized_product_approximation {n : ℕ} {J : Type*} [Fintype J]
    (w : J → Fin n → ℝ) (hw : ∀ j i, 0 ≤ w j i)
    (c : J → ℝ) (hc : ∀ j, 0 < c j)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hbudget : (2 * 2 ^ n : ℝ) *
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 2) < 1) :
    ∃ φ : Fin m → FracAtom n,
      RelativeMarginQuantifiers.amplitude φ 0 ≤ 1 ∧
      ∀ x : Fin n → Bool,
        |RelativeMarginQuantifiers.score φ 0 x -
          ∏ j, c j / (c j + ∑ i, w j i * (if x i then 1 else 0))| < epsilon := by
  have hb : (2 * 2 ^ n : ℝ) *
      Real.exp (-2 * (m : ℝ) * (epsilon/2) ^ 2) < 1 := by
    convert hbudget using 2
    congr 1
    ring
  obtain ⟨sample,hs⟩ := normalized_product_empirical_faces
    w hw c hc m hm (epsilon/2) (by positivity) hb
  obtain ⟨φ,hφnorm,hφerr⟩ := empirical_faces_to_heads hm sample
    (epsilon/2) (by positivity)
  refine ⟨φ,hφnorm,fun x => ?_⟩
  have ht := abs_sub_le (RelativeMarginQuantifiers.score φ 0 x)
    ((∑ i,PositiveReciprocalExpansion.face (sample i) x)/m)
    (∏ j,c j/(c j+∑ i,w j i*(if x i then 1 else 0)))
  have hh := hs x
  rw [abs_sub_comm] at hh
  linarith [hφerr x]

/-- An explicit logarithmic sample threshold for the preceding theorem. -/
theorem normalized_product_approximation_of_width {n : ℕ} {J : Type*} [Fintype J]
    (w : J → Fin n → ℝ) (hw : ∀ j i, 0 ≤ w j i)
    (c : J → ℝ) (hc : ∀ j, 0 < c j)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hwidth : 2 * Real.log (2 * 2 ^ n : ℝ) / epsilon ^ 2 < m) :
    ∃ φ : Fin m → FracAtom n,
      RelativeMarginQuantifiers.amplitude φ 0 ≤ 1 ∧
      ∀ x : Fin n → Bool,
        |RelativeMarginQuantifiers.score φ 0 x -
          ∏ j, c j / (c j + ∑ i, w j i * (if x i then 1 else 0))| < epsilon := by
  apply normalized_product_approximation w hw c hc m hm epsilon hepsilon
  have hA : (0:ℝ) < 2 * 2 ^ n := by positivity
  have hmul := (div_lt_iff₀ (sq_pos_of_pos hepsilon)).mp hwidth
  have he : -((m:ℝ)*epsilon^2)/2 < -Real.log (2*2^n:ℝ) := by nlinarith
  calc
    _ < (2*2^n:ℝ)*Real.exp (-Real.log (2*2^n:ℝ)) :=
      mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr he) hA
    _ = 1 := by rw [Real.exp_neg, Real.exp_log hA]; exact mul_inv_cancel₀ hA.ne'

/-- A simultaneous complement of all input bits gives the corresponding
common-negative-orientation product, with the same genuine width and norm. -/
theorem normalized_negative_product_approximation_of_width
    {n : ℕ} {J : Type*} [Fintype J]
    (w : J → Fin n → ℝ) (hw : ∀ j i, 0 ≤ w j i)
    (c : J → ℝ) (hc : ∀ j, 0 < c j)
    (m : ℕ) (hm : 0 < m) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hwidth : 2 * Real.log (2 * 2 ^ n : ℝ) / epsilon ^ 2 < m) :
    ∃ φ : Fin m → FracAtom n,
      RelativeMarginQuantifiers.amplitude φ 0 ≤ 1 ∧
      ∀ x : Fin n → Bool,
        |RelativeMarginQuantifiers.score φ 0 x -
          ∏ j, c j / (c j + ∑ i, w j i * (if x i then 0 else 1))| < epsilon := by
  obtain ⟨θ,hθnorm,hθerr⟩ := normalized_product_approximation_of_width
    w hw c hc m hm epsilon hepsilon hwidth
  let φ : Fin m → FracAtom n := fun i => (θ i).flip
  have hs (i : Fin m) : RelativeMarginQuantifiers.atomSup (φ i) ≤
      RelativeMarginQuantifiers.atomSup (θ i) := by
    unfold RelativeMarginQuantifiers.atomSup
    apply Finset.sup'_le
    intro x hx
    simpa only [φ,FracAtom.flip_eval,RelativeMarginQuantifiers.atomSup] using
      RelativeMarginQuantifiers.abs_eval_le_atomSup (θ i) (flipBits x)
  refine ⟨φ,?_,fun x => ?_⟩
  · apply le_trans _ hθnorm
    unfold RelativeMarginQuantifiers.amplitude
    exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => hs i)
  · have hf (i : Fin n) : (if flipBits x i then (1:ℝ) else 0) =
        (if x i then 0 else 1) := by
      cases hxi : x i <;> simp [flipBits,hxi]
    have hh := hθerr (flipBits x)
    simp_rw [hf] at hh
    simpa only [RelativeMarginQuantifiers.score, φ, FracAtom.flip_eval] using hh

end HeadComplexity.ProbabilityMixtureApproximation
