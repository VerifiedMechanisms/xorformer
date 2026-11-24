import HeadComplexity.Research.AffineProductCapacity
import HeadComplexity.Research.OriginalMarginCapacity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.style.header false

/-!
A margin-free compiler from the original model to affine-product scores.
The width 2^H-1 is exponential in the original head count and does not give
an improvement at the critical widths. No margin or coefficient bound is used.
-/

noncomputable section
namespace HeadComplexity.FiniteDifferenceProductCompiler
open Finset Filter
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Differentiating the elementary product expansion groups all equal
exponential directions before they are counted. -/
theorem weighted_prod_sub_expansion (s : Finset ι) (a z : ι → ℝ) :
    (∑ h ∈ s, a h * ∏ g ∈ s.erase h, (z g - 1)) =
      ∑ v ∈ s.powerset, ((-1 : ℝ) ^ (v.card - 1) * ∑ h ∈ v, a h) *
        ∏ g ∈ s \ v, z g := by
  have hleft : HasDerivAt (fun t : ℝ => ∏ h ∈ s, ((t * a h - 1) + z h))
      (∑ h ∈ s, a h * ∏ g ∈ s.erase h, (z g - 1)) 0 := by
    have hh : ∀ h ∈ s, HasDerivAt (fun t : ℝ => (t * a h - 1) + z h) (a h) 0 := by
      intro h _
      convert (((hasDerivAt_id (0 : ℝ)).mul_const (a h)).sub_const 1).add_const (z h)
        using 1 <;> simp
    simpa [smul_eq_mul, mul_comm, sub_eq_add_neg, add_comm] using
      HasDerivAt.fun_finsetProd hh
  have hv (v : Finset ι) : HasDerivAt (fun t : ℝ => ∏ h ∈ v, (t * a h - 1))
      ((-1 : ℝ) ^ (v.card - 1) * ∑ h ∈ v, a h) 0 := by
    have hh : ∀ h ∈ v, HasDerivAt (fun t : ℝ => t * a h - 1) (a h) 0 := by
      intro h _
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a h)).sub_const 1
    convert HasDerivAt.fun_finsetProd hh using 1
    simp only [zero_mul, zero_sub, prod_const, smul_eq_mul, mul_sum]
    apply sum_congr rfl
    intro h hh
    rw [card_erase_of_mem hh]
  have hright : HasDerivAt
      (fun t : ℝ => ∑ v ∈ s.powerset,
        (∏ h ∈ v, (t * a h - 1)) * ∏ g ∈ s \ v, z g)
      (∑ v ∈ s.powerset, ((-1 : ℝ) ^ (v.card - 1) * ∑ h ∈ v, a h) *
        ∏ g ∈ s \ v, z g) 0 := by
    exact HasDerivAt.fun_sum fun v _ => (hv v).mul_const _
  have heq : (fun t : ℝ => ∏ h ∈ s, ((t * a h - 1) + z h)) =
      (fun t : ℝ => ∑ v ∈ s.powerset,
        (∏ h ∈ v, (t * a h - 1)) * ∏ g ∈ s \ v, z g) := by
    funext t
    exact prod_add _ _ _
  rw [heq] at hleft
  exact hleft.unique hright

lemma exp_difference_quotient_limit (b : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (t * b) - 1) / t)
      (𝓝[>] 0) (𝓝 b) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (t * b)) b 0 := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (0 * b)).comp 0
      ((hasDerivAt_id 0).mul_const b)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

/-- Positive clearing denominators preserves every original strict label. -/
lemma cleared_score_eq (a b : ι → ℝ) (hb : ∀ h, b h ≠ 0) :
    (∑ h, a h * ∏ g ∈ univ.erase h, b g) =
      (∑ h, a h / b h) * ∏ g, b g := by
  rw [sum_mul]
  apply sum_congr rfl
  intro h _
  rw [← mul_prod_erase univ b (mem_univ h)]
  field_simp [hb h]

lemma finite_difference_limit (a b : ι → ℝ) :
    Tendsto (fun t : ℝ => ∑ h, a h *
      ∏ g ∈ univ.erase h, ((Real.exp (t * b g) - 1) / t))
      (𝓝[>] 0) (𝓝 (∑ h, a h * ∏ g ∈ univ.erase h, b g)) := by
  apply tendsto_finsetSum
  intro h _
  exact tendsto_const_nhds.mul (tendsto_finsetProd _ fun g _ =>
    exp_difference_quotient_limit (b g))


variable {n H : ℕ}
open CoefficientOrderChart

abbrev SubsetIndex (H : ℕ) := {v : Finset (Fin H) // v ≠ ∅}

@[simp] theorem card_subsetIndex : Fintype.card (SubsetIndex H) = 2 ^ H - 1 := by
  simp [SubsetIndex, Fintype.card_subtype_compl, Fintype.card_finset]

omit [Fintype ι] [DecidableEq ι] in
lemma affineValue_sum (s : Finset ι) (a : ι → Option (Fin n) → ℝ)
    (x : Fin n → Bool) :
    affineValue (fun i => ∑ h ∈ s, a h i) x = ∑ h ∈ s, affineValue (a h) x := by
  simp only [affineValue, sum_add_distrib]
  congr 1
  simp_rw [mul_sum]
  exact sum_comm

lemma affineValue_mul (c : ℝ) (a : Option (Fin n) → ℝ) (x : Fin n → Bool) :
    affineValue (fun i => c * a i) x = c * affineValue a x := by
  simp only [affineValue, mul_add, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

lemma exp_affineValue (a : Option (Fin n) → ℝ) (x : Fin n → Bool) :
    Real.exp (affineValue a x) = Real.exp (a none) *
      ∏ i, if x i then Real.exp (a (some i)) else 1 := by
  rw [affineValue, Real.exp_add, Real.exp_sum]
  congr 1
  apply prod_congr rfl
  intro i _
  cases x i <;> simp [boolToReal]

lemma sum_subsetIndex (F : Finset (Fin H) → ℝ) (hzero : F ∅ = 0) :
    (∑ v : SubsetIndex H, F v.1) = ∑ v : Finset (Fin H), F v := by
  have hfilter : (∑ v : SubsetIndex H, F v.1) =
      ∑ v ∈ (univ : Finset (Finset (Fin H))).filter (fun v => v ≠ ∅), F v := by
    simpa only [Finset.subtype_univ] using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun v : Finset (Fin H) => v ≠ ∅) F)
  rw [hfilter]
  apply sum_subset (filter_subset _ _)
  intro v _ hv
  have he : v = ∅ := by simpa using hv
  simpa [he] using hzero

lemma grouped_expansion (a b : Fin H → ℝ) (t : ℝ) :
    (∑ h, a h * ∏ g ∈ univ.erase h, (Real.exp (t * b g) - 1)) =
      ∑ v : SubsetIndex H,
        ((-1 : ℝ) ^ (v.1.card - 1) * ∑ h ∈ v.1, a h) *
          Real.exp (t * ∑ g ∈ univ \ v.1, b g) := by
  rw [sum_subsetIndex (fun v =>
    ((-1 : ℝ) ^ (v.card - 1) * ∑ h ∈ v, a h) *
      Real.exp (t * ∑ g ∈ univ \ v, b g)) (by simp)]
  rw [weighted_prod_sub_expansion]
  simp only [powerset_univ]
  apply sum_congr rfl
  intro v _
  congr 1
  rw [mul_sum, Real.exp_sum]

lemma unscaled_eq_scaled (a b : Fin H → ℝ) {t : ℝ} (ht : 0 < t) :
    (∑ h, a h * ∏ g ∈ univ.erase h, (Real.exp (t * b g) - 1)) =
      t ^ (H - 1) * (∑ h, a h *
        ∏ g ∈ univ.erase h, ((Real.exp (t * b g) - 1) / t)) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  rw [prod_div_distrib, prod_const, card_erase_of_mem (mem_univ h)]
  simp only [card_univ, Fintype.card_fin]
  field_simp [ne_of_gt ht]


def compiledA (a b : Fin H → Option (Fin n) → ℝ) (t : ℝ)
    (v : SubsetIndex H) (i : Option (Fin n)) : ℝ :=
  (((-1 : ℝ) ^ (v.1.card - 1)) *
    Real.exp (t * ∑ g ∈ univ \ v.1, b g none)) * ∑ h ∈ v.1, a h i

def compiledZ (b : Fin H → Option (Fin n) → ℝ) (t : ℝ)
    (v : SubsetIndex H) (i : Fin n) : ℝ :=
  Real.exp (t * ∑ g ∈ univ \ v.1, b g (some i))

lemma compiled_term (a b : Fin H → Option (Fin n) → ℝ) (t : ℝ)
    (v : SubsetIndex H) (x : Fin n → Bool) :
    affineValue (compiledA a b t v) x *
      (∏ i, if x i then compiledZ b t v i else 1) =
      ((-1 : ℝ) ^ (v.1.card - 1) * ∑ h ∈ v.1, affineValue (a h) x) *
        Real.exp (t * ∑ g ∈ univ \ v.1, affineValue (b g) x) := by
  have he : Real.exp (t * ∑ g ∈ univ \ v.1, affineValue (b g) x) =
      Real.exp (t * ∑ g ∈ univ \ v.1, b g none) *
        ∏ i, if x i then compiledZ b t v i else 1 := by
    rw [← affineValue_sum, ← affineValue_mul, exp_affineValue]
    rfl
  rw [he]
  unfold compiledA
  rw [affineValue_mul, affineValue_sum]
  ring

lemma compiledScore_eq (a b : Fin H → Option (Fin n) → ℝ)
    (t : ℝ) (x : Fin n → Bool) :
    (∑ v : SubsetIndex H, affineValue (compiledA a b t v) x *
      (∏ i, if x i then compiledZ b t v i else 1)) =
      ∑ h, affineValue (a h) x *
        ∏ g ∈ univ.erase h, (Real.exp (t * affineValue (b g) x) - 1) := by
  simp_rw [compiled_term]
  exact (grouped_expansion _ _ _).symm

/-- Finite-cube continuity, positivity of all original denominators, and
regrouping give a strict sign compiler with no relative-margin hypothesis. -/
theorem mem_represented_of_affine_ratios
    (a b : Fin H → Option (Fin n) → ℝ) (f : (Fin n → Bool) → Bool)
    (hb : ∀ h x, 0 < affineValue (b h) x)
    (hf : ∀ x, if f x then 0 < ∑ h, affineValue (a h) x / affineValue (b h) x
      else (∑ h, affineValue (a h) x / affineValue (b h) x) < 0) :
    f ∈ AffineProductCapacity.represented n (2 ^ H - 1) := by
  let D (t : ℝ) (x : Fin n → Bool) := ∑ h, affineValue (a h) x *
    ∏ g ∈ univ.erase h, ((Real.exp (t * affineValue (b g) x) - 1) / t)
  have hlimit (x : Fin n → Bool) : Tendsto (fun t => D t x) (𝓝[>] 0)
      (𝓝 (∑ h, affineValue (a h) x * ∏ g ∈ univ.erase h, affineValue (b g) x)) :=
    finite_difference_limit _ _
  have hclear (x : Fin n → Bool) : if f x then
      0 < ∑ h, affineValue (a h) x * ∏ g ∈ univ.erase h, affineValue (b g) x
      else (∑ h, affineValue (a h) x * ∏ g ∈ univ.erase h, affineValue (b g) x) < 0 := by
    rw [cleared_score_eq _ _ (fun h => ne_of_gt (hb h x))]
    have hp : 0 < ∏ g, affineValue (b g) x := prod_pos fun g _ => hb g x
    have hx := hf x
    cases he : f x <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    · exact mul_neg_of_neg_of_pos hx hp
    · exact mul_pos hx hp
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x,
      if f x then 0 < D t x else D t x < 0 := by
    rw [Filter.eventually_all]
    intro x
    have hx := hclear x
    cases he : f x <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    · exact (hlimit x).eventually_lt_const hx
    · exact (hlimit x).eventually_const_lt hx
  obtain ⟨t, hsign, ht⟩ := (hevent.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := ht
  let e : Fin (2 ^ H - 1) ≃ SubsetIndex H :=
    Fintype.equivOfCardEq (by simp)
  apply AffineProductCapacity.mem_represented_of_score 0
    (fun k => compiledA a b t (e k)) (fun k => compiledZ b t (e k)) f
  intro x
  have heq : (∑ k : Fin (2 ^ H - 1),
      (compiledA a b t (e k) none +
        ∑ i, boolToReal (x i) * compiledA a b t (e k) (some i)) *
      (∏ i, if x i then compiledZ b t (e k) i else 1)) = t ^ (H - 1) * D t x := by
    calc
      _ = ∑ v : SubsetIndex H, affineValue (compiledA a b t v) x *
          (∏ i, if x i then compiledZ b t v i else 1) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by rw [compiledScore_eq, unscaled_eq_scaled _ _ htpos]
  rw [zero_add, heq]
  have hp : 0 < t ^ (H - 1) := pow_pos htpos _
  have hx := hsign x
  cases he : f x <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_pos_of_neg hp hx
  · exact mul_pos hp hx


lemma affineValue_add (a b : Option (Fin n) → ℝ) (x : Fin n → Bool) :
    affineValue (fun i => a i + b i) x = affineValue a x + affineValue b x := by
  simp only [affineValue, mul_add, sum_add_distrib]
  ring

/-- A nonempty original sum absorbs its bias into one affine numerator.
The positive denominators and every original head are retained. -/
theorem mem_represented_of_original {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) :
    f ∈ AffineProductCapacity.represented n (2 ^ H - 1) := by
  classical
  obtain ⟨phi, c, hs⟩ := exists_strict_fracCertificate (fracComputable_of_computable hf)
  by_cases hH : H = 0
  · subst H
    simp only [pow_zero, Nat.sub_self]
    apply AffineProductCapacity.mem_represented_of_score c
      (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) f
    intro x
    simpa using hs x
  · let j : Fin H := ⟨0, Nat.pos_of_ne_zero hH⟩
    let a := OriginalMarginCapacity.numeratorCoefficients ∘ phi
    let b := OriginalMarginCapacity.denominatorCoefficients ∘ phi
    let a' : Fin H → Option (Fin n) → ℝ := fun h i =>
      a h i + if h = j then c * b h i else 0
    have hb (h : Fin H) (x : Fin n → Bool) : 0 < affineValue (b h) x := by
      simpa only [b, Function.comp_apply,
        OriginalMarginCapacity.affineValue_denominatorCoefficients] using (phi h).denom_pos x
    apply mem_represented_of_affine_ratios a' b f hb
    intro x
    have hterm (h : Fin H) : affineValue (a' h) x / affineValue (b h) x =
        (phi h).eval x + if h = j then c else 0 := by
      by_cases hh : h = j
      · have ha : affineValue (a' h) x =
            affineValue (a h) x + c * affineValue (b h) x := by
          simp only [a', hh, ↓reduceIte]
          rw [affineValue_add, affineValue_mul]
        rw [ha, add_div, mul_div_cancel_right₀ _ (ne_of_gt (hb h x))]
        simp only [hh, ↓reduceIte]
        congr 1
        simpa only [a, b, Function.comp_apply, hh] using
          OriginalMarginCapacity.affineRatio_eq_eval (phi h) x
      · simp only [a', hh, ↓reduceIte, add_zero]
        exact OriginalMarginCapacity.affineRatio_eq_eval (phi h) x
    have hsum : (∑ h, affineValue (a' h) x / affineValue (b h) x) =
        c + ∑ h, (phi h).eval x := by
      simp_rw [hterm]
      rw [sum_add_distrib]
      simp [add_comm]
    rw [hsum]
    exact hs x

/-- Unconditional exact compiler. Its exponential width is too large for
any improvement of the unrestricted asymptotic lower bound. -/
theorem original_compiler (n H : ℕ) :
    AffineProductCapacity.HasCompiler n H (2 ^ H - 1) :=
  fun _ hf => mem_represented_of_original hf

end HeadComplexity.FiniteDifferenceProductCompiler
