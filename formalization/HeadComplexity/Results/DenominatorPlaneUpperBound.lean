import HeadComplexity.Results.CollinearDenominatorUpperBound

set_option linter.style.header false

/-!
# Head-preserving simulation in an affine denominator plane

When all denominators lie in the span of two affine functions and that span
contains a positive affine function with strictly uniform slopes, proper
partial fractions give a head-preserving vanilla classifier. The numerators
are unrestricted and no sign perturbation is required.
-/

namespace HeadComplexity

open scoped BigOperators
open Polynomial

namespace AffineStatistic

variable {n H m : ℕ}

/-- Proper polynomial sums in a projective affine statistic admit H vanilla
heads when the base is positive and has uniformly strict slopes. -/
theorem computable_of_projective_affine_polynomial_sum
    (v w : Fin n → ℝ) (d b : ℝ)
    (hvpos : ∀ x, 0 < eval v d x)
    (hvslope : (∀ i, 0 < v i) ∨ (∀ i, v i < 0))
    (W : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (p : Fin m → ℝ[X]) (hdeg : ∀ j, (p j).natDegree < H)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < ∑ j, eval (W j) (a j) x / eval v d x *
        (p j).eval (eval w b x / eval v d x) ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  classical
  let av (h : Fin H) : ℝ := 2 + ∑ i, |w i / v i| +
    ∑ x : Fin n → Bool, |eval w b x / eval v d x| + (h : ℕ)
  have havinj : Function.Injective av := by
    intro h j heq
    exact Fin.ext (Nat.cast_inj.mp (add_left_cancel heq))
  have hvne (i : Fin n) : v i ≠ 0 := by
    rcases hvslope with hp | hn
    · exact (hp i).ne'
    · exact (hn i).ne
  have havslope (h : Fin H) (i : Fin n) : 0 < w i / v i + av h := by
    have hi : |w i / v i| ≤ ∑ j, |w j / v j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (w j / v j)) (Finset.mem_univ i)
    have hx : 0 ≤ ∑ x : Fin n → Bool, |eval w b x / eval v d x| :=
      Finset.sum_nonneg fun x _ ↦ abs_nonneg _
    have hh : (0 : ℝ) ≤ (h : ℕ) := Nat.cast_nonneg _
    dsimp only [av]
    linarith [neg_le_abs (w i / v i)]
  have havpos (h : Fin H) (x : Fin n → Bool) :
      0 < eval w b x / eval v d x + av h := by
    have hx : |eval w b x / eval v d x| ≤
        ∑ y : Fin n → Bool, |eval w b y / eval v d y| :=
      Finset.single_le_sum (fun y _ ↦ abs_nonneg (eval w b y / eval v d y)) (Finset.mem_univ x)
    have hi : 0 ≤ ∑ i, |w i / v i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    have hh : (0 : ℝ) ≤ (h : ℕ) := Nat.cast_nonneg _
    dsimp only [av]
    linarith [neg_le_abs (eval w b x / eval v d x)]
  choose bv hpf using fun j ↦ proper_partial_fraction (p j) av havinj (hdeg j)
  let r (h : Fin H) : AffineFraction n := {
    A := fun i ↦ ∑ j, bv j h * W j i
    b := ∑ j, bv j h * a j
    C := fun i ↦ w i + av h * v i
    d := b + av h * d }
  have hrnum (h : Fin H) (x : Fin n → Bool) :
      (r h).numerator x = ∑ j, bv j h * eval (W j) (a j) x := by
    dsimp [r, AffineFraction.numerator, eval]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hrden (h : Fin H) (x : Fin n → Bool) :
      (r h).denominator x = eval w b x + av h * eval v d x := by
    dsimp [r, AffineFraction.denominator, eval]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    ring
  have hrpos (h : Fin H) (x : Fin n → Bool) : 0 < (r h).denominator x := by
    rw [hrden]
    have he : eval w b x + av h * eval v d x =
        eval v d x * (eval w b x / eval v d x + av h) := by
      field_simp [(hvpos x).ne']
    rw [he]
    exact mul_pos (hvpos x) (havpos h x)
  have hrslope (h : Fin H) (i : Fin n) :
      (r h).C i = v i * (w i / v i + av h) := by
    dsimp only [r]
    field_simp [hvne i]
  have hradm (h : Fin H) : (r h).Admissible := by
    have horient : (∀ i, 0 < (r h).C i) ∨ (∀ i, (r h).C i < 0) := by
      rcases hvslope with hp | hn
      · exact Or.inl (fun i ↦ by rw [hrslope]; exact mul_pos (hp i) (havslope h i))
      · exact Or.inr (fun i ↦ by rw [hrslope]; exact mul_neg_of_neg_of_pos (hn i) (havslope h i))
    refine ⟨hrpos h, horient.elim Or.inl (fun hn ↦ Or.inr (Or.inl hn)), ?_⟩
    intro hz
    rcases horient with hp | hn
    · exact Or.inl (fun i ↦ False.elim ((hp i).ne' (hz i)))
    · exact Or.inl (fun i ↦ False.elim ((hn i).ne (hz i)))
  apply (computableWithSharedHeadsN_iff_affineFractionComputable H f).mpr
  refine ⟨r, 0, hradm, fun x ↦ ?_⟩
  let y := eval w b x / eval v d x
  have hreval (h : Fin H) : (r h).eval x =
      ∑ j, eval (W j) (a j) x / eval v d x * (bv j h / (y + av h)) := by
    rw [AffineFraction.eval, hrnum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hrden]
    dsimp only [y]
    field_simp [(hvpos x).ne', (havpos h x).ne', (hrpos h x).ne']
  simp_rw [hreval]
  rw [zero_add, Finset.sum_comm]
  have hscore : (∑ j, ∑ h, eval (W j) (a j) x / eval v d x *
        (bv j h / (y + av h))) =
      (∑ j, eval (W j) (a j) x / eval v d x * (p j).eval y) /
        ∏ h, (y + av h) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum, hpf j y (fun h ↦ havpos h x)]
    ring
  rw [hscore, div_pos_iff_of_pos_right (Finset.prod_pos fun h _ ↦ havpos h x)]
  exact hf x

/-- A positive affine denominator plane containing one strictly oriented
positive base admits head-preserving vanilla simulation. -/
theorem computable_of_denominator_plane
    (r : Fin H → AffineFraction n) (c : ℝ)
    (v w : Fin n → ℝ) (d b : ℝ) (α β : Fin H → ℝ)
    (hvpos : ∀ x, 0 < eval v d x)
    (hvslope : (∀ i, 0 < v i) ∨ (∀ i, v i < 0))
    (hden : ∀ h x, 0 < (r h).denominator x)
    (hspan : ∀ h x, (r h).denominator x = α h * eval v d x + β h * eval w b x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  classical
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst H
    apply (computableWithSharedHeadsN_iff_affineFractionComputable 0 f).mpr
    exact ⟨r, c, fun h ↦ Fin.elim0 h, hf⟩
  let first : Fin H := ⟨0, hH⟩
  let shift (h : Fin H) : ℝ := if h = first then c else 0
  have hshiftsum : (∑ h, shift h) = c := by simp [shift]
  let W (h : Fin H) (i : Fin n) := (r h).A i + shift h * (r h).C i
  let a (h : Fin H) := (r h).b + shift h * (r h).d
  let D (h : Fin H) : ℝ[X] := C (β h) * X + C (α h)
  let p (h : Fin H) : ℝ[X] := ∏ j ∈ Finset.univ.erase h, D j
  have hDdegree (h : Fin H) : (D h).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · simp
  have hpdegree (h : Fin H) : (p h).natDegree < H := by
    have hle : (p h).natDegree ≤ H - 1 := by
      apply (Polynomial.natDegree_prod_le _ _).trans
      apply le_trans (Finset.sum_le_sum fun j _ ↦ hDdegree j)
      simp
    omega
  have hDvalue (h : Fin H) (x : Fin n → Bool) :
      (D h).eval (eval w b x / eval v d x) = (r h).denominator x / eval v d x := by
    simp only [D, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [hspan]
    field_simp [(hvpos x).ne']
    ring
  have hpvalue (h : Fin H) (x : Fin n → Bool) :
      (p h).eval (eval w b x / eval v d x) =
        ∏ j ∈ Finset.univ.erase h, ((r j).denominator x / eval v d x) := by
    simp only [p, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun j _ ↦ hDvalue j x
  have hLvalue (h : Fin H) (x : Fin n → Bool) :
      eval (W h) (a h) x = (r h).numerator x + shift h * (r h).denominator x := by
    dsimp [eval, W, a, AffineFraction.numerator, AffineFraction.denominator]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    ring
  have hscore (x : Fin n → Bool) :
      (∑ h, eval (W h) (a h) x / eval v d x *
        (p h).eval (eval w b x / eval v d x)) =
        (c + ∑ h, (r h).eval x) * ∏ h, ((r h).denominator x / eval v d x) := by
    have hterm (h : Fin H) :
        eval (W h) (a h) x / eval v d x *
          (p h).eval (eval w b x / eval v d x) =
          ((r h).eval x + shift h) * ∏ j, ((r j).denominator x / eval v d x) := by
      rw [hLvalue, hpvalue,
        ← Finset.mul_prod_erase Finset.univ (fun j ↦ (r j).denominator x / eval v d x)
          (Finset.mem_univ h), AffineFraction.eval]
      field_simp [(hden h x).ne', (hvpos x).ne']
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hshiftsum]
    ring
  apply computable_of_projective_affine_polynomial_sum v w d b hvpos hvslope W a p hpdegree f
  intro x
  rw [hscore, mul_pos_iff_of_pos_right
    (Finset.prod_pos fun h _ ↦ div_pos (hden h x) (hvpos x))]
  exact hf x

end AffineStatistic

/-- Pure rotary families in a denominator plane with an oriented positive
base admit vanilla simulation at the same head count. -/
theorem pureRoPEFamily_vanilla_of_denominator_plane {n H : ℕ}
    (p : Fin H → PureRoPEAtom n) (c : ℝ)
    (v w : Fin n → ℝ) (d b : ℝ) (α β : Fin H → ℝ)
    (hvpos : ∀ x, 0 < AffineStatistic.eval v d x)
    (hvslope : (∀ i, 0 < v i) ∨ (∀ i, v i < 0))
    (hspan : ∀ h x, (p h).toAffineFraction.denominator x =
      α h * AffineStatistic.eval v d x + β h * AffineStatistic.eval w b x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  apply AffineStatistic.computable_of_denominator_plane
    (fun h ↦ (p h).toAffineFraction) c v w d b α β hvpos hvslope
    (fun h x ↦ (p h).denominator_pos x) hspan f
  intro x
  simpa only [PureRoPEAtom.eval_eq] using hf x

/-- The same denominator-plane theorem permits arbitrary retained numerators. -/
theorem retainedRoPEFamily_vanilla_of_denominator_plane {n H : ℕ}
    (p : Fin H → RetainedRoPEAtom n) (c : ℝ)
    (v w : Fin n → ℝ) (d b : ℝ) (α β : Fin H → ℝ)
    (hvpos : ∀ x, 0 < AffineStatistic.eval v d x)
    (hvslope : (∀ i, 0 < v i) ∨ (∀ i, v i < 0))
    (hspan : ∀ h x, (p h).toAffineFraction.denominator x =
      α h * AffineStatistic.eval v d x + β h * AffineStatistic.eval w b x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < c + ∑ h, (p h).eval x ↔ f x = true)) :
    computableWithSharedHeadsN n H f := by
  apply AffineStatistic.computable_of_denominator_plane
    (fun h ↦ (p h).toAffineFraction) c v w d b α β hvpos hvslope
    (fun h x ↦ (p h).denominator_pos x) hspan f
  exact hf

end HeadComplexity
