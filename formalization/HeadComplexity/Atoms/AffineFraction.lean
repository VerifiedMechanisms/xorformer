import HeadComplexity.Atoms.FracAtom
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Exact affine coefficients of a fractional atom

An affine fraction records its numerator and denominator separately. The main
theorem characterizes the image of the atom coefficient map, not every ratio
representation of the same function on the Boolean cube. These are the supporting
coefficient lemmas for Theorem 10's exact affine-ratio normal form.
-/

namespace HeadComplexity

open scoped BigOperators

/-- A prescribed numerator and denominator, without an implicit rescaling. -/
@[ext] structure AffineFraction (n : ℕ) where
  A : Fin n → ℝ
  b : ℝ
  C : Fin n → ℝ
  d : ℝ

namespace AffineFraction

variable {n : ℕ}

noncomputable def numerator (r : AffineFraction n) (x : Fin n → Bool) : ℝ :=
  r.b + ∑ i, r.A i * boolToReal (x i)

noncomputable def denominator (r : AffineFraction n) (x : Fin n → Bool) : ℝ :=
  r.d + ∑ i, r.C i * boolToReal (x i)

noncomputable def eval (r : AffineFraction n) (x : Fin n → Bool) : ℝ :=
  r.numerator x / r.denominator x

/-- All entries are strictly positive, all strictly negative, or all zero. -/
def UniformSign (v : Fin n → ℝ) : Prop :=
  (∀ i, 0 < v i) ∨ (∀ i, v i < 0) ∨ (∀ i, v i = 0)

/-- A positive denominator with uniform slopes. Only a constant denominator
restricts the numerator slopes; the numerator constant is always free. -/
def Admissible (r : AffineFraction n) : Prop :=
  (∀ x, 0 < r.denominator x) ∧ UniformSign r.C ∧
    ((∀ i, r.C i = 0) → UniformSign r.A)

theorem denominator_pos (r : AffineFraction n) (h : r.Admissible)
    (x : Fin n → Bool) : 0 < r.denominator x := h.1 x

/-- Empty coordinate vectors impose no sign restriction. -/
@[simp] theorem admissible_zero (r : AffineFraction 0) : r.Admissible ↔ 0 < r.d := by
  simp [Admissible, UniformSign, denominator]

end AffineFraction

namespace FracAtom

variable {n : ℕ}

/-- Expand the atom on Boolean inputs, retaining its actual coefficients. -/
noncomputable def toAffineFraction (φ : FracAtom n) : AffineFraction n where
  A i := φ.ρ i * ((φ.α - 1) * φ.m i + φ.α * φ.δ)
  b := φ.η + ∑ i, φ.ρ i * φ.m i
  C i := φ.ρ i * (φ.α - 1)
  d := φ.γ + ∑ i, φ.ρ i

theorem numerator_eq (φ : FracAtom n) (x : Fin n → Bool) :
    φ.η + ∑ i, φ.wt x i * (φ.m i + if x i then φ.δ else 0) =
      φ.toAffineFraction.numerator x := by
  unfold AffineFraction.numerator toAffineFraction
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [wt, boolToReal, hx]
  ring

theorem denominator_eq (φ : FracAtom n) (x : Fin n → Bool) :
    φ.γ + ∑ i, φ.wt x i = φ.toAffineFraction.denominator x := by
  unfold AffineFraction.denominator toAffineFraction
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [wt, boolToReal, hx]
  ring

theorem eval_eq (φ : FracAtom n) (x : Fin n → Bool) :
    φ.eval x = φ.toAffineFraction.eval x := by
  unfold eval AffineFraction.eval
  rw [numerator_eq, denominator_eq]

theorem toAffineFraction_admissible (φ : FracAtom n) :
    φ.toAffineFraction.Admissible := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [← denominator_eq]
    exact φ.denom_pos x
  · rcases lt_trichotomy φ.α 1 with hlt | heq | hgt
    · exact Or.inr (Or.inl fun i ↦ mul_neg_of_pos_of_neg (φ.hρ i) (sub_neg.mpr hlt))
    · exact Or.inr (Or.inr fun i ↦ by simp [toAffineFraction, heq])
    · exact Or.inl fun i ↦ mul_pos (φ.hρ i) (sub_pos.mpr hgt)
  · intro hC
    have hA (i) : φ.toAffineFraction.A i = φ.ρ i * φ.δ := by
      have hα : φ.α = 1 := sub_eq_zero.mp
        ((mul_eq_zero.mp (hC i)).resolve_left (φ.hρ i).ne')
      simp [toAffineFraction, hα]
    rcases lt_trichotomy φ.δ 0 with hneg | hzero | hpos
    · right; left
      intro i
      rw [hA]
      exact mul_neg_of_pos_of_neg (φ.hρ i) hneg
    · right; right
      intro i
      simp [hA, hzero]
    · left
      intro i
      rw [hA]
      exact mul_pos (φ.hρ i) hpos

end FracAtom

namespace AffineFraction

variable {n : ℕ}

/-- The constants are free once the slopes and positive position weights fit. -/
private theorem realize (r : AffineFraction n) (α δ : ℝ) (ρ m : Fin n → ℝ)
    (hα : 0 < α) (hρ : ∀ i, 0 < ρ i) (hs : ∑ i, ρ i < r.d)
    (hA : ∀ i, ρ i * ((α - 1) * m i + α * δ) = r.A i)
    (hC : ∀ i, ρ i * (α - 1) = r.C i) :
    ∃ φ : FracAtom n, φ.toAffineFraction = r := by
  refine ⟨{
    η := r.b - ∑ i, ρ i * m i
    δ := δ
    γ := r.d - ∑ i, ρ i
    α := α
    ρ := ρ
    m := m
    hγ := sub_pos.mpr hs
    hα := hα
    hρ := hρ }, ?_⟩
  ext i <;> simp [FracAtom.toAffineFraction, hA, hC]

/-- One inverse formula handles both strict orientations of denominator slopes. -/
private theorem realize_nonconstant (r : AffineFraction n) (t : ℝ)
    (ht : t ≠ 0) (hα : 0 < 1 + t) (hρ : ∀ i, 0 < r.C i / t)
    (hs : ∑ i, r.C i / t < r.d) :
    ∃ φ : FracAtom n, φ.toAffineFraction = r := by
  have hC (i) : r.C i ≠ 0 := by
    intro hz
    have := hρ i
    simp [hz] at this
  apply realize r (1 + t) 0 (fun i ↦ r.C i / t) (fun i ↦ r.A i / r.C i)
    hα hρ hs
  · intro i
    field_simp [ht, hC i]
    ring
  · intro i
    field_simp [ht]
    ring

/-- Scale positive coordinates so their total weight is smaller than `d`. -/
private theorem small_weights (w : Fin n → ℝ) (d : ℝ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) :
    ∃ q : ℝ, 0 < q ∧ (∑ i, w i / q) < d := by
  let S := ∑ i, w i
  let q := 1 + S / d
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ (hw i).le
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q, hq, ?_⟩
  rw [← Finset.sum_div]
  apply (div_lt_iff₀ hq).mpr
  have hprod : d * q = d + S := by dsimp [q]; field_simp
  change S < d * q
  rw [hprod]
  linarith

private theorem realize_positive (r : AffineFraction n)
    (hd : 0 < r.d) (hC : ∀ i, 0 < r.C i) :
    ∃ φ : FracAtom n, φ.toAffineFraction = r := by
  obtain ⟨t, ht, hs⟩ := small_weights r.C r.d hC hd
  exact realize_nonconstant r t ht.ne' (by linarith)
    (fun i ↦ div_pos (hC i) ht) hs

private theorem realize_negative (r : AffineFraction n)
    (hC : ∀ i, r.C i < 0) (hs : 0 < r.d + ∑ i, r.C i) :
    ∃ φ : FracAtom n, φ.toAffineFraction = r := by
  let S := ∑ i, -r.C i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ (neg_pos.mpr (hC i)).le
  have hSd : S < r.d := by dsimp [S]; rw [Finset.sum_neg_distrib]; linarith
  have hd : 0 < r.d := lt_of_le_of_lt hS hSd
  let α := (r.d - S) / (2 * r.d)
  have hα : 0 < α := div_pos (sub_pos.mpr hSd) (by positivity)
  have hαlt : α < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * r.d)).mpr
    linarith
  have ht : α - 1 < 0 := sub_neg.mpr hαlt
  apply realize_nonconstant r (α - 1) ht.ne (by linarith)
    (fun i ↦ div_pos_of_neg_of_neg (hC i) ht)
  have hprod : r.d * (1 - α) = (r.d + S) / 2 := by
    dsimp [α]
    field_simp
    ring
  have hsum : (∑ i, r.C i / (α - 1)) = S / (1 - α) := by
    rw [← Finset.sum_div]
    dsimp [S]
    rw [Finset.sum_neg_distrib, show α - 1 = -(1 - α) by ring, div_neg, neg_div]
  rw [hsum]
  apply (div_lt_iff₀ (sub_pos.mpr hαlt)).mpr
  rw [hprod]
  linarith

private theorem realize_constant (r : AffineFraction n) (δ : ℝ) (ρ : Fin n → ℝ)
    (hC : ∀ i, r.C i = 0) (hρ : ∀ i, 0 < ρ i) (hs : ∑ i, ρ i < r.d)
    (hA : ∀ i, ρ i * δ = r.A i) :
    ∃ φ : FracAtom n, φ.toAffineFraction = r := by
  apply realize r 1 δ ρ (fun _ ↦ 0) (by norm_num) hρ hs
  · simpa using hA
  · simpa using fun i ↦ (hC i).symm

/-- Construct an atom with exactly the prescribed coefficients. -/
theorem exists_atom (r : AffineFraction n) (h : r.Admissible) :
    ∃ φ : FracAtom n, φ.toAffineFraction = r := by
  have hd : 0 < r.d := by
    simpa [denominator, boolToReal] using h.1 (fun _ ↦ false)
  rcases h.2.1 with hpos | hneg | hC
  · exact realize_positive r hd hpos
  · apply realize_negative r hneg
    simpa [denominator, boolToReal] using h.1 (fun _ ↦ true)
  rcases h.2.2 hC with hpos | hneg | hzero
  · obtain ⟨q, hq, hs⟩ := small_weights r.A r.d hpos hd
    exact realize_constant r q (fun i ↦ r.A i / q) hC
      (fun i ↦ div_pos (hpos i) hq) hs (fun i ↦ div_mul_cancel₀ _ hq.ne')
  · obtain ⟨q, hq, hs⟩ := small_weights (fun i ↦ -r.A i) r.d
      (fun i ↦ neg_pos.mpr (hneg i)) hd
    apply realize_constant r (-q) (fun i ↦ -r.A i / q) hC
      (fun i ↦ div_pos (neg_pos.mpr (hneg i)) hq) hs
    intro i
    field_simp
  · let w : ℝ := r.d / ((n : ℝ) + 1)
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hw : 0 < w := div_pos hd hn
    have hs : (∑ _ : Fin n, w) < r.d := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [w]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hn).mpr
      nlinarith
    exact realize_constant r 0 (fun _ ↦ w) hC (fun _ ↦ hw) hs
      (fun i ↦ by simpa using (hzero i).symm)

/-- Exact image of the coefficient map, in every dimension including zero. -/
theorem realizable_iff (r : AffineFraction n) :
    (∃ φ : FracAtom n, φ.toAffineFraction = r) ↔ r.Admissible := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact φ.toAffineFraction_admissible
  · exact r.exists_atom

end AffineFraction
end HeadComplexity
