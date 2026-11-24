import HeadComplexity.Results.AffinePlaneIncidence

set_option linter.style.header false

/-!
# Exact energy of the nonvertical affine-plane transform

This file audits a restricted selector mechanism.  It leaves the original
head model and worst-case quantity unchanged.  The energy identity keeps
all point weights arbitrary, so it cannot silently identify memories of
different local tables.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The weighted mass on a nonvertical affine line. -/
noncomputable def jointCellPlaneLineMass (f : F × F → ℝ) (l : F × F) : ℝ :=
  ∑ p : F × F, if p.2 = l.1 * p.1 + l.2 then f p else 0

omit [Fintype F] [DecidableEq F] in
private theorem jointCell_plane_incidence_rewrite (p l : F × F) :
    p.2 = l.1 * p.1 + l.2 ↔ l.2 = p.2 - l.1 * p.1 := by
  constructor <;> intro h <;> linear_combination -h

/-- Adjointness of line aggregation and the pencil sum. -/
theorem jointCell_plane_line_mass_adjoint (f : F × F → ℝ) (Z : F × F → ℝ) :
    (∑ l : F × F, jointCellPlaneLineMass f l * Z l) =
      ∑ p : F × F, f p * ∑ a : F, Z (a, p.2 - a * p.1) := by
  classical
  simp only [jointCellPlaneLineMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [jointCell_plane_incidence_rewrite]
  rw [affinePlane_line_rank_identity p (fun _ ↦ f p) Z]
  exact (Finset.mul_sum _ _ _).symm

/-- Every point belongs to exactly one line of each slope. -/
theorem jointCell_plane_line_mass_sum (f : F × F → ℝ) :
    (∑ l : F × F, jointCellPlaneLineMass f l) =
      (Fintype.card F : ℝ) * ∑ p : F × F, f p := by
  have h := jointCell_plane_line_mass_adjoint f (fun _ ↦ 1)
  simpa [Finset.sum_mul, mul_comm] using h

private theorem jointCell_plane_pencil_mass (f : F × F → ℝ) (p : F × F) :
    (∑ a : F, jointCellPlaneLineMass f (a, p.2 - a * p.1)) =
      (Fintype.card F : ℝ) * f p +
        ∑ g : F × F, if g.1 ≠ p.1 then f g else 0 := by
  classical
  simpa [jointCellPlaneLineMass] using
    (affinePlane_weighted_pencil_identity p (fun _ ↦ (1 : ℝ)) (fun _ g ↦ f g))

omit [Field F] in
private theorem jointCell_plane_off_vertical (f : F × F → ℝ) (p : F × F) :
    (∑ g : F × F, if g.1 ≠ p.1 then f g else 0) =
      (∑ g : F × F, f g) - ∑ y : F, f (p.1, y) := by
  classical
  have hsplit :
      (∑ g : F × F, f g) =
        (∑ g : F × F, if g.1 ≠ p.1 then f g else 0) +
          ∑ g : F × F, if g.1 = p.1 then f g else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g hg
    by_cases h : g.1 = p.1 <;> simp [h]
  have hv : (∑ g : F × F, if g.1 = p.1 then f g else 0) =
      ∑ y : F, f (p.1, y) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x : F, if x = p.1 then ∑ y : F, f (x, y) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : x = p.1 <;> simp [h]
      _ = _ := by simp
  rw [hv] at hsplit
  linarith

/-- The exact second moment, including the vertical-fiber subtraction.
No positivity or independence assumption is imposed on the point weights. -/
theorem jointCell_plane_line_mass_energy (f : F × F → ℝ) :
    (∑ l : F × F, jointCellPlaneLineMass f l ^ 2) =
      (Fintype.card F : ℝ) * (∑ p : F × F, f p ^ 2) +
        (∑ p : F × F, f p) ^ 2 -
          ∑ x : F, (∑ y : F, f (x, y)) ^ 2 := by
  classical
  have hadj := jointCell_plane_line_mass_adjoint f (jointCellPlaneLineMass f)
  simp_rw [← pow_two, jointCell_plane_pencil_mass, jointCell_plane_off_vertical] at hadj
  rw [hadj]
  have hvertical :
      (∑ p : F × F, f p * ∑ y : F, f (p.1, y)) =
        ∑ x : F, (∑ y : F, f (x, y)) ^ 2 := by
    simp [Fintype.sum_prod_type, ← Finset.sum_mul, pow_two]
  calc
    _ = (Fintype.card F : ℝ) * (∑ p : F × F, f p ^ 2) +
          (∑ p : F × F, f p) ^ 2 -
            ∑ p : F × F, f p * ∑ y : F, f (p.1, y) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [mul_left_comm (f _) (Fintype.card F : ℝ), ← pow_two]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ = _ := by rw [hvertical]

omit [DecidableEq F] in
/-- An incidence-free rectangle has at most `q^3` entries.  This deliberately
uses the easy uniform bound rather than an optimized extremal constant. -/
theorem jointCell_plane_empty_rectangle (P L : Finset (F × F))
    (hempty : ∀ p ∈ P, ∀ l ∈ L, p.2 ≠ l.1 * p.1 + l.2) :
    (P.card : ℝ) * L.card ≤ (Fintype.card F : ℝ) ^ 3 := by
  classical
  let f : F × F → ℝ := fun p ↦ if p ∈ P then 1 else 0
  let q : ℝ := Fintype.card F
  let p : ℝ := P.card
  let m : F × F → ℝ := jointCellPlaneLineMass f
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hf : (∑ x : F × F, f x) = p := by simp [f, p]
  have hf2 : (∑ x : F × F, f x ^ 2) = p := by simp [f, p]
  have hsum : (∑ l : F × F, m l) = q * p := by
    simpa [m, q, hf] using jointCell_plane_line_mass_sum f
  have henergy : (∑ l : F × F, m l ^ 2) ≤ q * p + p ^ 2 := by
    have h := jointCell_plane_line_mass_energy f
    have hnonneg : 0 ≤ ∑ x : F, (∑ y : F, f (x, y)) ^ 2 := by positivity
    dsimp [m]
    rw [h, hf, hf2]
    dsimp [q]
    linarith
  have hvariance : (∑ l : F × F, (q * m l - p) ^ 2) ≤ q ^ 3 * p := by
    have hexpand :
        (∑ l : F × F, (q * m l - p) ^ 2) =
          q ^ 2 * (∑ l : F × F, m l ^ 2) -
            2 * q * p * (∑ l : F × F, m l) + q ^ 2 * p ^ 2 := by
      simp_rw [sub_sq, mul_pow]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [show ∀ l, 2 * (q * m l) * p = (2 * q * p) * m l by
        intro l; ring]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp [q, pow_two, mul_assoc]
    rw [hexpand, hsum]
    have hmul := mul_le_mul_of_nonneg_left henergy (sq_nonneg q)
    nlinarith
  have hzero (l : F × F) (hl : l ∈ L) : m l = 0 := by
    dsimp [m, jointCellPlaneLineMass]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxp : x ∈ P
    · simp [hempty x hxp l hl]
    · simp [f, hxp]
  have hrect : (L.card : ℝ) * p ^ 2 ≤ q ^ 3 * p := by
    calc
      _ = ∑ l ∈ L, (q * m l - p) ^ 2 := by
        symm
        calc
          _ = ∑ l ∈ L, p ^ 2 := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hzero l hl]
            ring
          _ = _ := by simp
      _ ≤ ∑ l : F × F, (q * m l - p) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
          (fun i hi hnot ↦ sq_nonneg _)
      _ ≤ _ := hvariance
  by_cases hp0 : p = 0
  · have hcard : P.card = 0 := by
      dsimp [p] at hp0
      exact_mod_cast hp0
    simp only [hcard, Nat.cast_zero, zero_mul]
    positivity
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    change p * (L.card : ℝ) ≤ q ^ 3
    apply (mul_le_mul_iff_left₀ hp').mp
    nlinarith [hrect]

omit [DecidableEq F] in
/-- A set-containment representation of all nonvertical affine-plane
incidences needs at least `q - 1` coordinates.  This also applies to a single
pure-product selector, whose nonzero support is a containment relation. -/
theorem jointCell_plane_containment_dimension {I : Type*} [Fintype I]
    (code support : F × F → Finset I)
    (hcode : ∀ p l, p.2 = l.1 * p.1 + l.2 ↔ code p ⊆ support l) :
    Fintype.card F - 1 ≤ Fintype.card I := by
  classical
  let q : ℝ := Fintype.card F
  let C : I → F × F → F × F → ℝ := fun i p l ↦
    if i ∈ code p ∧ i ∉ support l then 1 else 0
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hC (i : I) :
      (∑ p : F × F, ∑ l : F × F, C i p l) ≤ q ^ 3 := by
    let P : Finset (F × F) := Finset.univ.filter (fun p ↦ i ∈ code p)
    let L : Finset (F × F) := Finset.univ.filter (fun l ↦ i ∉ support l)
    have hempty : ∀ p ∈ P, ∀ l ∈ L, p.2 ≠ l.1 * p.1 + l.2 := by
      intro p hp l hl hinc
      have hip : i ∈ code p := (Finset.mem_filter.mp hp).2
      have hil : i ∉ support l := (Finset.mem_filter.mp hl).2
      exact hil ((hcode p l).mp hinc hip)
    have hrect := jointCell_plane_empty_rectangle P L hempty
    have hsum : (∑ p : F × F, ∑ l : F × F, C i p l) =
        (P.card : ℝ) * L.card := by
      have hsplit (p l : F × F) : C i p l =
          (if i ∈ code p then (1 : ℝ) else 0) *
            (if i ∉ support l then (1 : ℝ) else 0) := by
        dsimp [C]
        split_ifs <;> simp_all
      simp_rw [hsplit, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      change _ = _
      rw [Finset.sum_boole, Finset.sum_boole]
    simpa [hsum, q] using hrect
  have hcover (p l : F × F) :
      (if p.2 ≠ l.1 * p.1 + l.2 then (1 : ℝ) else 0) ≤ ∑ i : I, C i p l := by
    by_cases hinc : p.2 = l.1 * p.1 + l.2
    · simp only [hinc, ne_eq, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg fun i hi ↦ by dsimp [C]; split_ifs <;> norm_num
    · have hnsub : ¬code p ⊆ support l := fun h ↦ hinc ((hcode p l).mpr h)
      obtain ⟨i, hip, hil⟩ := Finset.not_subset.mp hnsub
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset I))
        (f := fun i ↦ C i p l)
        (fun j hj ↦ show 0 ≤ C j p l by dsimp [C]; split_ifs <;> norm_num)
        (Finset.mem_univ i)
      simpa [hinc, C, hip, hil] using hsingle
  have htotal : (∑ p : F × F, ∑ l : F × F,
      if p.2 ≠ l.1 * p.1 + l.2 then (1 : ℝ) else 0) = q ^ 4 - q ^ 3 := by
    have hpoint : ∀ p l : F × F,
        (if p.2 ≠ l.1 * p.1 + l.2 then (1 : ℝ) else 0) =
          1 - (if p.2 = l.1 * p.1 + l.2 then 1 else 0) := by
      intro p l
      split_ifs <;> simp_all
    simp_rw [hpoint, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun p l : F × F ↦
      if p.2 = l.1 * p.1 + l.2 then (1 : ℝ) else 0)]
    change _ - ∑ l : F × F, jointCellPlaneLineMass (fun _ ↦ 1) l = _
    rw [jointCell_plane_line_mass_sum]
    simp [q, pow_succ, mul_assoc]
  have hcount : q ^ 4 - q ^ 3 ≤ (Fintype.card I : ℝ) * q ^ 3 := by
    calc
      _ = ∑ p : F × F, ∑ l : F × F,
          if p.2 ≠ l.1 * p.1 + l.2 then (1 : ℝ) else 0 := htotal.symm
      _ ≤ ∑ p : F × F, ∑ l : F × F, ∑ i : I, C i p l := by
        apply Finset.sum_le_sum
        intro p hp
        exact Finset.sum_le_sum fun l hl ↦ hcover p l
      _ = ∑ i : I, ∑ p : F × F, ∑ l : F × F, C i p l := by
        simp_rw [Finset.sum_comm (f := fun l i ↦ C i _ l)]
        rw [Finset.sum_comm]
      _ ≤ ∑ i : I, q ^ 3 := Finset.sum_le_sum fun i hi ↦ hC i
      _ = _ := by simp
  have hdim : q - 1 ≤ (Fintype.card I : ℝ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hq 3)).mp
    nlinarith [hcount]
  have hnat : Fintype.card F ≤ Fintype.card I + 1 := by
    have hreal : (Fintype.card F : ℝ) ≤ (Fintype.card I : ℝ) + 1 := by
      dsimp [q] at hdim
      linarith
    exact_mod_cast hreal
  omega

end HeadComplexity.AxisZeroGluing
