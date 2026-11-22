import HeadComplexity.Results.BlockDesignHall
import Mathlib.FieldTheory.Finite.GaloisField

set_option linter.style.header false

/-!
# Affine lines for the multiaffine matching obstruction

The directions are the forms x + a*y, together with the form y. Repeated
parallel classes will supply the Hall matchings. This auxiliary construction
asserts no lower bound on attention-head complexity.
-/

namespace HeadComplexity.FiniteFieldLines

open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

abbrev Point := F × F
abbrev Direction := Option F

def value : Direction F → Point F → F
  | some a, (x, y) => x + a * y
  | none, (_, y) => y

def line (d : Direction F) (t : F) : Finset (Point F) :=
  Finset.univ.filter fun p ↦ value F d p = t

@[simp] theorem mem_line (d : Direction F) (t : F) (p : Point F) :
    p ∈ line F d t ↔ value F d p = t := by simp [line]

omit [Field F] [DecidableEq F] in
theorem card_point : Fintype.card (Point F) = Fintype.card F ^ 2 := by
  simp [Point, Fintype.card_prod, pow_two]

omit [Field F] [DecidableEq F] in
theorem card_direction : Fintype.card (Direction F) = Fintype.card F + 1 := by
  simp [Direction, Fintype.card_option]

theorem card_line (d : Direction F) (t : F) :
    (line F d t).card = Fintype.card F := by
  classical
  rw [← Finset.card_univ (α := F)]
  symm
  cases d with
  | none =>
      apply Finset.card_bij (fun x _ ↦ (x, t))
      · intro x _
        simp [value]
      · intro x _ x' _ he
        exact congrArg (fun p : Point F ↦ p.1) he
      · rintro ⟨x, y⟩ hp
        refine ⟨x, Finset.mem_univ _, ?_⟩
        have hp' : y = t := (mem_line F _ _ _).mp hp
        simp [hp']
  | some a =>
      apply Finset.card_bij (fun y _ ↦ (t - a * y, y))
      · intro y _
        simp only [mem_line, value]
        ring
      · intro y _ y' _ he
        exact congrArg (fun p : Point F ↦ p.2) he
      · rintro ⟨x, y⟩ hp
        refine ⟨y, Finset.mem_univ _, ?_⟩
        have hp' : x + a * y = t := (mem_line F _ _ _).mp hp
        apply Prod.ext
        · linear_combination -hp'
        · rfl

theorem intersection_card_le_one (d e : Direction F) (t s : F)
    (hne : line F d t ≠ line F e s) :
    (line F d t ∩ line F e s).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp'
  obtain ⟨hp1, hp2⟩ := Finset.mem_inter.mp hp
  obtain ⟨hp1', hp2'⟩ := Finset.mem_inter.mp hp'
  simp only [mem_line] at hp1 hp2 hp1' hp2'
  cases d with
  | none =>
      cases e with
      | none =>
          have hts : t = s := hp1.symm.trans hp2
          exact False.elim (hne (hts ▸ rfl))
      | some b =>
          change y = t at hp1
          change y' = t at hp1'
          change x + b * y = s at hp2
          change x' + b * y' = s at hp2'
          apply Prod.ext
          · linear_combination hp2 - hp2' - b * hp1 + b * hp1'
          · exact hp1.trans hp1'.symm
  | some a =>
      cases e with
      | none =>
          change y = s at hp2
          change y' = s at hp2'
          change x + a * y = t at hp1
          change x' + a * y' = t at hp1'
          apply Prod.ext
          · linear_combination hp1 - hp1' - a * hp2 + a * hp2'
          · exact hp2.trans hp2'.symm
      | some b =>
          change x + a * y = t at hp1
          change x' + a * y' = t at hp1'
          change x + b * y = s at hp2
          change x' + b * y' = s at hp2'
          by_cases hab : a = b
          · subst b
            have hts : t = s := hp1.symm.trans hp2
            exact False.elim (hne (hts ▸ rfl))
          · have hy : y = y' := by
              apply (mul_left_cancel₀ (sub_ne_zero.mpr hab))
              linear_combination hp1 - hp1' - hp2 + hp2'
            apply Prod.ext
            · linear_combination hp1 - hp1' - a * hy
            · exact hy

theorem line_injective :
    Function.Injective (fun dt : Direction F × F ↦ line F dt.1 dt.2) := by
  rintro ⟨d, t⟩ ⟨e, s⟩ heq
  change line F d t = line F e s at heq
  have hm (p : Point F) : value F d p = t ↔ value F e p = s := by
    rw [← mem_line, ← mem_line, heq]
  cases d with
  | none =>
      cases e with
      | none =>
          have hts : t = s := (hm (0, t)).mp rfl
          simp [hts]
      | some b =>
          have h0 : b * t = s := by simpa [value] using (hm (0, t)).mp rfl
          have h1 : 1 + b * t = s := (hm (1, t)).mp rfl
          have hf : (1 : F) = 0 := by linear_combination h1 - h0
          exact False.elim (one_ne_zero hf)
  | some a =>
      cases e with
      | none =>
          have h0 : (0 : F) = s := by
            apply (hm (t, 0)).mp
            simp [value]
          have h1 : (1 : F) = s := by
            apply (hm (t - a, 1)).mp
            simp [value]
          have hf : (1 : F) = 0 := by linear_combination h1 - h0
          exact False.elim (one_ne_zero hf)
      | some b =>
          have hts : t = s := by
            simpa [value] using (hm (t, 0)).mp (by simp [value])
          have h1 : t - a + b = s := by
            simpa [value] using (hm (t - a, 1)).mp (by simp [value])
          have hab : a = b := by linear_combination hts - h1
          simp [hab, hts]

def blocks : Finset (Finset (Point F)) :=
  Finset.univ.image fun dt : Direction F × F ↦ line F dt.1 dt.2

theorem line_mem_blocks (d : Direction F) (t : F) : line F d t ∈ blocks F := by
  exact Finset.mem_image.mpr ⟨(d, t), Finset.mem_univ _, rfl⟩

def color (r : ℕ) (k : Direction F × Fin r) (p : Point F) : F :=
  value F k.1 p

theorem line_multiplicity (r : ℕ) (A : Finset (Point F)) (hA : A ∈ blocks F) :
    (Finset.univ.filter fun k : Direction F × Fin r ↦
      ∃ t, (Finset.univ.filter fun p ↦ color F r k p = t) = A).card = r := by
  classical
  obtain ⟨⟨d, t⟩, _, rfl⟩ := Finset.mem_image.mp hA
  have heq : (Finset.univ.filter fun k : Direction F × Fin r ↦
      ∃ s, (Finset.univ.filter fun p ↦ color F r k p = s) = line F d t) =
      ({d} : Finset (Direction F)) ×ˢ (Finset.univ : Finset (Fin r)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton, and_true]
    constructor
    · rintro ⟨s, hs⟩
      have hp : (k.1, s) = (d, t) := by
        apply line_injective F
        exact hs
      exact congrArg Prod.fst hp
    · intro hk
      exact ⟨t, by simp only [color, hk, line]⟩
  rw [heq]
  simp

theorem color_hall (r : ℕ) (hr : 2 * r ≤ Fintype.card F)
    (T : Finset (Point F)) (hT : T.card < Fintype.card (Direction F × Fin r)) :
    (Finset.univ.filter fun k : Direction F × Fin r ↦
      ∃ t, (Finset.univ.filter fun p ↦ color F r k p = t) ⊆ T).card ≤ T.card := by
  classical
  apply BlockDesignHall.color_hall_of_contained_bound r (blocks F) (color F r)
  · intro k t
    exact line_mem_blocks F k.1 t
  · intro A hA
    exact le_of_eq (line_multiplicity F r A hA)
  · intro U hU
    apply BlockDesignHall.contained_lines_weight_bound (Fintype.card F) r (blocks F)
    · intro A hA
      obtain ⟨⟨d, t⟩, _, rfl⟩ := Finset.mem_image.mp hA
      exact card_line F d t
    · intro A hA B hB hne
      obtain ⟨⟨d, t⟩, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨⟨e, s⟩, _, rfl⟩ := Finset.mem_image.mp hB
      exact intersection_card_le_one F d e t s hne
    · simp only [Fintype.card_prod, card_direction, Fintype.card_fin] at hU
      nlinarith [Nat.mul_le_mul_left (Fintype.card F + 1) hr]
    · exact hr
  · exact hT

theorem exists_representatives (r : ℕ) (hr : 2 * r ≤ Fintype.card F)
    (target : Direction F × Fin r → F) :
    ∃ f : Direction F × Fin r → Point F,
      Function.Injective f ∧ ∀ k, color F r k (f k) = target k := by
  exact MultiaffinePermutation.exists_color_representatives (color F r)
    (color_hall F r hr) target

/-- The affine-line construction, with all matching hypotheses discharged. -/
theorem exists_positive_multiaffine_tests (r b : ℕ) (hr : 2 * r ≤ Fintype.card F)
    (encode : F ≃ (Fin b → Bool)) :
    ∃ P : (Direction F × Fin r) × Fin b → MvPolynomial (Point F) ℝ,
      (∀ j v, (P j).degreeOf v ≤ 1) ∧
      ∀ label : (Direction F × Fin r) × Fin b → Bool,
        ∃ z : Point F → ℝ, (∀ v, 0 < z v) ∧
          ∀ j, MvPolynomial.eval z (P j) = if label j then 1 else -1 := by
  classical
  let a : Point F → ℝ := fun p ↦ ((Fintype.equivFin (Point F) p).val : ℝ) + 1
  have ha : Function.Injective a := by
    intro p p' hp
    apply (Fintype.equivFin (Point F)).injective
    apply Fin.ext
    have he : ((Fintype.equivFin (Point F) p).val : ℝ) =
        ((Fintype.equivFin (Point F) p').val : ℝ) := by
      change _ + 1 = _ + 1 at hp
      linarith
    exact_mod_cast he
  have hpos (p : Point F) : 0 < a p := by dsimp [a]; positivity
  have hcard : Fintype.card (Direction F × Fin r) ≤ Fintype.card (Point F) := by
    rw [Fintype.card_prod, card_direction, Fintype.card_fin, card_point]
    have hq := Fintype.one_lt_card (α := F)
    nlinarith [Nat.mul_le_mul_left (Fintype.card F + 1) hr]
  obtain ⟨position⟩ := Function.Embedding.nonempty_of_card_le hcard
  let P : (Direction F × Fin r) × Fin b → MvPolynomial (Point F) ℝ := fun j ↦
    MultiaffinePermutation.decoder a
      (fun p ↦ if encode (color F r j.1 p) j.2 then 1 else -1) (position j.1)
  refine ⟨P, ?_, ?_⟩
  · intro j v
    exact MultiaffinePermutation.decoder_degreeOf_le_one _ _ _ _
  · intro label
    obtain ⟨f, hf, hfc⟩ := exists_representatives F r hr
      (fun k ↦ encode.symm (fun j ↦ label (k, j)))
    obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair position f position.injective hf
    refine ⟨a ∘ e, fun v ↦ hpos (e v), ?_⟩
    intro j
    change MvPolynomial.eval (a ∘ e) (MultiaffinePermutation.decoder a
      (fun p ↦ if encode (color F r j.1 p) j.2 then 1 else -1) (position j.1)) = _
    rw [MultiaffinePermutation.decoder_eval_permutation a _ ha e, he, hfc]
    simp

theorem exists_positive_multiaffine_tests_fin (r b : ℕ)
    (hr : 2 * r ≤ Fintype.card F) (encode : F ≃ (Fin b → Bool)) :
    ∃ P : Fin ((Fintype.card F + 1) * r * b) →
        MvPolynomial (Fin (Fintype.card F ^ 2)) ℝ,
      (∀ j v, (P j).degreeOf v ≤ 1) ∧
      ∀ label : Fin ((Fintype.card F + 1) * r * b) → Bool,
        ∃ z : Fin (Fintype.card F ^ 2) → ℝ, (∀ v, 0 < z v) ∧
          ∀ j, MvPolynomial.eval z (P j) = if label j then 1 else -1 := by
  classical
  obtain ⟨P, hdegree, hshatter⟩ := exists_positive_multiaffine_tests F r b hr encode
  let eV := Fintype.equivFinOfCardEq (card_point F)
  have hj : Fintype.card ((Direction F × Fin r) × Fin b) =
      (Fintype.card F + 1) * r * b := by
    simp only [Fintype.card_prod, card_direction, Fintype.card_fin]
  let eJ := Fintype.equivFinOfCardEq hj
  let Q := fun j ↦ MvPolynomial.rename eV (P (eJ.symm j))
  refine ⟨Q, ?_, ?_⟩
  · intro j v
    have he := MvPolynomial.degreeOf_rename_of_injective
      (p := P (eJ.symm j)) eV.injective (eV.symm v)
    change (MvPolynomial.rename eV (P (eJ.symm j))).degreeOf v ≤ 1
    simpa only [Equiv.apply_symm_apply] using he.trans_le (hdegree _ _)
  · intro label
    obtain ⟨z, hzpos, hz⟩ := hshatter (label ∘ eJ)
    refine ⟨z ∘ eV.symm, fun v ↦ hzpos (eV.symm v), ?_⟩
    intro j
    change MvPolynomial.eval (z ∘ eV.symm)
      (MvPolynomial.rename eV (P (eJ.symm j))) = _
    rw [MvPolynomial.eval_rename]
    simpa [Function.comp_def] using hz (eJ.symm j)

/-- An explicit numerical instance: 108 independent tests on 64 positive
parameters, with individual degree at most one. -/
theorem exists_108_tests_on_64_positive_parameters :
    ∃ P : Fin 108 → MvPolynomial (Fin 64) ℝ,
      (∀ j v, (P j).degreeOf v ≤ 1) ∧
      ∀ label : Fin 108 → Bool, ∃ z : Fin 64 → ℝ,
        (∀ v, 0 < z v) ∧
        ∀ j, MvPolynomial.eval z (P j) = if label j then 1 else -1 := by
  classical
  let F := GaloisField 2 3
  let : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 3 (by decide)
  let encode : F ≃ (Fin 3 → Bool) := Fintype.equivOfCardEq (by simp [hq])
  have h := exists_positive_multiaffine_tests_fin F 4 3 (by omega) encode
  rw [hq] at h
  exact h

/-- No universal linear bound on the number of independently realizable
multiaffine sign tests follows from separate affinity and parameter positivity. -/
theorem unbounded_multiaffine_tests_per_positive_parameter (K : ℕ) :
    ∃ p m : ℕ, K * p < m ∧
      ∃ P : Fin m → MvPolynomial (Fin p) ℝ,
        (∀ j v, (P j).degreeOf v ≤ 1) ∧
        ∀ label : Fin m → Bool, ∃ z : Fin p → ℝ,
          (∀ v, 0 < z v) ∧
          ∀ j, MvPolynomial.eval z (P j) = if label j then 1 else -1 := by
  classical
  let b := 2 * K + 2
  let r := 2 ^ (2 * K + 1)
  let q := 2 ^ b
  let F := GaloisField 2 b
  let : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 b (by dsimp [b]; omega)
  have hqr : q = 2 * r := by
    dsimp [q, b, r]
    rw [show 2 * K + 2 = (2 * K + 1) + 1 by omega, pow_succ]
    ring
  have hrpos : 0 < r := by dsimp [r]; positivity
  let encode : F ≃ (Fin b → Bool) := Fintype.equivOfCardEq (by simp [hq, q])
  have h := exists_positive_multiaffine_tests_fin F r b (by omega) encode
  refine ⟨q ^ 2, (q + 1) * r * b, ?_, ?_⟩
  · dsimp [b]
    rw [hqr]
    nlinarith [sq_pos_of_pos hrpos]
  · rw [hq] at h
    exact h

end HeadComplexity.FiniteFieldLines
