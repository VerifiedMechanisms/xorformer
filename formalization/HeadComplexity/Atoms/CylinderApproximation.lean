import HeadComplexity.Atoms.FracAtomSymmetry
import HeadComplexity.Atoms.UniformApproximationSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset

set_option linter.style.header false

/-!
# Uniform approximation of Boolean cylinders

A cylinder fixes one set of coordinates to true and a disjoint set to false.
Expanding either orientation expresses its indicator as a sum of pure positive
or pure negative squarefree monomials.  Choosing the cheaper expansion gives
the cylinder cost from theorem 96.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- A partial Boolean assignment, represented by disjoint positive and
negative coordinate sets. -/
structure CubeCylinder (n : ℕ) where
  positive : Finset (Fin n)
  negative : Finset (Fin n)
  disjoint : Disjoint positive negative

namespace CubeCylinder

/-- Real-valued indicator of a Boolean cylinder. -/
def eval (C : CubeCylinder n) (bits : Fin n → Bool) : ℝ :=
  (∏ i ∈ C.positive, boolToReal (bits i)) *
    ∏ i ∈ C.negative, (1 - boolToReal (bits i))

/-- Raw-calibration cost of a cylinder. -/
def cost (C : CubeCylinder n) : ℕ :=
  if C.positive = ∅ ∧ C.negative = ∅ then 0
  else min (2 ^ C.positive.card) (2 ^ C.negative.card)

/-- The pure negative squarefree monomial on a coordinate set. -/
def negativeSquarefreeMonomial (S : Finset (Fin n))
    (bits : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, (1 - boolToReal (bits i))

/-- The cylinder containing exactly one Boolean input. -/
def point (target : Fin n → Bool) : CubeCylinder n where
  positive := Finset.univ.filter fun i ↦ target i = true
  negative := Finset.univ.filter fun i ↦ target i = false
  disjoint := by
    rw [Finset.disjoint_left]
    simp

/-- The positive cylinder associated with a squarefree monomial. -/
def positiveMonomial (S : Finset (Fin n)) : CubeCylinder n where
  positive := S
  negative := ∅
  disjoint := Finset.disjoint_empty_right S

@[simp] theorem eval_positiveMonomial (S : Finset (Fin n))
    (bits : Fin n → Bool) :
    (positiveMonomial S).eval bits = squarefreeMonomial S bits := by
  simp [positiveMonomial, eval, squarefreeMonomial]

@[simp] theorem cost_positiveMonomial {S : Finset (Fin n)}
  (hS : S.Nonempty) :
    (positiveMonomial S).cost = 1 := by
  simp [positiveMonomial, cost, hS.ne_empty, Nat.one_le_two_pow]

@[simp] theorem eval_point_self (target : Fin n → Bool) :
    (point target).eval target = 1 := by
  unfold point eval
  rw [show (∏ i ∈ Finset.univ.filter (fun i ↦ target i = true),
      boolToReal (target i)) = 1 by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [boolToReal, hi],
    show (∏ i ∈ Finset.univ.filter (fun i ↦ target i = false),
      (1 - boolToReal (target i))) = 1 by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [boolToReal, hi]]
  norm_num

/-- A point cylinder is the Kronecker indicator of its target input. -/
theorem eval_point (target bits : Fin n → Bool) :
    (point target).eval bits = if bits = target then 1 else 0 := by
  classical
  by_cases heq : bits = target
  · subst bits
    simp
  · rw [if_neg heq]
    have hex : ∃ i, bits i ≠ target i := by
      by_contra h
      push Not at h
      exact heq (funext h)
    obtain ⟨i, hi⟩ := hex
    unfold point eval
    cases ht : target i <;> cases hb : bits i
    · simp_all
    · apply mul_eq_zero.mpr
      right
      apply Finset.prod_eq_zero (i := i)
      · simp [ht]
      · simp [hb, boolToReal]
    · apply mul_eq_zero.mpr
      left
      apply Finset.prod_eq_zero (i := i)
      · simp [ht]
      · simp [hb, boolToReal]
    · simp_all

theorem squarefreeMonomial_flipBits (S : Finset (Fin n))
    (bits : Fin n → Bool) :
    squarefreeMonomial S (flipBits bits) =
      negativeSquarefreeMonomial S bits := by
  unfold squarefreeMonomial negativeSquarefreeMonomial
  apply Finset.prod_congr rfl
  intro i _
  cases hi : bits i <;> simp [flipBits, hi, boolToReal]

/-- Pure negative monomials inherit one-atom approximation from pure positive
monomials by simultaneous input complementation. -/
theorem uniformlyOneAtomApproximable_signedNegativeMonomial
    (S : Finset (Fin n)) (a : ℝ) :
    UniformlyOneAtomApproximable
      (fun bits ↦ a * negativeSquarefreeMonomial S bits) := by
  intro ε hε
  obtain ⟨phi, hphi⟩ :=
    exists_fracAtom_approx_signedMonomial S a ε hε
  refine ⟨phi.flip, fun bits ↦ ?_⟩
  simpa only [FracAtom.flip_eval, squarefreeMonomial_flipBits] using
    hphi (flipBits bits)

/-- A fixed finite sum of one-atom-approximable scores is uniformly
approximable by the same finite atom type. -/
theorem uniformlyAtomsApproximable_fin_sum
    (g : Fin H → (Fin n → Bool) → ℝ)
    (hg : ∀ h, UniformlyOneAtomApproximable (g h)) :
    UniformlyAtomsApproximable (Fin H) (fun bits ↦ ∑ h, g h bits) := by
  intro ε hε
  let δ : ℝ := ε / (H + 1 : ℝ)
  have hden : (0 : ℝ) < H + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  choose phi hphi using fun h ↦ hg h δ hδ
  refine ⟨phi, 0, fun bits ↦ ?_⟩
  simp only [zero_add]
  rw [← Finset.sum_sub_distrib]
  have habs : |∑ h, ((phi h).eval bits - g h bits)| ≤
      ∑ h, |(phi h).eval bits - g h bits| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum : (∑ h, |(phi h).eval bits - g h bits|) ≤ H * δ := by
    calc
      (∑ h, |(phi h).eval bits - g h bits|) ≤ ∑ _h : Fin H, δ :=
        Finset.sum_le_sum fun h _ ↦ (hphi h bits).le
      _ = H * δ := by simp
  have hbudget : (H : ℝ) * δ < ε := by
    have hratio : (H : ℝ) / (H + 1 : ℝ) < 1 := by
      rw [div_lt_one hden]
      norm_num
    dsimp [δ]
    calc
      (H : ℝ) * (ε / (H + 1 : ℝ)) =
          ε * ((H : ℝ) / (H + 1 : ℝ)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := mul_one ε
  exact habs.trans_lt (hsum.trans_lt hbudget)

/-- Positive-oriented inclusion-exclusion expansion of a cylinder. -/
theorem eval_eq_positiveExpansion (C : CubeCylinder n)
    (bits : Fin n → Bool) :
    C.eval bits =
      ∑ U ∈ C.negative.powerset,
        (-1 : ℝ) ^ U.card * squarefreeMonomial (C.positive ∪ U) bits := by
  classical
  unfold eval squarefreeMonomial
  rw [Finset.prod_sub (fun _ ↦ (1 : ℝ))
    (fun i ↦ boolToReal (bits i)) C.negative]
  simp only [Finset.prod_const_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hsubset : U ⊆ C.negative := Finset.mem_powerset.mp hU
  have hdisj : Disjoint C.positive U := C.disjoint.mono_right hsubset
  rw [Finset.prod_union hdisj]
  ring

/-- Negative-oriented inclusion-exclusion expansion of a cylinder. -/
theorem eval_eq_negativeExpansion (C : CubeCylinder n)
    (bits : Fin n → Bool) :
    C.eval bits =
      ∑ U ∈ C.positive.powerset,
        (-1 : ℝ) ^ U.card *
          negativeSquarefreeMonomial (C.negative ∪ U) bits := by
  classical
  unfold eval negativeSquarefreeMonomial
  have hpositive :
      (∏ i ∈ C.positive, boolToReal (bits i)) =
        ∑ U ∈ C.positive.powerset,
          (-1 : ℝ) ^ U.card *
            ∏ i ∈ U, (1 - boolToReal (bits i)) := by
    rw [show (∏ i ∈ C.positive, boolToReal (bits i)) =
        ∏ i ∈ C.positive, ((1 : ℝ) - (1 - boolToReal (bits i))) by
      apply Finset.prod_congr rfl
      intro i _
      ring]
    rw [Finset.prod_sub (fun _ ↦ (1 : ℝ))
      (fun i ↦ 1 - boolToReal (bits i)) C.positive]
    simp only [Finset.prod_const_one, mul_one]
  rw [hpositive, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro U hU
  have hsubset : U ⊆ C.positive := Finset.mem_powerset.mp hU
  have hdisj : Disjoint C.negative U := C.disjoint.symm.mono_right hsubset
  rw [Finset.prod_union hdisj]
  ring

/-- A constant score uses no atoms and the free block constant. -/
theorem uniformlyAtomsApproximable_const (c : ℝ) :
    UniformlyAtomsApproximable (Fin 0)
      (fun _ : Fin n → Bool ↦ c) := by
  intro ε hε
  refine ⟨Fin.elim0, c, fun bits ↦ ?_⟩
  simpa using hε

private theorem positiveExpansion_uniformlyAtomsApproximable
    (C : CubeCylinder n) (a : ℝ) :
    UniformlyAtomsApproximable (Fin C.negative.powerset.card)
      (fun bits ↦ a * C.eval bits) := by
  classical
  let e : {U // U ∈ C.negative.powerset} ≃
      Fin C.negative.powerset.card := C.negative.powerset.equivFin
  let g : Fin C.negative.powerset.card → (Fin n → Bool) → ℝ :=
    fun j bits ↦
      let U := (e.symm j).1
      (a * (-1 : ℝ) ^ U.card) *
        squarefreeMonomial (C.positive ∪ U) bits
  have hg : ∀ j, UniformlyOneAtomApproximable (g j) := by
    intro j
    exact uniformlyOneAtomApproximable_signedMonomial
      (C.positive ∪ (e.symm j).1)
      (a * (-1 : ℝ) ^ (e.symm j).1.card)
  have hsum : ∀ bits, (∑ j, g j bits) = a * C.eval bits := by
    intro bits
    rw [C.eval_eq_positiveExpansion bits, Finset.mul_sum]
    dsimp [g]
    rw [show (∑ j : Fin C.negative.powerset.card,
        (a * (-1 : ℝ) ^ (e.symm j).1.card) *
          squarefreeMonomial (C.positive ∪ (e.symm j).1) bits) =
        ∑ U ∈ C.negative.powerset,
          (a * (-1 : ℝ) ^ U.card) *
            squarefreeMonomial (C.positive ∪ U) bits by
      rw [← C.negative.powerset.sum_attach,
        Finset.attach_eq_univ, ← e.symm.sum_comp]]
    apply Finset.sum_congr rfl
    intro U _
    ring
  have happ := uniformlyAtomsApproximable_fin_sum g hg
  simpa only [hsum] using happ

private theorem negativeExpansion_uniformlyAtomsApproximable
    (C : CubeCylinder n) (a : ℝ) :
    UniformlyAtomsApproximable (Fin C.positive.powerset.card)
      (fun bits ↦ a * C.eval bits) := by
  classical
  let e : {U // U ∈ C.positive.powerset} ≃
      Fin C.positive.powerset.card := C.positive.powerset.equivFin
  let g : Fin C.positive.powerset.card → (Fin n → Bool) → ℝ :=
    fun j bits ↦
      let U := (e.symm j).1
      (a * (-1 : ℝ) ^ U.card) *
        negativeSquarefreeMonomial (C.negative ∪ U) bits
  have hg : ∀ j, UniformlyOneAtomApproximable (g j) := by
    intro j
    exact uniformlyOneAtomApproximable_signedNegativeMonomial
      (C.negative ∪ (e.symm j).1)
      (a * (-1 : ℝ) ^ (e.symm j).1.card)
  have hsum : ∀ bits, (∑ j, g j bits) = a * C.eval bits := by
    intro bits
    rw [C.eval_eq_negativeExpansion bits, Finset.mul_sum]
    dsimp [g]
    rw [show (∑ j : Fin C.positive.powerset.card,
        (a * (-1 : ℝ) ^ (e.symm j).1.card) *
          negativeSquarefreeMonomial (C.negative ∪ (e.symm j).1) bits) =
        ∑ U ∈ C.positive.powerset,
          (a * (-1 : ℝ) ^ U.card) *
            negativeSquarefreeMonomial (C.negative ∪ U) bits by
      rw [← C.positive.powerset.sum_attach,
        Finset.attach_eq_univ, ← e.symm.sum_comp]]
    apply Finset.sum_congr rfl
    intro U _
    ring
  have happ := uniformlyAtomsApproximable_fin_sum g hg
  simpa only [hsum] using happ

/-- Every signed cylinder is uniformly approximable using its orientation
cost, with a free constant for the vacuous cylinder. -/
theorem uniformlyAtomsApproximable (C : CubeCylinder n) (a : ℝ) :
    UniformlyAtomsApproximable (Fin C.cost)
      (fun bits ↦ a * C.eval bits) := by
  classical
  by_cases hvac : C.positive = ∅ ∧ C.negative = ∅
  · rw [cost, if_pos hvac]
    obtain ⟨hp, hn⟩ := hvac
    have heval : ∀ bits, C.eval bits = 1 := by
      intro bits
      simp [eval, hp, hn]
    simpa only [heval, mul_one] using
      (uniformlyAtomsApproximable_const (n := n) a)
  · by_cases horient : 2 ^ C.positive.card ≤ 2 ^ C.negative.card
    · rw [cost, if_neg hvac, Nat.min_eq_left horient]
      rw [← Finset.card_powerset]
      exact negativeExpansion_uniformlyAtomsApproximable C a
    · have horient' : 2 ^ C.negative.card ≤ 2 ^ C.positive.card :=
        Nat.le_of_not_ge horient
      rw [cost, if_neg hvac, Nat.min_eq_right horient']
      rw [← Finset.card_powerset]
      exact positiveExpansion_uniformlyAtomsApproximable C a

end CubeCylinder

end HeadComplexity
