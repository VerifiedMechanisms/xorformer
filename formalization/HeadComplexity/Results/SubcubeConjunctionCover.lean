import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

set_option linter.style.header false

/-! A subcube-cover proof of the classical `(3/2)^n` lower bound for
literal-conjunction sign representations of parity. This is an obstruction
to a proposed compiler, not a lower bound for attention heads. -/
namespace HeadComplexity.SubcubeConjunctionCover
open scoped BigOperators

variable {n : ℕ}

def bitSign (b : Bool) : ℝ := if b then -1 else 1

def indicator (a : Option Bool) (b : Bool) : ℝ :=
  match a with
  | none => 1
  | some c => if b = c then 1 else 0

def parity (x : Fin n → Bool) : ℝ := ∏ i, bitSign (x i)

def conjunction (a : Fin n → Option Bool) (x : Fin n → Bool) : ℝ :=
  ∏ i, indicator (a i) (x i)

def alternatingSum (face : Fin n → Option Bool) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ x, conjunction face x * parity x * f x

def coordinateCover (term face : Option Bool) : Prop :=
  match term, face with
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some b, some c => b = c

def Covers (term face : Fin n → Option Bool) : Prop :=
  ∀ i, coordinateCover (term i) (face i)

theorem indicator_nonneg (a : Option Bool) (b : Bool) : 0 ≤ indicator a b := by
  cases a with
  | none => norm_num [indicator]
  | some c => cases b <;> cases c <;> norm_num [indicator]

theorem alternatingSum_conjunction (a face : Fin n → Option Bool) :
    alternatingSum face (conjunction a) =
      ∏ i, ∑ b : Bool, indicator (face i) b * bitSign b * indicator (a i) b := by
  unfold alternatingSum conjunction parity
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (b : Bool) ↦
    indicator (face i) b * bitSign b * indicator (a i) b)).symm

theorem coordinate_sum_zero_of_not_cover (a face : Option Bool)
    (h : ¬ coordinateCover a face) :
    ∑ b : Bool, indicator face b * bitSign b * indicator a b = 0 := by
  cases a with
  | none => cases face <;> simp_all [coordinateCover, indicator, bitSign]
  | some b =>
    cases face with
    | none => simp [coordinateCover] at h
    | some c =>
      cases b <;> cases c <;>
        norm_num [coordinateCover, indicator, bitSign] at *

theorem alternatingSum_zero_of_not_covers (a face : Fin n → Option Bool)
    (h : ¬ Covers a face) : alternatingSum face (conjunction a) = 0 := by
  rw [alternatingSum_conjunction]
  obtain ⟨i, hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (coordinate_sum_zero_of_not_cover _ _ hi)

theorem alternatingSum_pos (face : Fin n → Option Bool)
    (f : (Fin n → Bool) → ℝ) (hf : ∀ x, 0 < parity x * f x) :
    0 < alternatingSum face f := by
  let x : Fin n → Bool := fun i ↦ (face i).getD false
  have hx : conjunction face x = 1 := by
    apply Finset.prod_eq_one
    intro i _
    cases hi : face i <;> simp [indicator, x, hi]
  unfold alternatingSum
  apply Finset.sum_pos'
  · intro y _
    rw [mul_assoc]
    exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ indicator_nonneg _ _) (hf y).le
  · exact ⟨x, Finset.mem_univ x, by rw [hx, one_mul]; exact hf x⟩

theorem representation_covers {ι : Type*} [Fintype ι]
    (a : ι → Fin n → Option Bool) (c : ι → ℝ)
    (hf : ∀ x, 0 < parity x * ∑ j, c j * conjunction (a j) x)
    (face : Fin n → Option Bool) : ∃ j, Covers (a j) face := by
  classical
  by_contra h
  push Not at h
  have hz : alternatingSum face (fun x ↦ ∑ j, c j * conjunction (a j) x) = 0 := by
    unfold alternatingSum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have he : (∑ x, conjunction face x * parity x * (c j * conjunction (a j) x)) =
        c j * alternatingSum face (conjunction (a j)) := by
      unfold alternatingSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [he, alternatingSum_zero_of_not_covers _ _ (h j), mul_zero]
  exact (ne_of_gt (alternatingSum_pos face _ hf)) hz

def coveredFace (a : Fin n → Option Bool) (bits : Fin n → Bool) :
    Fin n → Option Bool := fun i ↦
  match a i with
  | none => some (bits i)
  | some b => if bits i then some b else none

theorem covers_has_code (a face : Fin n → Option Bool) (h : Covers a face) :
    ∃ bits, coveredFace a bits = face := by
  let bits : Fin n → Bool := fun i ↦
    match a i with
    | none => (face i).getD false
    | some _ => (face i).isSome
  refine ⟨bits, ?_⟩
  funext i
  have hi := h i
  cases ha : a i with
  | none =>
    cases hf : face i <;> simp_all [coordinateCover, coveredFace, bits]
  | some b =>
    cases hf : face i <;> simp_all [coordinateCover, coveredFace, bits]

/-- The classical literal-conjunction density bound, without any coefficient
or margin restrictions. The proof covers all `3^n` faces by `2^n` possible
faces per summand. -/
theorem parity_conjunction_count {ι : Type*} [Fintype ι]
    (a : ι → Fin n → Option Bool) (c : ι → ℝ)
    (hf : ∀ x, 0 < parity x * ∑ j, c j * conjunction (a j) x) :
    3 ^ n ≤ Fintype.card ι * 2 ^ n := by
  let code : (ι × (Fin n → Bool)) → (Fin n → Option Bool) :=
    fun jb ↦ coveredFace (a jb.1) jb.2
  have hs : Function.Surjective code := by
    intro face
    obtain ⟨j, hj⟩ := representation_covers a c hf face
    obtain ⟨bits, hbits⟩ := covers_has_code (a j) face hj
    exact ⟨(j, bits), hbits⟩
  have hcard := Fintype.card_le_of_surjective code hs
  simpa using hcard

end HeadComplexity.SubcubeConjunctionCover
