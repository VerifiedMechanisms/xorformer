import HeadComplexity.Atoms.WeightedAtom
import HeadComplexity.Polynomial.ThresholdDegree
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.style.header false

/-! An explicit family of quadratically represented Boolean functions with
2^(k^3) distinct truth tables on three blocks of k bits. This audits the cost
of treating arbitrary reciprocal second-order jets as a bounded number of heads. -/
namespace HeadComplexity.QuadraticThresholdEncoding

open Finset
open scoped BigOperators

abbrev Bits (k : ℕ) := Fin k → Bool
abbrev Parameters (k : ℕ) := (Fin k × Fin k) → Bits k
abbrev Input (k : ℕ) := Bits k × Bits k × Bits k

noncomputable def address {k : ℕ} (x : Bits k) : ℝ :=
  wT (fun i ↦ (2 : ℝ) ^ i.val) x

def unit {k : ℕ} (j : Fin k) : Bits k := fun i ↦ decide (i = j)

noncomputable def score {k : ℕ} (T : Parameters k) (x y z : Bits k) : ℝ :=
  address x * (∑ l, boolToReal (z l)) -
    ∑ j, ∑ l, address (T (j, l)) * boolToReal (y j) * boolToReal (z l)

theorem score_units {k : ℕ} (T : Parameters k) (x : Bits k) (j l : Fin k) :
    score T x (unit j) (unit l) = address x - address (T (j, l)) := by
  classical
  simp [score, unit, boolToReal, mul_ite]

noncomputable def family {k : ℕ} (T : Parameters k) (input : Input k) : Bool :=
  decide (0 < score T input.1 input.2.1 input.2.2)

abbrev Coordinate (k : ℕ) := Fin k ⊕ (Fin k ⊕ Fin k)

noncomputable def polynomial {k : ℕ} (T : Parameters k) :
    MvPolynomial (Coordinate k) ℝ :=
  (∑ i, MvPolynomial.C ((2 : ℝ) ^ i.val) * MvPolynomial.X (Sum.inl i)) *
    (∑ l, MvPolynomial.X (Sum.inr (Sum.inr l))) -
  ∑ j, ∑ l, MvPolynomial.C (address (T (j, l))) *
    MvPolynomial.X (Sum.inr (Sum.inl j)) * MvPolynomial.X (Sum.inr (Sum.inr l))

noncomputable def evaluationPoint {k : ℕ} (x y z : Bits k) : Coordinate k → ℝ :=
  Sum.elim (fun i ↦ boolToReal (x i))
    (Sum.elim (fun j ↦ boolToReal (y j)) (fun l ↦ boolToReal (z l)))

theorem polynomial_eval {k : ℕ} (T : Parameters k) (x y z : Bits k) :
    MvPolynomial.eval (evaluationPoint x y z) (polynomial T) = score T x y z := by
  simp [polynomial, evaluationPoint, score, address, wT, boolToReal, mul_ite]

theorem polynomial_totalDegree_le {k : ℕ} (T : Parameters k) :
    (polynomial T).totalDegree ≤ 2 := by
  classical
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    have hleft : (∑ i : Fin k, MvPolynomial.C ((2 : ℝ) ^ i.val) *
        MvPolynomial.X (Sum.inl i : Coordinate k)).totalDegree ≤ 1 := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i _
      simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]
        using MvPolynomial.totalDegree_mul
        (MvPolynomial.C ((2 : ℝ) ^ i.val)) (MvPolynomial.X (Sum.inl i : Coordinate k))
    have hright : (∑ l : Fin k,
        MvPolynomial.X (Sum.inr (Sum.inr l) : Coordinate k) :
          MvPolynomial (Coordinate k) ℝ).totalDegree ≤ 1 := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro l _
      simp
    omega
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l _
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (address (T (j, l))))
      (MvPolynomial.X (Sum.inr (Sum.inl j) : Coordinate k))
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] at h ⊢
    omega

theorem family_injective (k : ℕ) : Function.Injective (family (k := k)) := by
  classical
  intro T U h
  funext jl
  rcases jl with ⟨j, l⟩
  apply wT_two_pow_injective
  change address (T (j, l)) = address (U (j, l))
  apply le_antisymm
  · by_contra! hlt
    have heq := congrFun h (T (j, l), unit j, unit l)
    have hpos : 0 < address (T (j, l)) - address (U (j, l)) := sub_pos.mpr hlt
    simp [family, score_units, hpos] at heq
  · by_contra! hlt
    have heq := congrFun h (U (j, l), unit j, unit l)
    have hpos : 0 < address (U (j, l)) - address (T (j, l)) := sub_pos.mpr hlt
    simp [family, score_units, hpos] at heq

theorem parameters_card (k : ℕ) : Fintype.card (Parameters k) = 2 ^ (k ^ 3) := by
  simp only [Parameters, Bits, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, ← pow_mul]
  congr 1
  ring

theorem family_card (k : ℕ) :
    Fintype.card (Set.range (family (k := k))) = 2 ^ (k ^ 3) := by
  classical
  rw [Set.card_range_of_injective (family_injective k), parameters_card]

theorem input_card (k : ℕ) : Fintype.card (Input k) = 2 ^ (3 * k) := by
  simp only [Input, Bits, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, ← pow_add]
  congr 1
  ring

theorem exists_outside (k : ℕ) (C : Finset (Input k → Bool))
    (hC : C.card < 2 ^ (k ^ 3)) : ∃ T : Parameters k, family T ∉ C := by
  classical
  by_contra! h
  let g : Parameters k → C := fun T ↦ ⟨family T, h T⟩
  have hginj : Function.Injective g := by
    intro T U hTU
    exact family_injective k (congrArg Subtype.val hTU)
  have hcard := Fintype.card_le_of_injective g hginj
  have hle : 2 ^ (k ^ 3) ≤ C.card := by
    simpa only [parameters_card, Fintype.card_coe] using hcard
  omega

theorem head_count_exponent_lt (k H : ℕ) (hk : 3 ≤ k) (hH : 24 * H ≤ k) :
    1 + 2 * (3 * k) * H * (3 * k + 1) < k ^ 3 := by
  have h₁ := Nat.mul_le_mul_right (k * (3 * k + 1)) hH
  have h₂ := Nat.mul_le_mul_left (k ^ 2) hk
  have h₃ : 9 ≤ k ^ 2 := by nlinarith
  nlinarith

end HeadComplexity.QuadraticThresholdEncoding
