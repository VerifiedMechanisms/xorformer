import HeadComplexity.Research.UniformClusterCapacity

set_option linter.style.header false
set_option maxRecDepth 1500

/-!
Polynomial capacity for reciprocal scores in filtered finite-dimensional
algebras. All multiplication slots are charged and their associativity
relations are discarded in the counting class. This does not supply an
access theorem from unrestricted original xorformers.
-/

noncomputable section
namespace HeadComplexity.FilteredAlgebraCapacity
open MvPolynomial PolynomialRootCount
open scoped BigOperators

/-- Here q is the number of nonidentity basis vectors, so each algebra has
length q+1. The right summand contains every ordered multiplication slot. -/
abbrev Parameter (n G q : ℕ) := Unit ⊕
  (Fin G × ((Bool × Option (Fin q) × Option (Fin n)) ⊕ (Fin q × Fin q × Fin q)))

@[simp] theorem card_parameter (n G q : ℕ) :
    Fintype.card (Parameter n G q) = 1 + 2 * (n + 1) * (G * (q + 1)) + G * q ^ 3 := by
  simp [Parameter]
  ring

def weight (n G q : ℕ) (k : Fin G → Fin q → ℕ) : Parameter n G q → ℕ
  | Sum.inl _ => G * (q + 1)
  | Sum.inr (_, Sum.inl (false, none, _)) => 1
  | Sum.inr (_, Sum.inl (true, none, _)) => G * (q + 1)
  | Sum.inr (g, Sum.inl (false, some i, _)) => G * k g i + 1
  | Sum.inr (g, Sum.inl (true, some i, _)) => G * (q + 1 - k g i)
  | Sum.inr (g, Sum.inr (i, j, l)) => G * (k g l - k g i - k g j) + 1

variable {n G q : ℕ}

def affinePoly (kind : Bool) (g : Fin G) (i : Option (Fin q)) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inr (g, Sum.inl (kind, i, none))) +
    ∑ a, C (boolToReal (x a)) * X (Sum.inr (g, Sum.inl (kind, i, some a)))

def structurePoly (g : Fin G) (i j l : Fin q) : MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inr (g, Sum.inr (i, j, l)))

/-- Coordinate of U^(m+1), using a fixed recursive multiplication. -/
def nilpotentPower (k : Fin G → Fin q → ℕ) (g : Fin G) (x : Fin n → Bool) :
    ℕ → Fin q → MvPolynomial (Parameter n G q) ℝ
  | 0, l => affinePoly false g (some l) x
  | m + 1, l => ∑ i : Fin q, ∑ j : Fin q,
      if k g i + k g j ≤ k g l then
        affinePoly false g (some i) x * nilpotentPower k g x m j * structurePoly g i j l
      else 0

theorem affinePoly_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (kind : Bool) (g : Fin G) (i : Option (Fin q)) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (affinePoly kind g i x)
      (weight n G q k (Sum.inr (g, Sum.inl (kind, i, none)))) := by
  unfold affinePoly
  apply weightedDegreeLE_add (weightedDegreeLE_X _ _)
  apply weightedDegreeLE_sum Finset.univ
  intro a _
  apply weightedDegreeLE_C_mul
  cases kind <;> cases i <;> exact weightedDegreeLE_X _ _

theorem nilpotentPower_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (g : Fin G) (x : Fin n → Bool) (m : ℕ) (l : Fin q) :
    WeightedDegreeLE (weight n G q k) (nilpotentPower k g x m l)
      (G * k g l + 2 * m + 1) := by
  induction m generalizing l with
  | zero => simpa [nilpotentPower, weight] using affinePoly_weightedDegreeLE k false g (some l) x
  | succ m ih =>
    rw [nilpotentPower]
    apply weightedDegreeLE_sum Finset.univ
    intro i _
    apply weightedDegreeLE_sum Finset.univ
    intro j _
    split
    · rename_i hij
      have hA : WeightedDegreeLE (weight n G q k) (affinePoly false g (some i) x)
          (G * k g i + 1) := affinePoly_weightedDegreeLE k false g (some i) x
      have hC : WeightedDegreeLE (weight n G q k) (structurePoly g i j l)
          (G * (k g l - k g i - k g j) + 1) := weightedDegreeLE_X _ _
      have hh := weightedDegreeLE_mul (weightedDegreeLE_mul hA (ih j)) hC
      convert hh using 1
      have he : k g l - k g i - k g j + k g i + k g j = k g l := by omega
      nlinarith [congrArg (fun a ↦ G * a) he]
    · exact weightedDegreeLE_zero _ _

theorem nilpotentPower_eq_zero_of_order (k : Fin G → Fin q → ℕ)
    (hk : ∀ g i, 0 < k g i) (g : Fin G) (x : Fin n → Bool)
    (m : ℕ) (l : Fin q) (horder : k g l < m + 1) :
    nilpotentPower k g x m l = 0 := by
  induction m generalizing l with
  | zero => have := hk g l; omega
  | succ m ih =>
    rw [nilpotentPower]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split
    · rename_i hij
      rw [ih j (by have := hk g i; omega), mul_zero, zero_mul]
    · rfl

def clusterNumerator (k : Fin G → Fin q → ℕ) (g : Fin G) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  affinePoly true g none x * affinePoly false g none x ^ q +
    ∑ m : Fin q, ∑ l : Fin q,
      C ((-1 : ℝ) ^ ((m : ℕ) + 1)) * affinePoly true g (some l) x *
        nilpotentPower k g x m l * affinePoly false g none x ^ (q - m - 1)

def clearingPoly (x : Fin n → Bool) : MvPolynomial (Parameter n G q) ℝ :=
  ∏ g : Fin G, affinePoly false g none x ^ (q + 1)

def scorePoly (k : Fin G → Fin q → ℕ) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inl ()) * clearingPoly x +
    ∑ g : Fin G, clusterNumerator k g x *
      ∏ h ∈ Finset.univ.erase g, affinePoly false h none x ^ (q + 1)

theorem clusterNumerator_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (hk : ∀ g i, k g i ≤ q) (g : Fin G) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (clusterNumerator k g x) (G * (q + 1) + 2 * q) := by
  have hB : WeightedDegreeLE (weight n G q k) (affinePoly false g none x) 1 :=
    affinePoly_weightedDegreeLE k false g none x
  unfold clusterNumerator
  apply weightedDegreeLE_add
  · have hA : WeightedDegreeLE (weight n G q k) (affinePoly true g none x) (G * (q + 1)) :=
      affinePoly_weightedDegreeLE k true g none x
    exact weightedDegreeLE_mono (weightedDegreeLE_mul hA (weightedDegreeLE_pow hB q)) (by omega)
  · apply weightedDegreeLE_sum Finset.univ
    intro m _
    apply weightedDegreeLE_sum Finset.univ
    intro l _
    have hA : WeightedDegreeLE (weight n G q k) (affinePoly true g (some l) x)
        (G * (q + 1 - k g l)) := affinePoly_weightedDegreeLE k true g (some l) x
    have hh := weightedDegreeLE_mul
      (weightedDegreeLE_mul (weightedDegreeLE_C_mul ((-1 : ℝ) ^ ((m : ℕ) + 1)) hA)
        (nilpotentPower_weightedDegreeLE k g x m l))
      (weightedDegreeLE_pow hB (q - m - 1))
    apply weightedDegreeLE_mono hh
    simp only [one_mul]
    have he : q + 1 - k g l + k g l = q + 1 := by have := hk g l; omega
    have heq : G * (q + 1 - k g l) + G * k g l = G * (q + 1) := by
      nlinarith [congrArg (fun a ↦ G * a) he]
    have := m.isLt
    omega

theorem clearingPoly_weightedDegreeLE (k : Fin G → Fin q → ℕ) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (clearingPoly x) (G * (q + 1)) := by
  have hh := weightedDegreeLE_prod Finset.univ
    (fun g (_ : g ∈ (Finset.univ : Finset (Fin G))) ↦
      weightedDegreeLE_pow (affinePoly_weightedDegreeLE k false g none x) (q + 1))
  simpa [clearingPoly, weight] using hh

theorem scorePoly_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (hk : ∀ g i, k g i ≤ q) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (scorePoly k x) (3 * (G * (q + 1))) := by
  unfold scorePoly
  apply weightedDegreeLE_add
  · exact weightedDegreeLE_mono (weightedDegreeLE_mul
      (weightedDegreeLE_X _ _) (clearingPoly_weightedDegreeLE k x)) (by simp [weight]; omega)
  · apply weightedDegreeLE_sum Finset.univ
    intro g _
    have hprod := weightedDegreeLE_prod (Finset.univ.erase g)
      (fun h (_ : h ∈ Finset.univ.erase g) ↦
        weightedDegreeLE_pow (affinePoly_weightedDegreeLE k false h none x) (q + 1))
    apply weightedDegreeLE_mono
      (weightedDegreeLE_mul (clusterNumerator_weightedDegreeLE k hk g x) hprod)
    simp only [weight, one_mul, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ g), Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hG : 0 < G := Nat.zero_lt_of_lt g.isLt
    have he : G - 1 + 1 = G := by omega
    have heq : (G - 1) * (q + 1) + (q + 1) = G * (q + 1) := by
      nlinarith [congrArg (fun a ↦ a * (q + 1)) he]
    have hqG : q ≤ G * (q + 1) := by nlinarith
    omega

theorem weight_pos (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q) (i : Parameter n G q) : 0 < weight n G q k i := by
  rcases i with _ | ⟨g, ⟨kind, i, a⟩ | ⟨i, j, l⟩⟩
  · exact Nat.mul_pos hG (by omega)
  · cases kind <;> cases i <;> simp only [weight]
    · omega
    · omega
    · exact Nat.mul_pos hG (by omega)
    · rename_i i
      exact Nat.mul_pos hG (by have := hk g i; omega)
  · simp [weight]

theorem weight_le (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q) (i : Parameter n G q) :
    weight n G q k i ≤ 3 * (G * (q + 1)) := by
  have hbase : 1 ≤ G * (q + 1) := Nat.mul_pos hG (by omega)
  rcases i with _ | ⟨g, ⟨kind, i, a⟩ | ⟨i, j, l⟩⟩
  · simp only [weight]; omega
  · cases kind <;> cases i <;> simp only [weight]
    · omega
    · rename_i i
      have hh := Nat.mul_le_mul_left G (hk g i)
      nlinarith
    · omega
    · rename_i i
      have hh := Nat.mul_le_mul_left G (Nat.sub_le (q + 1) (k g i))
      omega
  · simp only [weight]
    have hsub : k g l - k g i - k g j ≤ q := (Nat.sub_le _ _).trans
      ((Nat.sub_le _ _).trans (hk g l))
    have hh := Nat.mul_le_mul_left G hsub
    nlinarith

def represented (n G q : ℕ) (k : Fin G → Fin q → ℕ) : Set ((Fin n → Bool) → Bool) :=
  strictPolynomialSignPatterns (scorePoly (n := n) k)

theorem card_represented_le (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q)
    (hparameters : 1 + 2 * (n + 1) * (G * (q + 1)) + G * q ^ 3 ≤ 2 ^ n) :
    ((represented n G q k).ncard : ℝ) ≤
      (4 * Real.exp 1 * (3 * (G * (q + 1)) : ℕ) * (2 : ℝ) ^ n /
        (1 + 2 * (n + 1) * (G * (q + 1)) + G * q ^ 3 : ℕ)) ^
          (1 + 2 * (n + 1) * (G * (q + 1)) + G * q ^ 3) /
        ∏ i : Parameter n G q, (weight n G q k i : ℝ) := by
  have hh := weightedStrictPolynomialSignPatterns_card_le
    (show 0 < Fintype.card (Parameter n G q) by simp)
    (show Fintype.card (Parameter n G q) ≤ Fintype.card (Fin n → Bool) by
      simpa only [card_parameter, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin] using hparameters)
    (weight n G q k) (weight_pos k hG hk) (weight_le k hG hk)
    (scorePoly (n := n) k) (scorePoly_weightedDegreeLE k hk)
  simpa only [represented, card_parameter, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hh

def clusterScore (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (g : Fin G) (x : Fin n → Bool) : ℝ :=
  eval θ (affinePoly true g none x) / eval θ (affinePoly false g none x) +
    ∑ m : Fin q, ∑ l : Fin q,
      ((-1 : ℝ) ^ ((m : ℕ) + 1) * eval θ (affinePoly true g (some l) x) *
        eval θ (nilpotentPower k g x m l)) / eval θ (affinePoly false g none x) ^ ((m : ℕ) + 2)

def score (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ) (x : Fin n → Bool) : ℝ :=
  θ (Sum.inl ()) + ∑ g : Fin G, clusterScore k θ g x

theorem clear_inverse_term (a b : ℝ) (hb : b ≠ 0) (m q : ℕ) (hm : m < q) :
    a / b ^ (m + 2) * b ^ (q + 1) = a * b ^ (q - m - 1) := by
  have he : q + 1 = (m + 2) + (q - m - 1) := by omega
  rw [he, pow_add]
  field_simp
  simp [pow_add, mul_assoc]

theorem eval_clusterNumerator (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (g : Fin G) (x : Fin n → Bool) (hB : eval θ (affinePoly false g none x) ≠ 0) :
    eval θ (clusterNumerator k g x) = clusterScore k θ g x *
      eval θ (affinePoly false g none x) ^ (q + 1) := by
  simp only [clusterNumerator, map_add, map_mul, map_pow, map_sum, eval_C,
    clusterScore, add_mul, Finset.sum_mul]
  congr 1
  · rw [pow_succ]
    field_simp
  · apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro l _
    exact (clear_inverse_term _ _ hB m q m.isLt).symm

theorem eval_scorePoly (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (x : Fin n → Bool) (hB : ∀ g, eval θ (affinePoly false g none x) ≠ 0) :
    eval θ (scorePoly k x) = score k θ x * eval θ (clearingPoly x) := by
  simp only [scorePoly, map_add, map_sum, map_mul, map_prod, map_pow, eval_X]
  rw [score, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [eval_clusterNumerator k θ g x (hB g), mul_assoc]
  congr 1
  simp only [clearingPoly, map_prod, map_pow]
  exact Finset.mul_prod_erase Finset.univ
    (fun h : Fin G ↦ eval θ (affinePoly false h none x) ^ (q + 1)) (Finset.mem_univ g)

theorem eval_clearingPoly_pos (θ : Parameter n G q → ℝ) (x : Fin n → Bool)
    (hB : ∀ g, 0 < eval θ (affinePoly false g none x)) :
    0 < eval θ (clearingPoly x) := by
  simp only [clearingPoly, map_prod, map_pow]
  exact Finset.prod_pos (fun g _ ↦ pow_pos (hB g) _)

theorem mem_represented_of_score (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hB : ∀ x g, 0 < eval θ (affinePoly false g none x))
    (hf : ∀ x, if f x then 0 < score k θ x else score k θ x < 0) :
    f ∈ represented n G q k := by
  refine ⟨θ, fun x ↦ ?_⟩
  rw [eval_scorePoly k θ x (fun g ↦ (hB x g).ne')]
  have hQ := eval_clearingPoly_pos θ x (hB x)
  have hx := hf x
  cases hfval : f x
  · simp only [hfval, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact mul_neg_of_neg_of_pos hx hQ
  · simp only [hfval, ↓reduceIte] at hx ⊢
    exact mul_pos hx hQ

end HeadComplexity.FilteredAlgebraCapacity
