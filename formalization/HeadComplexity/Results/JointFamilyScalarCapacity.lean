import HeadComplexity.Results.JointFamilyActiveDirections
import HeadComplexity.Results.ScalarDecoderRootBound

set_option linter.style.header false

/-!
# Scalar decoding and affine selectors cannot increase the word length

For a scalar decoder with `a` output bits and `q = 2^a` distinct strict
sign words, the total number of active poles across the bit decoders is
at least `q - 1`. Each bit's affine realization of the corresponding
finite-plane selectors requires `K_b * (q - 1) <= n` coordinates.
Summing gives `(q - 1)^2 <= a * n`. In particular `a <= log_2(4n)`.

The restriction is specific to exact affine line selectors. It does not
bound nonlinear selector constructions or general original-model scores.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Clear only the active scalar Cauchy denominators. -/
noncomputable def jointFamilyCauchyPolynomial (S : Finset I)
    (pole η : I → ℝ) (c : ℝ) : Polynomial ℝ :=
  Polynomial.C c * ∏ i ∈ S, (Polynomial.C (pole i) - Polynomial.X) +
    ∑ i ∈ S, Polynomial.C (η i) *
      ∏ j ∈ S.erase i, (Polynomial.C (pole j) - Polynomial.X)

private theorem cauchy_product_degree (S : Finset I) (pole : I → ℝ) :
    (∏ i ∈ S, (Polynomial.C (pole i) - Polynomial.X : Polynomial ℝ)).natDegree ≤
      S.card := by
  refine (Polynomial.natDegree_prod_le S _).trans ?_
  calc
    (∑ i ∈ S, (Polynomial.C (pole i) - Polynomial.X : Polynomial ℝ).natDegree) ≤
        ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = S.card := by simp

/-- Clearing `K` active scalar poles gives numerator degree at most `K`. -/
theorem jointFamilyCauchyPolynomial_degree (S : Finset I)
    (pole η : I → ℝ) (c : ℝ) :
    (jointFamilyCauchyPolynomial S pole η c).natDegree ≤ S.card := by
  unfold jointFamilyCauchyPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (cauchy_product_degree S pole)
  · apply (Polynomial.natDegree_sum_le _ _).trans
    apply Finset.sup_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((cauchy_product_degree (S.erase i) pole).trans Finset.card_erase_le)

/-- The cleared polynomial has the same strict signs as the scalar score
whenever all active denominators are positive. -/
theorem jointFamilyCauchyPolynomial_eval (S : Finset I)
    (pole η : I → ℝ) (c t : ℝ)
    (hden : ∀ i ∈ S, pole i - t ≠ 0) :
    (jointFamilyCauchyPolynomial S pole η c).eval t =
      (∏ i ∈ S, (pole i - t)) * (c + ∑ i ∈ S, η i / (pole i - t)) := by
  classical
  simp only [jointFamilyCauchyPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finsetSum,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_prod_erase S (fun j ↦ pole j - t) hi]
    field_simp [hden i hi]

/-- The root budget and the active-direction feature budget combine
without assuming any particular pole is active in every output bit. -/
theorem jointFamily_root_feature_budget {a m n : ℕ}
    (p : Fin a → Polynomial ℝ)
    (hp : ∀ b, p b ≠ 0)
    (token : Fin (m + 1) → ℝ) (htoken : StrictMono token)
    (hchange : ∀ i : Fin m, ∃ b : Fin a,
      (p b).eval (token i.castSucc) * (p b).eval (token i.succ) < 0)
    (hfeature : ∀ b, (p b).natDegree * m ≤ n) :
    m * m ≤ a * n := by
  have hroot := polynomial_sign_sequence_degree_bound p hp token htoken hchange
  calc
    m * m ≤ (∑ b, (p b).natDegree) * m := Nat.mul_le_mul_right m hroot
    _ = ∑ b, (p b).natDegree * m := Finset.sum_mul _ _ _
    _ ≤ ∑ _b : Fin a, n := Finset.sum_le_sum (fun b _ ↦ hfeature b)
    _ = a * n := by simp

/-- Distinct strict sign words suffice for the varying-degree root budget. -/
theorem jointFamily_root_feature_budget_of_distinct_words {a m n : ℕ}
    (p : Fin a → Polynomial ℝ)
    (token : Fin (m + 1) → ℝ) (htoken : StrictMono token)
    (hnonzero : ∀ i b, (p b).eval (token i) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m + 1) ↦
      fun b : Fin a ↦ (0 < (p b).eval (token i))))
    (hfeature : ∀ b, (p b).natDegree * m ≤ n) :
    m * m ≤ a * n := by
  classical
  have hp (b : Fin a) : p b ≠ 0 := by
    intro he
    simpa [he] using hnonzero 0 b
  apply jointFamily_root_feature_budget p hp token htoken ?_ hfeature
  intro i
  by_contra hc
  push Not at hc
  have he : (fun b : Fin a ↦ 0 < (p b).eval (token i.castSucc)) =
      (fun b : Fin a ↦ 0 < (p b).eval (token i.succ)) := by
    funext b
    apply propext
    have hprod := hc b
    have ha := hnonzero i.castSucc b
    have hb := hnonzero i.succ b
    constructor
    · intro h
      by_contra h'
      have hn : (p b).eval (token i.succ) < 0 := lt_of_le_of_ne (le_of_not_gt h') hb
      exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg h hn)
    · intro h
      by_contra h'
      have hn : (p b).eval (token i.castSucc) < 0 := lt_of_le_of_ne (le_of_not_gt h') ha
      exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hn h)
  have hi := hwords he
  have : i.castSucc < i.succ := by simp
  exact (ne_of_lt this) hi

/-- A scalar Cauchy codebook together with exact affine weighted line
selectors obeys the quadratic capacity obstruction. The point addresses
may depend on the decoded bit. Poles with zero weight are not charged. -/
theorem jointFamily_cauchy_affine_capacity
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a m n : ℕ}
    (hcard : Fintype.card F = m + 1)
    (pole : F → ℝ) (η : Fin a → F → ℝ) (c : Fin a → ℝ)
    (token : Fin (m + 1) → ℝ) (htoken : StrictMono token)
    (hden : ∀ i z, 0 < pole z - token i)
    (hnonzero : ∀ i b, c b + (∑ z : F, η b z / (pole z - token i)) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m + 1) ↦
      fun b : Fin a ↦ (0 < c b + ∑ z : F, η b z / (pole z - token i))))
    (address : Fin a → (F × F) → Fin n → ℝ)
    (bias : Fin a → F → F → ℝ) (weight : Fin a → F → F → Fin n → ℝ)
    (hselector : ∀ b, ∀ p : F × F, ∀ u v,
      (if p.2 = u * p.1 + v then η b u else 0) =
        bias b u v + ∑ k, weight b u v k * address b p k) :
    m * m ≤ a * n := by
  classical
  let S : Fin a → Finset F := fun b ↦ Finset.univ.filter (fun z ↦ η b z ≠ 0)
  let P : Fin a → Polynomial ℝ := fun b ↦
    jointFamilyCauchyPolynomial (S b) pole (η b) (c b)
  have hsum (b : Fin a) (t : ℝ) :
      (∑ z ∈ S b, η b z / (pole z - t)) = ∑ z : F, η b z / (pole z - t) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    have he : η b z = 0 := by simpa [S] using hz
    simp [he]
  have hprod (b : Fin a) (i : Fin (m + 1)) :
      0 < ∏ z ∈ S b, (pole z - token i) :=
    Finset.prod_pos (fun z _ ↦ hden i z)
  have heval (b : Fin a) (i : Fin (m + 1)) :
      (P b).eval (token i) = (∏ z ∈ S b, (pole z - token i)) *
        (c b + ∑ z : F, η b z / (pole z - token i)) := by
    change (jointFamilyCauchyPolynomial (S b) pole (η b) (c b)).eval (token i) = _
    rw [jointFamilyCauchyPolynomial_eval (S b) pole (η b) (c b) (token i)
      (fun z _ ↦ (hden i z).ne'), hsum]
  have hPnonzero (i : Fin (m + 1)) (b : Fin a) : (P b).eval (token i) ≠ 0 := by
    rw [heval]
    exact mul_ne_zero (hprod b i).ne' (hnonzero i b)
  have hPwords : Function.Injective (fun i : Fin (m + 1) ↦
      fun b : Fin a ↦ (0 < (P b).eval (token i))) := by
    intro i j he
    apply hwords
    funext b
    have hb := congrFun he b
    simpa only [heval, mul_pos_iff_of_pos_left (hprod b i),
      mul_pos_iff_of_pos_left (hprod b j)] using hb
  have hgeometry (b : Fin a) : (S b).card * m ≤ n := by
    by_cases hs : (S b).Nonempty
    · letI : Nonempty (↥(S b)) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
      have hη (z : ↥(S b)) : η b z.val ≠ 0 := (Finset.mem_filter.mp z.property).2
      have h := jointFamily_active_weighted_affine_selectors_dimension
        (fun z : ↥(S b) ↦ z.val) Subtype.val_injective
        (fun z : ↥(S b) ↦ η b z.val) hη (address b)
        (fun z v ↦ bias b z.val v) (fun z v k ↦ weight b z.val v k)
        (fun p z v ↦ hselector b p z.val v)
      simpa [hcard] using h
    · have he : S b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [he]
  apply jointFamily_root_feature_budget_of_distinct_words P token htoken
    hPnonzero hPwords
  intro b
  exact (Nat.mul_le_mul_right m (jointFamilyCauchyPolynomial_degree
    (S b) pole (η b) (c b))).trans (hgeometry b)

/-- The numerical consequence rules out superlogarithmic word capacity
for this class of scalar decoders with affine finite-plane selectors. -/
theorem jointFamily_word_length_le_log {a n : ℕ} (ha : 1 ≤ a)
    (hbudget : (2 ^ a - 1) * (2 ^ a - 1) ≤ a * n) :
    2 ^ a ≤ 4 * n ∧ a ≤ Nat.log 2 (4 * n) := by
  have hq : 2 ≤ 2 ^ a := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) ha
  have hhalf : 2 ^ a ≤ 2 * (2 ^ a - 1) := by omega
  have hsq := Nat.mul_self_le_mul_self hhalf
  have haq : a ≤ 2 ^ a := a.lt_two_pow_self.le
  have han := Nat.mul_le_mul_right n haq
  have hbound : 2 ^ a ≤ 4 * n := by nlinarith
  exact ⟨hbound, Nat.le_log_of_pow_le (by norm_num) hbound⟩

/-- Complete capacity obstruction for exact scalar Cauchy decoding with
affine finite-plane selectors. Enlarging the field cannot give a word
length greater than `log_2(4n)` in this construction class. -/
theorem jointFamily_cauchy_affine_word_length_le_log
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a m n : ℕ}
    (ha : 1 ≤ a) (hcard : Fintype.card F = m + 1) (hwordsCard : m + 1 = 2 ^ a)
    (pole : F → ℝ) (η : Fin a → F → ℝ) (c : Fin a → ℝ)
    (token : Fin (m + 1) → ℝ) (htoken : StrictMono token)
    (hden : ∀ i z, 0 < pole z - token i)
    (hnonzero : ∀ i b, c b + (∑ z : F, η b z / (pole z - token i)) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m + 1) ↦
      fun b : Fin a ↦ (0 < c b + ∑ z : F, η b z / (pole z - token i))))
    (address : Fin a → (F × F) → Fin n → ℝ)
    (bias : Fin a → F → F → ℝ) (weight : Fin a → F → F → Fin n → ℝ)
    (hselector : ∀ b, ∀ p : F × F, ∀ u v,
      (if p.2 = u * p.1 + v then η b u else 0) =
        bias b u v + ∑ k, weight b u v k * address b p k) :
    2 ^ a ≤ 4 * n ∧ a ≤ Nat.log 2 (4 * n) := by
  have h := jointFamily_cauchy_affine_capacity hcard pole η c token htoken
    hden hnonzero hwords address bias weight hselector
  apply jointFamily_word_length_le_log ha
  have hm : 2 ^ a - 1 = m := by omega
  simpa [hm] using h

end HeadComplexity.AxisZeroGluing
