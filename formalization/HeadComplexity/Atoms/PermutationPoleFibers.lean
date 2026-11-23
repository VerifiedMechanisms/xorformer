import HeadComplexity.Atoms.PartialFraction
import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Data.Fintype.Perm

set_option linter.style.header false

/-!
# Finite-sample separation of reciprocal pole sets

Two sums of `H` simple reciprocals with distinct poles cannot agree at `2H`
distinct regular points unless their pole sets agree.  This is an ingredient
of a restricted-family interpolation ambiguity construction, not a statement
about connected components of the full head-parameter fiber.
-/

namespace HeadComplexity.PermutationPoleFibers

open Polynomial Finset
open scoped BigOperators

noncomputable def poleProduct {H : ℕ} (p : Fin H → ℝ) : ℝ[X] :=
  ∏ h, (X + C (p h))

noncomputable def poleCofactor {H : ℕ} (p : Fin H → ℝ) (h : Fin H) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase h, (X + C (p j))

noncomputable def reciprocalSum {H : ℕ} (p : Fin H → ℝ) (t : ℝ) : ℝ :=
  ∑ h, 1 / (t + p h)

theorem poleProduct_eval {H : ℕ} (p : Fin H → ℝ) (t : ℝ) :
    (poleProduct p).eval t = ∏ h, (t + p h) := by
  simp [poleProduct, eval_prod]

theorem poleCofactor_eval {H : ℕ} (p : Fin H → ℝ) (h : Fin H) (t : ℝ) :
    (poleCofactor p h).eval t = ∏ j ∈ Finset.univ.erase h, (t + p j) := by
  simp [poleCofactor, eval_prod]

theorem poleProduct_degree {H : ℕ} (p : Fin H → ℝ) :
    (poleProduct p).natDegree = H := by
  rw [poleProduct, natDegree_prod _ _ (fun i _ ↦ (monic_X_add_C (p i)).ne_zero)]
  simp

theorem poleCofactor_degree {H : ℕ} (p : Fin H → ℝ) (h : Fin H) :
    (poleCofactor p h).natDegree = H - 1 := by
  rw [poleCofactor, natDegree_prod _ _ (fun i _ ↦ (monic_X_add_C (p i)).ne_zero)]
  simp

theorem reciprocalSum_mul_product {H : ℕ} (p : Fin H → ℝ) (t : ℝ)
    (hregular : ∀ h, t + p h ≠ 0) :
    reciprocalSum p t * (poleProduct p).eval t =
      ∑ h, (poleCofactor p h).eval t := by
  rw [reciprocalSum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun h _ ↦ ?_)
  rw [poleProduct_eval, poleCofactor_eval,
    ← Finset.mul_prod_erase Finset.univ (fun j ↦ t + p j) (Finset.mem_univ h)]
  field_simp [hregular h]

/-- The rational numerator of a difference of reciprocal sums. -/
noncomputable def comparisonPolynomial {H : ℕ} (p q : Fin H → ℝ) : ℝ[X] :=
  (∑ h, poleCofactor p h) * poleProduct q -
    (∑ h, poleCofactor q h) * poleProduct p

theorem comparisonPolynomial_degree {H : ℕ} (hH : 0 < H) (p q : Fin H → ℝ) :
    (comparisonPolynomial p q).natDegree < 2 * H := by
  have hsum : ∀ r : Fin H → ℝ, (∑ h, poleCofactor r h).natDegree ≤ H - 1 := by
    intro r
    exact natDegree_sum_le_of_forall_le _ _ (fun h _ ↦ (poleCofactor_degree r h).le)
  have hp := natDegree_mul_le (p := ∑ h, poleCofactor p h) (q := poleProduct q)
  have hq := natDegree_mul_le (p := ∑ h, poleCofactor q h) (q := poleProduct p)
  rw [poleProduct_degree] at hp hq
  have hdeg := natDegree_sub_le
    ((∑ h, poleCofactor p h) * poleProduct q)
    ((∑ h, poleCofactor q h) * poleProduct p)
  change (comparisonPolynomial p q).natDegree ≤ _ at hdeg
  have hp' := hsum p
  have hq' := hsum q
  omega

theorem comparisonPolynomial_eval_zero {H : ℕ} (p q : Fin H → ℝ) (t : ℝ)
    (hp : ∀ h, t + p h ≠ 0) (hq : ∀ h, t + q h ≠ 0)
    (heq : reciprocalSum p t = reciprocalSum q t) :
    (comparisonPolynomial p q).eval t = 0 := by
  simp only [comparisonPolynomial, eval_sub, eval_mul, eval_finsetSum]
  rw [← reciprocalSum_mul_product p t hp, ← reciprocalSum_mul_product q t hq, heq]
  ring

theorem comparisonPolynomial_zero {H : ℕ} (hH : 0 < H) (p q : Fin H → ℝ)
    (samples : Fin (2 * H) → ℝ) (hinj : Function.Injective samples)
    (hp : ∀ s h, samples s + p h ≠ 0) (hq : ∀ s h, samples s + q h ≠ 0)
    (heq : ∀ s, reciprocalSum p (samples s) = reciprocalSum q (samples s)) :
    comparisonPolynomial p q = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
  · intro s
    exact comparisonPolynomial_eval_zero p q (samples s) (hp s) (hq s) (heq s)
  · simpa using comparisonPolynomial_degree hH p q

theorem comparisonPolynomial_at_pole {H : ℕ} (p q : Fin H → ℝ)
    (i : Fin H) :
    (comparisonPolynomial p q).eval (-p i) =
      (∏ j ∈ Finset.univ.erase i, (p j - p i)) *
        ∏ j, (q j - p i) := by
  classical
  have hprod : (poleProduct p).eval (-p i) = 0 := by
    rw [poleProduct_eval]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  have hco : ∀ h : Fin H, h ≠ i → (poleCofactor p h).eval (-p i) = 0 := by
    intro h hhi
    rw [poleCofactor_eval]
    exact Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨Ne.symm hhi, Finset.mem_univ i⟩) (by ring)
  simp only [comparisonPolynomial, eval_sub, eval_mul, hprod, mul_zero, sub_zero,
    eval_finsetSum]
  rw [Finset.sum_eq_single i (fun h _ hhi ↦ hco h hhi)
    (fun h ↦ absurd (Finset.mem_univ i) h), poleCofactor_eval, poleProduct_eval]
  congr 1 <;> apply Finset.prod_congr rfl <;> intros <;> ring

/-- Agreement at `2H` regular samples forces every pole of the first sum
to occur in the second sum. Distinctness of the first poles is essential. -/
theorem poles_included_of_samples {H : ℕ} (hH : 0 < H) (p q : Fin H → ℝ)
    (hpinj : Function.Injective p)
    (samples : Fin (2 * H) → ℝ) (hinj : Function.Injective samples)
    (hp : ∀ s h, samples s + p h ≠ 0) (hq : ∀ s h, samples s + q h ≠ 0)
    (heq : ∀ s, reciprocalSum p (samples s) = reciprocalSum q (samples s)) :
    ∀ i, ∃ j, p i = q j := by
  classical
  have hzero := comparisonPolynomial_zero hH p q samples hinj hp hq heq
  intro i
  have hval := comparisonPolynomial_at_pole p q i
  rw [hzero, eval_zero] at hval
  have hleft : (∏ j ∈ Finset.univ.erase i, (p j - p i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun e ↦ (Finset.mem_erase.mp hj).1 (hpinj e))
  have hright : (∏ j, (q j - p i)) = 0 := (mul_eq_zero.mp hval.symm).resolve_left hleft
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hright
  exact ⟨j, (sub_eq_zero.mp hj).symm⟩

/-- A pole present in only one sum is detected at one of any `2H` distinct
regular samples. -/
theorem exists_distinguishing_sample {H : ℕ} (hH : 0 < H) (p q : Fin H → ℝ)
    (hpinj : Function.Injective p)
    (samples : Fin (2 * H) → ℝ) (hinj : Function.Injective samples)
    (hp : ∀ s h, samples s + p h ≠ 0) (hq : ∀ s h, samples s + q h ≠ 0)
    (hdiff : ∃ i, ∀ j, p i ≠ q j) :
    ∃ s, reciprocalSum p (samples s) ≠ reciprocalSum q (samples s) := by
  by_contra! h
  obtain ⟨i, hi⟩ := hdiff
  obtain ⟨j, hj⟩ := poles_included_of_samples hH p q hpinj samples hinj hp hq h i
  exact hi j hj

/-- Two base-`H` digits, used to distinguish a row from a column matching. -/
def pairCode {H : ℕ} (i j : Fin H) : ℕ := (i : ℕ) + H * (j : ℕ)

theorem pairCode_injective {H : ℕ} {i j i' j' : Fin H}
    (heq : pairCode i j = pairCode i' j') : i = i' ∧ j = j' := by
  have hH : 0 < H := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hi := congrArg (fun a ↦ a % H) heq
  simp [pairCode, Nat.add_mod, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt i'.isLt] at hi
  have him : i = i' := Fin.ext hi
  subst i'
  have hj : H * (j : ℕ) = H * (j' : ℕ) := by
    simpa [pairCode] using heq
  exact ⟨rfl, Fin.ext (Nat.eq_of_mul_eq_mul_left hH hj)⟩

noncomputable def codedPole {H : ℕ} (π : Equiv.Perm (Fin H)) (h : Fin H) : ℝ :=
  ((H + 2 + pairCode h (π h) : ℕ) : ℝ)

theorem codedPole_pos {H : ℕ} (π : Equiv.Perm (Fin H)) (h : Fin H) :
    0 < codedPole π h := by
  unfold codedPole
  positivity

theorem codedPole_eq_iff {H : ℕ} (π σ : Equiv.Perm (Fin H)) (h j : Fin H) :
    codedPole π h = codedPole σ j ↔ h = j ∧ π h = σ j := by
  constructor
  · intro heq
    unfold codedPole at heq
    have hnat : H + 2 + pairCode h (π h) = H + 2 + pairCode j (σ j) := by
      exact_mod_cast heq
    exact pairCode_injective (Nat.add_left_cancel hnat)
  · rintro ⟨rfl, heq⟩
    simp only [codedPole, heq]

theorem codedPole_injective {H : ℕ} (π : Equiv.Perm (Fin H)) :
    Function.Injective (codedPole π) := by
  intro h j heq
  exact ((codedPole_eq_iff π π h j).mp heq).1

/-- Distinct matchings yield different tables at the first `2H` integer
addresses. These are valid positive-denominator samples. -/
theorem permutation_detected_at_integer_sample {H : ℕ} (hH : 0 < H)
    (π σ : Equiv.Perm (Fin H)) (hne : π ≠ σ) :
    ∃ s : Fin (2 * H),
      reciprocalSum (codedPole π) s.val ≠ reciprocalSum (codedPole σ) s.val := by
  have hdiff : ∃ i, π i ≠ σ i := by
    by_contra! h
    exact hne (Equiv.ext h)
  apply exists_distinguishing_sample hH (codedPole π) (codedPole σ)
    (codedPole_injective π) (fun s : Fin (2 * H) ↦ (s.val : ℝ))
  · intro a b heq
    exact Fin.ext (Nat.cast_injective heq)
  · intro s h
    exact ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (codedPole_pos π h))
  · intro s h
    exact ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (codedPole_pos σ h))
  · obtain ⟨i, hi⟩ := hdiff
    refine ⟨i, fun j heq ↦ ?_⟩
    obtain ⟨rfl, hsame⟩ := (codedPole_eq_iff π σ i j).mp heq
    exact hi hsame

/-- Permuting one coefficient column does not change its one-selector slice. -/
theorem singleton_slice_invariant {H : ℕ} (π : Equiv.Perm (Fin H)) (t : ℝ) :
    (∑ h : Fin H, 1 / (1 + t + (H : ℝ) * ((π h).val + 1))) =
      ∑ h : Fin H, 1 / (1 + t + (H : ℝ) * (h.val + 1)) := by
  exact Equiv.sum_comp π (fun h : Fin H ↦ 1 / (1 + t + (H : ℝ) * (h.val + 1)))

noncomputable def selectedScore {H k : ℕ} (perms : Fin k → Equiv.Perm (Fin H))
    (base : Bool) (xs : Fin k → Bool) (t : ℝ) : ℝ :=
  ∑ h : Fin H, 1 / (1 + t + (h.val + 1) * boolToReal base +
    ∑ i, (H : ℝ) * ((perms i h).val + 1) * boolToReal (xs i))

theorem zero_slice {H k : ℕ} (perms : Fin k → Equiv.Perm (Fin H)) (t : ℝ) :
    selectedScore perms false (fun _ ↦ false) t = (H : ℝ) / (1 + t) := by
  simp [selectedScore, boolToReal, div_eq_mul_inv]

theorem base_slice {H k : ℕ} (perms : Fin k → Equiv.Perm (Fin H)) (t : ℝ) :
    selectedScore perms true (fun _ ↦ false) t =
      ∑ h : Fin H, 1 / (1 + t + (h.val + 1)) := by
  simp [selectedScore, boolToReal]

theorem other_singleton_slice {H k : ℕ} (perms : Fin k → Equiv.Perm (Fin H))
    (i : Fin k) (t : ℝ) :
    selectedScore perms false (fun j ↦ decide (j = i)) t =
      ∑ h : Fin H, 1 / (1 + t + (H : ℝ) * (h.val + 1)) := by
  classical
  have hone : ∀ h : Fin H,
      (∑ j, (H : ℝ) * ((perms j h).val + 1) * boolToReal (decide (j = i))) =
        (H : ℝ) * ((perms i h).val + 1) := by
    intro h
    rw [Finset.sum_eq_single i]
    · simp [boolToReal]
    · intro j _ hji
      simp [hji, boolToReal]
    · simp
  simp only [selectedScore, show boolToReal false = 0 by rfl, mul_zero, add_zero, hone]
  exact singleton_slice_invariant (perms i) t

theorem paired_slice {H k : ℕ} (perms : Fin k → Equiv.Perm (Fin H))
    (i : Fin k) (t : ℝ) :
    selectedScore perms true (fun j ↦ decide (j = i)) t =
      reciprocalSum (codedPole (perms i)) t := by
  classical
  unfold selectedScore reciprocalSum
  apply Finset.sum_congr rfl
  intro h _
  have hone :
      (∑ j, (H : ℝ) * ((perms j h).val + 1) * boolToReal (decide (j = i))) =
        (H : ℝ) * ((perms i h).val + 1) := by
    rw [Finset.sum_eq_single i]
    · simp [boolToReal]
    · intro j _ hji
      simp [hji, boolToReal]
    · simp
  rw [hone]
  congr 1
  simp only [codedPole, pairCode, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    show boolToReal true = 1 by rfl, mul_one]
  ring

noncomputable def sampledTable {H k : ℕ} (perms : Fin k → Equiv.Perm (Fin H)) :
    Bool × (Fin k → Bool) × Fin (2 * H) → ℝ :=
  fun a ↦ selectedScore perms a.1 a.2.1 a.2.2.val

/-- The matching choices give genuinely different complete sampled tables,
although their zero- and one-selector slices all agree. -/
theorem sampledTable_injective {H k : ℕ} (hH : 0 < H) :
    Function.Injective (sampledTable (H := H) (k := k)) := by
  intro perms other heq
  funext i
  by_contra hne
  obtain ⟨s, hs⟩ := permutation_detected_at_integer_sample hH (perms i) (other i) hne
  have hvalue := congrFun heq (true, (fun j ↦ decide (j = i)), s)
  simp only [sampledTable, paired_slice] at hvalue
  exact hs hvalue

/-- Number of matching choices. The preceding injection makes this also the
number of distinct sampled tables in this constructed family. -/
theorem matching_family_card (H k : ℕ) :
    Fintype.card (Fin k → Equiv.Perm (Fin H)) = (Nat.factorial H) ^ k := by
  simp [Fintype.card_perm]

end HeadComplexity.PermutationPoleFibers

#print axioms HeadComplexity.PermutationPoleFibers.exists_distinguishing_sample
#print axioms HeadComplexity.PermutationPoleFibers.pairCode_injective
#print axioms HeadComplexity.PermutationPoleFibers.permutation_detected_at_integer_sample
#print axioms HeadComplexity.PermutationPoleFibers.singleton_slice_invariant
#print axioms HeadComplexity.PermutationPoleFibers.sampledTable_injective
#print axioms HeadComplexity.PermutationPoleFibers.matching_family_card
