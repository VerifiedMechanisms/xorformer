import HeadComplexity.Results.PureRoPEReplicationStrict
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic

set_option linter.style.header false

/-!
# Exact finite-population moments and sign-preserving permutation averages

These identities justify the finite-population corrections used when a
multilinear cubic is averaged over replicas with fixed group means.
-/

namespace HeadComplexity.MeanGridSymmetrization

noncomputable section

open Finset
open scoped BigOperators

def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

theorem average_sign {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ)
    (b : Bool) (hf : ∀ a, 0 < f a ↔ b = true) : 0 < average f ↔ b = true := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  cases b
  · have hn : ∑ a, f a ≤ 0 := Finset.sum_nonpos (fun a _ ↦ by
      simpa using le_of_not_gt (by simpa using hf a))
    have ha : average f ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn hc.le
    simp [not_lt_of_ge ha]
  · have hp : 0 < ∑ a, f a :=
      Finset.sum_pos (fun a _ ↦ (hf a).mpr rfl) Finset.univ_nonempty
    simpa [average] using div_pos hp hc

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun a ↦ f a + g a) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    average (fun a ↦ ∑ b, f a b) = ∑ b, average (fun a ↦ f a b) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem average_finset_sum {α β : Type*} [Fintype α]
    (s : Finset β) (f : α → β → ℝ) :
    average (fun a ↦ ∑ b ∈ s, f a b) = ∑ b ∈ s, average (fun a ↦ f a b) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem average_product {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℝ) :
    average (fun σ : ι → α ↦ ∏ i, f i (σ i)) = ∏ i, average (f i) := by
  unfold average
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

theorem average_equiv {α : Type*} [Fintype α] (e : α ≃ α) (f : α → ℝ) :
    average (fun a ↦ f (e a)) = average f := by
  unfold average
  rw [e.sum_comp]

theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α ↦ c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := α)).ne'
  simp only [average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem average_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun a ↦ c * f a) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem tuple_average_invariant {d m : ℕ} (r s : Fin d → Fin m)
    (hr : Function.Injective r) (hs : Function.Injective s)
    (G : (Fin d → Fin m) → ℝ) :
    average (fun σ : Equiv.Perm (Fin m) ↦ G (fun i ↦ σ (r i))) =
      average (fun σ : Equiv.Perm (Fin m) ↦ G (fun i ↦ σ (s i))) := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair r s hr hs
  have he := average_equiv (Equiv.mulRight τ)
    (fun σ : Equiv.Perm (Fin m) ↦ G (fun i ↦ σ (r i)))
  change average (fun σ : Equiv.Perm (Fin m) ↦ G (fun i ↦ (σ * τ) (r i))) =
    average (fun σ : Equiv.Perm (Fin m) ↦ G (fun i ↦ σ (r i))) at he
  simpa only [Equiv.Perm.mul_apply, hτ] using he.symm

theorem average_one_coordinate {m : ℕ} (hm : 0 < m) (z : Fin m → ℝ) (r : Fin m) :
    average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r)) = (∑ i, z i) / m := by
  have hc (i : Fin m) :
      average (fun σ : Equiv.Perm (Fin m) ↦ z (σ i)) =
        average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r)) := by
    have he := tuple_average_invariant (fun _ : Fin 1 ↦ i) (fun _ : Fin 1 ↦ r)
      (fun a b _ ↦ Subsingleton.elim a b) (fun a b _ ↦ Subsingleton.elim a b)
      (fun v ↦ z (v 0))
    exact he
  have he : (m : ℝ) * average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r)) = ∑ i, z i := by
    calc
      _ = ∑ i : Fin m, average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r)) := by simp
      _ = ∑ i : Fin m, average (fun σ : Equiv.Perm (Fin m) ↦ z (σ i)) := by simp only [hc]
      _ = average (fun σ : Equiv.Perm (Fin m) ↦ ∑ i, z (σ i)) := (average_sum _).symm
      _ = average (fun _ : Equiv.Perm (Fin m) ↦ ∑ i, z i) := by
        congr 1
        funext σ
        exact Equiv.sum_comp σ z
      _ = _ := average_const _
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  apply (eq_div_iff hm').mpr
  simpa only [mul_comm] using he

def permuted {n m : ℕ} (x : Fin n × Fin m → Bool)
    (σ : Fin n → Equiv.Perm (Fin m)) (p : Fin n × Fin m) : Bool :=
  x (p.1, σ p.1 p.2)

theorem permutation_average_sign {n m : ℕ} (f : (Fin n × Fin m → Bool) → Bool)
    (P : (Fin n × Fin m → Bool) → ℝ)
    (hP : ∀ x, 0 < P x ↔ f x = true)
    (hf : ∀ x σ, f (permuted x σ) = f x) (x : Fin n × Fin m → Bool) :
    0 < average (fun σ : Fin n → Equiv.Perm (Fin m) ↦ P (permuted x σ)) ↔ f x = true := by
  apply average_sign
  intro σ
  rw [hP, hf]

def distinctTwo {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else z i * z j

def distinctThree {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if i ≠ j ∧ i ≠ k ∧ j ≠ k then z i * z j * z k else 0

theorem distinctTwo_eq {m : ℕ} (z : Fin m → ℝ) (hz : ∀ i, z i ^ 2 = 1) :
    distinctTwo z = (∑ i, z i) ^ 2 - m := by
  have he (i j) : (if i = j then 0 else z i * z j) =
      z i * z j - if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst j
      simp only [ite_true]
      nlinarith [hz i]
    · simp [h]
  simp only [distinctTwo, he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem distinctThree_eq {m : ℕ} (z : Fin m → ℝ) (hz : ∀ i, z i ^ 2 = 1) :
    distinctThree z = (∑ i, z i) ^ 3 - (3 * (m : ℝ) - 2) * (∑ i, z i) := by
  have he (i j k) :
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then z i * z j * z k else 0) =
        z i * z j * z k - (if i = j then z k else 0) -
          (if i = k then z j else 0) - (if j = k then z i else 0) +
            2 * (if i = j ∧ i = k then z i else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp only [ne_eq, not_true_eq_false, and_self, ite_false, ite_true]
        have hh := congrArg (fun a : ℝ ↦ a * z i) (hz i)
        nlinarith
      · simp only [ne_eq, not_true_eq_false, false_and, ite_false, ite_true, hik,
          and_false, mul_zero, add_zero, sub_zero]
        have hh := congrArg (fun a : ℝ ↦ a * z k) (hz i)
        nlinarith
    · by_cases hik : i = k
      · subst k
        simp only [ne_eq, not_true_eq_false, and_false, ite_false, ite_true, hij,
          Ne.symm hij, false_and, mul_zero, add_zero, sub_zero]
        have hh := congrArg (fun a : ℝ ↦ a * z j) (hz i)
        nlinarith
      · by_cases hjk : j = k
        · subst k
          simp only [ne_eq, not_true_eq_false, and_false, ite_false, ite_true, hij,
            mul_zero, add_zero, sub_zero]
          have hh := congrArg (fun a : ℝ ↦ a * z i) (hz j)
          nlinarith
        · simp [hij, hik, hjk]
  have hd (i j : Fin m) :
      (∑ k : Fin m, if i = j then if i = k then z i else 0 else 0) =
        if i = j then z i else 0 := by
    by_cases h : i = j <;> simp [h]
  simp only [distinctThree, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_zero]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [hd]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem average_if {α : Type*} [Fintype α] (p : Prop) [Decidable p] (f g : α → ℝ) :
    average (fun a ↦ if p then f a else g a) = if p then average f else average g := by
  by_cases h : p <;> simp [h]

theorem pair_count {m : ℕ} (c : ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, if i = j then 0 else c) =
      ((m : ℝ) ^ 2 - m) * c := by
  have he (i j : Fin m) : (if i = j then 0 else c) =
      (if i = j then 0 else (1 : ℝ) * 1) * c := by
    by_cases h : i = j <;> simp [h]
  simp_rw [he]
  simp only [← Finset.sum_mul]
  change distinctTwo (fun _ : Fin m ↦ (1 : ℝ)) * c = _
  rw [distinctTwo_eq _ (fun _ ↦ by norm_num)]
  simp

theorem average_two_coordinates {m : ℕ} (hm : 1 < m) (z : Fin m → ℝ)
    (hz : ∀ i, z i ^ 2 = 1) (r s : Fin m) (hrs : r ≠ s) :
    average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r) * z (σ s)) =
      ((∑ i, z i) ^ 2 - m) / ((m : ℝ) * (m - 1)) := by
  let C := average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r) * z (σ s))
  have hc (i j : Fin m) (hij : i ≠ j) :
      average (fun σ : Equiv.Perm (Fin m) ↦ z (σ i) * z (σ j)) = C := by
    have he := tuple_average_invariant ![i, j] ![r, s]
      (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
      (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
      (fun v ↦ z (v 0) * z (v 1))
    exact he
  have ha : average (fun σ : Equiv.Perm (Fin m) ↦ distinctTwo (fun i ↦ z (σ i))) =
      distinctTwo z := by
    have he (σ : Equiv.Perm (Fin m)) : distinctTwo (fun i ↦ z (σ i)) = distinctTwo z := by
      rw [distinctTwo_eq _ (fun i ↦ hz _), distinctTwo_eq z hz, Equiv.sum_comp σ z]
    simp only [he, average_const]
  have hb : average (fun σ : Equiv.Perm (Fin m) ↦ distinctTwo (fun i ↦ z (σ i))) =
      ((m : ℝ) ^ 2 - m) * C := by
    unfold distinctTwo
    simp_rw [average_sum, average_if, average_const]
    calc
      _ = ∑ i : Fin m, ∑ j : Fin m, if i = j then 0 else C := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · simp [h]
        · simp [h, hc i j h]
      _ = _ := pair_count C
  have he := ha.symm.trans hb
  rw [distinctTwo_eq z hz] at he
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  have hd : (m : ℝ) * (m - 1) ≠ 0 := ne_of_gt (by positivity)
  apply (eq_div_iff hd).mpr
  change C * ((m : ℝ) * (m - 1)) = _
  nlinarith [he]

theorem average_two_mean_formula {m : ℕ} (hm : 1 < m) (z : Fin m → ℝ)
    (hz : ∀ i, z i ^ 2 = 1) (r s : Fin m) (hrs : r ≠ s) :
    average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r) * z (σ s)) =
      ((m : ℝ) * ((∑ i, z i) / m) ^ 2 - 1) / (m - 1) := by
  rw [average_two_coordinates hm z hz r s hrs]
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  have h0 : (m : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have h1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp

theorem triple_count {m : ℕ} (c : ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
      if i ≠ j ∧ i ≠ k ∧ j ≠ k then c else 0) =
        ((m : ℝ) ^ 3 - (3 * m - 2) * m) * c := by
  have he (i j k : Fin m) : (if i ≠ j ∧ i ≠ k ∧ j ≠ k then c else 0) =
      (if i ≠ j ∧ i ≠ k ∧ j ≠ k then (1 : ℝ) * 1 * 1 else 0) * c := by
    by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k <;> simp [h]
  simp_rw [he]
  simp only [← Finset.sum_mul]
  change distinctThree (fun _ : Fin m ↦ (1 : ℝ)) * c = _
  rw [distinctThree_eq _ (fun _ ↦ by norm_num)]
  simp

theorem average_three_coordinates {m : ℕ} (hm : 2 < m) (z : Fin m → ℝ)
    (hz : ∀ i, z i ^ 2 = 1) (r s t : Fin m) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r) * z (σ s) * z (σ t)) =
      ((∑ i, z i) ^ 3 - (3 * (m : ℝ) - 2) * (∑ i, z i)) /
        ((m : ℝ) * (m - 1) * (m - 2)) := by
  let C := average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r) * z (σ s) * z (σ t))
  have hc (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      average (fun σ : Equiv.Perm (Fin m) ↦ z (σ i) * z (σ j) * z (σ k)) = C := by
    have he := tuple_average_invariant ![i, j, k] ![r, s, t]
      (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
      (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
      (fun v ↦ z (v 0) * z (v 1) * z (v 2))
    exact he
  have ha : average (fun σ : Equiv.Perm (Fin m) ↦ distinctThree (fun i ↦ z (σ i))) =
      distinctThree z := by
    have he (σ : Equiv.Perm (Fin m)) : distinctThree (fun i ↦ z (σ i)) = distinctThree z := by
      rw [distinctThree_eq _ (fun i ↦ hz _), distinctThree_eq z hz, Equiv.sum_comp σ z]
    simp only [he, average_const]
  have hb : average (fun σ : Equiv.Perm (Fin m) ↦ distinctThree (fun i ↦ z (σ i))) =
      ((m : ℝ) ^ 3 - (3 * m - 2) * m) * C := by
    unfold distinctThree
    simp_rw [average_sum, average_if, average_const]
    calc
      _ = ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
          if i ≠ j ∧ i ≠ k ∧ j ≠ k then C else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
        · simp [h, hc i j k h.1 h.2.1 h.2.2]
        · simp [h]
      _ = _ := triple_count C
  have he := ha.symm.trans hb
  rw [distinctThree_eq z hz] at he
  have hm' : (2 : ℝ) < m := by exact_mod_cast hm
  have hd : (m : ℝ) * (m - 1) * (m - 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)
  apply (eq_div_iff hd).mpr
  change C * ((m : ℝ) * (m - 1) * (m - 2)) = _
  nlinarith [he]

theorem average_three_mean_formula {m : ℕ} (hm : 2 < m) (z : Fin m → ℝ)
    (hz : ∀ i, z i ^ 2 = 1) (r s t : Fin m) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    average (fun σ : Equiv.Perm (Fin m) ↦ z (σ r) * z (σ s) * z (σ t)) =
      ((m : ℝ) ^ 2 * ((∑ i, z i) / m) ^ 3 -
        (3 * m - 2) * ((∑ i, z i) / m)) / ((m - 1) * (m - 2)) := by
  rw [average_three_coordinates hm z hz r s t hrs hrt hst]
  have hm' : (2 : ℝ) < m := by exact_mod_cast hm
  have h0 : (m : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have h1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  field_simp

end

end HeadComplexity.MeanGridSymmetrization
