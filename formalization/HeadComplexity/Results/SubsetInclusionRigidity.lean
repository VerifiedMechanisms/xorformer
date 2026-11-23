import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- All fixed-cardinality subset sums determine the individual coefficients,
provided the cardinality is strictly between zero and that of the universe. -/
theorem fixed_card_subset_sum_zero {ι : Type*}
    (U : Finset ι) (k : ℕ) (a : ι → ℝ)
    (hk : 0 < k) (hkn : k < U.card)
    (h : ∀ S ⊆ U, S.card = k → ∑ i ∈ S, a i = 0) :
    ∀ i ∈ U, a i = 0 := by
  classical
  have heq : ∀ i ∈ U, ∀ j ∈ U, a i = a j := by
    intro i hi j hj
    by_cases hij : i = j
    · simp [hij]
    have hcard : k - 1 ≤ ((U.erase i).erase j).card := by
      have hj' : j ∈ U.erase i := mem_erase.mpr ⟨Ne.symm hij, hj⟩
      rw [card_erase_of_mem hj', card_erase_of_mem hi]
      omega
    obtain ⟨R, hR, hRc⟩ := exists_subset_card_eq hcard
    have hiR : i ∉ R := by
      intro hit
      exact (mem_erase.mp ((mem_erase.mp (hR hit)).2)).1 rfl
    have hjR : j ∉ R := by
      intro hjt
      exact (mem_erase.mp (hR hjt)).1 rfl
    have hRU : R ⊆ U := fun r hr ↦ (mem_erase.mp ((mem_erase.mp (hR hr)).2)).2
    have hiU : insert i R ⊆ U := insert_subset hi hRU
    have hjU : insert j R ⊆ U := insert_subset hj hRU
    have hci : (insert i R).card = k := by rw [card_insert_of_notMem hiR, hRc]; omega
    have hcj : (insert j R).card = k := by rw [card_insert_of_notMem hjR, hRc]; omega
    have hsi := h (insert i R) hiU hci
    have hsj := h (insert j R) hjU hcj
    rw [sum_insert hiR] at hsi
    rw [sum_insert hjR] at hsj
    linarith
  obtain ⟨S, hSU, hSc⟩ := exists_subset_card_eq (Nat.le_of_lt hkn)
  intro i hi
  have hs := h S hSU hSc
  have hc : (∑ j ∈ S, a j) = (k : ℝ) * a i := by
    calc
      (∑ j ∈ S, a j) = ∑ _j ∈ S, a i := by
        apply sum_congr rfl
        intro j hj
        exact heq j (hSU hj) i hi
      _ = (k : ℝ) * a i := by simp [hSc]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  exact (mul_eq_zero.mp (hc.symm.trans hs)).resolve_left hkR

private theorem symmetric_pair_sum_insert {ι : Type*} [DecidableEq ι]
    (w : ι → ι → ℝ) (R : Finset ι) (i : ι) (hi : i ∉ R)
    (hdiag : w i i = 0) (hsym : ∀ a b, w a b = w b a) :
    (∑ a ∈ insert i R, ∑ b ∈ insert i R, w a b) =
      (∑ a ∈ R, ∑ b ∈ R, w a b) + 2 * ∑ r ∈ R, w i r := by
  simp only [sum_insert hi, hdiag, zero_add]
  rw [sum_add_distrib]
  have heq : (∑ r ∈ R, w r i) = ∑ r ∈ R, w i r := by
    apply sum_congr rfl
    intro r hr
    exact hsym r i
  rw [heq]
  ring

/-- The inclusion matrix from unordered pairs to k-element subsets is
injective for 2 ≤ k ≤ |U|-2. The symmetric double sum counts each pair twice.
This is a combinatorial lemma, not a universal head-complexity theorem. -/
theorem fixed_card_pair_sum_zero {ι : Type*}
    (U : Finset ι) (k : ℕ) (w : ι → ι → ℝ)
    (hsym : ∀ i j, w i j = w j i) (hdiag : ∀ i, w i i = 0)
    (hk : 2 ≤ k) (hkn : k + 2 ≤ U.card)
    (h : ∀ S ⊆ U, S.card = k → (∑ i ∈ S, ∑ j ∈ S, w i j) = 0) :
    ∀ i ∈ U, ∀ j ∈ U, w i j = 0 := by
  classical
  have hcol : ∀ r ∈ U, ∀ i ∈ U, ∀ j ∈ U,
      i ≠ r → j ≠ r → w i r = w j r := by
    intro r hr i hi j hj hir hjr
    by_cases hij : i = j
    · simp [hij]
    let V := (U.erase i).erase j
    have hj' : j ∈ U.erase i := mem_erase.mpr ⟨Ne.symm hij, hj⟩
    have hVc : V.card = U.card - 2 := by
      simp only [V, card_erase_of_mem hj', card_erase_of_mem hi]
      omega
    have hk' : 0 < k - 1 := by omega
    have hkn' : k - 1 < V.card := by rw [hVc]; omega
    have hz := fixed_card_subset_sum_zero V (k - 1)
      (fun s ↦ w i s - w j s) hk' hkn' (by
        intro R hRV hRc
        have hiR : i ∉ R := by
          intro hit
          exact (mem_erase.mp ((mem_erase.mp (hRV hit)).2)).1 rfl
        have hjR : j ∉ R := by
          intro hjt
          exact (mem_erase.mp (hRV hjt)).1 rfl
        have hRU : R ⊆ U := fun s hs ↦ (mem_erase.mp ((mem_erase.mp (hRV hs)).2)).2
        have hci : (insert i R).card = k := by rw [card_insert_of_notMem hiR, hRc]; omega
        have hcj : (insert j R).card = k := by rw [card_insert_of_notMem hjR, hRc]; omega
        have hsi := h (insert i R) (insert_subset hi hRU) hci
        have hsj := h (insert j R) (insert_subset hj hRU) hcj
        rw [symmetric_pair_sum_insert w R i hiR (hdiag i) hsym] at hsi
        rw [symmetric_pair_sum_insert w R j hjR (hdiag j) hsym] at hsj
        rw [sum_sub_distrib]
        linarith)
    have hrV : r ∈ V := mem_erase.mpr ⟨Ne.symm hjr, mem_erase.mpr ⟨Ne.symm hir, hr⟩⟩
    exact sub_eq_zero.mp (hz r hrV)
  intro i hi j hj
  by_cases hij : i = j
  · simpa [hij] using hdiag j
  have hall : ∀ r ∈ U, ∀ s ∈ U, r ≠ s → w r s = w i j := by
    intro r hr s hs hrs
    by_cases hsi : s = i
    · subst s
      exact (hcol i hi r hr j hj hrs (Ne.symm hij)).trans (hsym j i)
    · calc
        w r s = w i s := hcol s hs r hr i hi hrs (Ne.symm hsi)
        _ = w s i := hsym i s
        _ = w j i := hcol i hi s hs j hj hsi (Ne.symm hij)
        _ = w i j := hsym j i
  obtain ⟨S, hSU, hSc⟩ := exists_subset_card_eq (show k ≤ U.card by omega)
  have hrow : ∀ r ∈ S, (∑ s ∈ S, w r s) = (k : ℝ) * w i j - w i j := by
    intro r hr
    calc
      (∑ s ∈ S, w r s) = ∑ s ∈ S, (w i j - if s = r then w i j else 0) := by
        apply sum_congr rfl
        intro s hs
        by_cases hsr : s = r
        · subst s
          simp [hdiag]
        · simp only [hsr, ↓reduceIte, sub_zero]
          exact hall r (hSU hr) s (hSU hs) (Ne.symm hsr)
      _ = (k : ℝ) * w i j - w i j := by
        rw [sum_sub_distrib]
        simp [hSc, hr]
  have htotal : (∑ r ∈ S, ∑ s ∈ S, w r s) =
      ((k : ℝ) * (k - 1)) * w i j := by
    calc
      (∑ r ∈ S, ∑ s ∈ S, w r s) = ∑ _r ∈ S, ((k : ℝ) * w i j - w i j) := by
        exact sum_congr rfl hrow
      _ = ((k : ℝ) * (k - 1)) * w i j := by simp [hSc]; ring
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : (k : ℝ) * (k - 1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  exact (mul_eq_zero.mp (htotal.symm.trans (h S hSU hSc))).resolve_left hn

end HeadComplexity
