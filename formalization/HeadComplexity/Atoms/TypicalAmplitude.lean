import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedSectionVars false

/-! Deterministic ingredients of the typical-label amplitude obstruction.
The head cover and the probabilistic chaining event are written proofs.
There is no head-count lower bound in this file. -/

namespace HeadComplexity.TypicalAmplitude

open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def correlation (f v : X → ℝ) : ℝ :=
  (∑ x, f x * v x) / Fintype.card X

lemma card_pos : (0 : ℝ) < Fintype.card X := by
  exact_mod_cast Fintype.card_pos

theorem correlation_add (f u v : X → ℝ) :
    correlation f (fun x ↦ u x + v x) = correlation f u + correlation f v := by
  simp only [correlation, mul_add, Finset.sum_add_distrib, add_div]

theorem correlation_sub (f u v : X → ℝ) :
    correlation f (fun x ↦ u x - v x) = correlation f u - correlation f v := by
  simp only [correlation, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem correlation_smul (f v : X → ℝ) (a : ℝ) :
    correlation f (fun x ↦ a * v x) = a * correlation f v := by
  simp only [correlation]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem abs_correlation_le_uniform (f v : X → ℝ) (a : ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hv : ∀ x, |v x| ≤ a) :
    |correlation f v| ≤ a := by
  have hN := card_pos (X := X)
  unfold correlation
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  calc
    |∑ x, f x * v x| ≤ ∑ x, |f x * v x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : X, a := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      calc
        |f x| * |v x| ≤ 1 * |v x| :=
          mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
        _ ≤ a := by simpa using hv x
    _ = a * Fintype.card X := by simp [mul_comm]

theorem weighted_dyadic_partial_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, ((j : ℝ) + 2) / (2 : ℝ)^(j+1)) =
      3 - ((J : ℝ) + 3) / (2 : ℝ)^J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem weighted_dyadic_partial_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range J, ((j : ℝ) + 2) / (2 : ℝ)^(j+1)) ≤ 3 := by
  rw [weighted_dyadic_partial_sum]
  have : 0 ≤ ((J : ℝ) + 3) / (2 : ℝ)^J := by positivity
  linarith

theorem finite_chain_bound (f : X → ℝ) (g : ℕ → X → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hbase : |correlation f (g 0)| ≤ 2*c)
    (hedge : ∀ j, |correlation f (fun x ↦ g (j+1) x - g j x)| ≤
      3*c*(((j : ℝ)+2)/(2 : ℝ)^(j+1))) (J : ℕ) :
    |correlation f (g J)| ≤ 11*c := by
  have hp (K : ℕ) : |correlation f (g K)| ≤
      2*c+3*c*∑ j ∈ Finset.range K, (((j : ℝ)+2)/(2 : ℝ)^(j+1)) := by
    induction K with
    | zero => simpa using hbase
    | succ K ih =>
      have hid : correlation f (g (K+1)) = correlation f (g K) +
          correlation f (fun x ↦ g (K+1) x-g K x) := by
        rw [correlation_sub]
        ring
      rw [hid]
      calc
        _ ≤ |correlation f (g K)| +
          |correlation f (fun x ↦ g (K+1) x-g K x)| := abs_add_le _ _
        _ ≤ (2*c+3*c*∑ j ∈ Finset.range K,
            (((j : ℝ)+2)/(2 : ℝ)^(j+1))) +
            3*c*(((K : ℝ)+2)/(2 : ℝ)^(K+1)) := add_le_add ih (hedge K)
        _ = _ := by rw [Finset.sum_range_succ]; ring
  have hs := mul_le_mul_of_nonneg_left (weighted_dyadic_partial_sum_le J)
    (show 0 ≤ 3*c by positivity)
  linarith [hp J]

theorem approximation_transfer (f v u : X → ℝ) (ε B : ℝ)
    (hf : ∀ x, |f x| ≤ 1) (happrox : ∀ x, |v x-u x| ≤ ε)
    (hu : |correlation f u| ≤ B) : |correlation f v| ≤ ε+B := by
  have he := abs_correlation_le_uniform f (fun x ↦ v x-u x) ε hf happrox
  have hid : correlation f v = correlation f (fun x ↦ v x-u x) + correlation f u := by
    rw [correlation_sub]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add he hu)

/-- The finite chain estimate passes to the limiting table without a
measurability or compactness assumption. -/
theorem dyadic_chain_bound (f v : X → ℝ) (g : ℕ → X → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ x, |f x| ≤ 1)
    (happrox : ∀ j x, |v x-g j x| ≤ (1/2 : ℝ)^j)
    (hbase : |correlation f (g 0)| ≤ 2*c)
    (hedge : ∀ j, |correlation f (fun x ↦ g (j+1) x - g j x)| ≤
      3*c*(((j : ℝ)+2)/(2 : ℝ)^(j+1))) :
    |correlation f v| ≤ 11*c := by
  by_contra h
  have hgap : 0 < |correlation f v| - 11*c := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hgap (show (1/2 : ℝ) < 1 by norm_num)
  have hb := finite_chain_bound f g c hc hbase hedge J
  have ht := approximation_transfer f v (g J) ((1/2 : ℝ)^J) (11*c) hf
    (happrox J) hb
  linarith

theorem margin_le_correlation (f S : X → ℝ) (μ : ℝ)
    (hm : ∀ x, μ ≤ f x*S x) : μ ≤ correlation f S := by
  have hN := card_pos (X := X)
  apply (le_div_iff₀ hN).mpr
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hm x)
  simpa [correlation, mul_comm] using hs

/-- A single uniform atom correlation event controls every finite combination.
The assumptions here are deterministic and include the bias correlation. -/
theorem relative_margin_bound {H : Type*} [Fintype H]
    (f : X → ℝ) (φ : H → X → ℝ) (c R γ : ℝ) (M : H → ℝ)
    (hbias : |correlation f (fun _ ↦ c)| ≤ R*|c|)
    (hhead : ∀ h, |correlation f (φ h)| ≤ R*M h)
    (hpos : 0 < |c|+∑ h, M h)
    (hm : ∀ x, γ*(|c|+∑ h, M h) ≤ f x*(c+∑ h, φ h x)) : γ ≤ R := by
  have he : correlation f (fun x ↦ c+∑ h, φ h x) =
      correlation f (fun _ ↦ c)+∑ h, correlation f (φ h) := by
    simp only [correlation, mul_add, Finset.mul_sum, Finset.sum_add_distrib,
      add_div, ← Finset.sum_div]
    rw [Finset.sum_comm]
  have hm' := margin_le_correlation f (fun x ↦ c+∑ h, φ h x)
    (γ*(|c|+∑ h, M h)) hm
  have hb : |correlation f (fun x ↦ c+∑ h, φ h x)| ≤ R*(|c|+∑ h, M h) := by
    rw [he]
    calc
      _ ≤ |correlation f (fun _ ↦ c)|+|∑ h, correlation f (φ h)| := abs_add_le _ _
      _ ≤ |correlation f (fun _ ↦ c)|+∑ h, |correlation f (φ h)| :=
        add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ R*|c|+∑ h, R*M h := add_le_add hbias (Finset.sum_le_sum fun h _ ↦ hhead h)
      _ = _ := by rw [mul_add, Finset.mul_sum]
  have hprod := hm'.trans ((le_abs_self _).trans hb)
  nlinarith

end HeadComplexity.TypicalAmplitude
