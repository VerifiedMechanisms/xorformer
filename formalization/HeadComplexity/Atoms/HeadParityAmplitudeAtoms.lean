import HeadComplexity.Atoms.HeadParityAmplitude
import HeadComplexity.Atoms.FracAtomSymmetry
import HeadComplexity.Atoms.AtomicMargin

set_option linter.style.header false
noncomputable section

namespace HeadComplexity.HeadParityAmplitude
open scoped BigOperators
variable {n : ℕ}

def subsetBits (t : Finset (Fin n)) : Fin n → Bool := fun i ↦ decide (i ∈ t)

def subsetAlternating (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ t, (-1 : ℝ)^t.card*f t

lemma sum_mem (f : Fin n → ℝ) (t : Finset (Fin n)) :
    (∑ i, if i ∈ t then f i else 0) = ∑ i ∈ t, f i := by
  rw [← Finset.sum_filter]
  simp

lemma atom_subset_affine (phi : FracAtom n) (t : Finset (Fin n)) :
    phi.eval (subsetBits t) =
      ((phi.η+∑ i, phi.ρ i*phi.m i)+
        ∑ i ∈ t, phi.ρ i*(phi.α*(phi.m i+phi.δ)-phi.m i)) /
      ((phi.γ+∑ i, phi.ρ i)+∑ i ∈ t, phi.ρ i*(phi.α-1)) := by
  have hd (i : Fin n) : phi.wt (subsetBits t) i =
      phi.ρ i+(if i ∈ t then phi.ρ i*(phi.α-1) else 0) := by
    by_cases hi : i ∈ t <;> simp [FracAtom.wt, subsetBits, hi] <;> ring
  have hn (i : Fin n) : phi.wt (subsetBits t) i *
      (phi.m i+(if subsetBits t i then phi.δ else 0)) =
      phi.ρ i*phi.m i+(if i ∈ t then
        phi.ρ i*(phi.α*(phi.m i+phi.δ)-phi.m i) else 0) := by
    by_cases hi : i ∈ t <;> simp [FracAtom.wt, subsetBits, hi] <;> ring
  unfold FracAtom.eval
  simp_rw [hn, hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_mem, sum_mem]
  ring

lemma atom_positive_unit_bound (hn : 0 < n) (phi : FracAtom n)
    (ha : 1 ≤ phi.α) (hb : ∀ x, |phi.eval x| ≤ 1) :
    |subsetAlternating (fun t ↦ phi.eval (subsetBits t))| ≤ 2 := by
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hc : 0 < phi.γ+∑ i, phi.ρ i :=
    add_pos_of_pos_of_nonneg phi.hγ (Finset.sum_nonneg fun i _ ↦ (phi.hρ i).le)
  have hw (i : Fin n) : 0 ≤ phi.ρ i*(phi.α-1) :=
    mul_nonneg (phi.hρ i).le (sub_nonneg.mpr ha)
  have h := positive_affine_ratio_bound
    (fun i ↦ phi.ρ i*(phi.α-1))
    (fun i ↦ phi.ρ i*(phi.α*(phi.m i+phi.δ)-phi.m i))
    (phi.γ+∑ i, phi.ρ i) (phi.η+∑ i, phi.ρ i*phi.m i)
    Finset.univ hs hc hw (fun t _ ↦ by rw [← atom_subset_affine]; exact hb _)
  simpa only [subsetAlternating, atom_subset_affine, Finset.powerset_univ] using h

lemma parity_compl (t : Finset (Fin n)) :
    (-1 : ℝ)^(tᶜ).card = (-1 : ℝ)^n*(-1 : ℝ)^t.card := by
  have hcard : t.card+(tᶜ).card = n := by
    simpa using Finset.card_add_card_compl t
  have he : (-1 : ℝ)^n = (-1 : ℝ)^t.card*(-1 : ℝ)^(tᶜ).card := by
    rw [← pow_add, hcard]
  rw [he]
  have hs : ((-1 : ℝ)^t.card)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
  calc
    _ = ((-1 : ℝ)^t.card)^2 * (-1 : ℝ)^(tᶜ).card := by rw [hs, one_mul]
    _ = _ := by ring

lemma subsetAlternating_compl (f : Finset (Fin n) → ℝ) :
    subsetAlternating (fun t ↦ f tᶜ) = (-1 : ℝ)^n*subsetAlternating f := by
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    ⟨fun t ↦ tᶜ, fun t ↦ tᶜ, compl_compl, compl_compl⟩
  have h := Fintype.sum_equiv e
    (fun t ↦ (-1 : ℝ)^t.card*f tᶜ)
    (fun t ↦ (-1 : ℝ)^n*((-1 : ℝ)^t.card*f t))
    (fun t ↦ by
      dsimp [e]
      rw [parity_compl]
      have hs : ((-1 : ℝ)^n)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
      calc
        _ = ((-1 : ℝ)^n)^2 * ((-1 : ℝ)^t.card*f tᶜ) := by rw [hs, one_mul]
        _ = _ := by ring)
  simpa only [subsetAlternating, Finset.mul_sum] using h

lemma subsetBits_compl (t : Finset (Fin n)) :
    subsetBits tᶜ = flipBits (subsetBits t) := by
  funext i
  simp [subsetBits, flipBits]

/-- Both admissible denominator orientations are included. -/
theorem atom_unit_parity_bound (hn : 0 < n) (phi : FracAtom n)
    (hb : ∀ x, |phi.eval x| ≤ 1) :
    |subsetAlternating (fun t ↦ phi.eval (subsetBits t))| ≤ 2 := by
  by_cases ha : 1 ≤ phi.α
  · exact atom_positive_unit_bound hn phi ha hb
  · have hflip : 1 ≤ phi.flip.α := by
      change 1 ≤ phi.α⁻¹
      exact (one_le_inv₀ phi.hα).mpr (le_of_not_ge ha)
    have h := atom_positive_unit_bound hn phi.flip hflip (fun x ↦ by
      rw [FracAtom.flip_eval]
      exact hb _)
    simp only [FracAtom.flip_eval, ← subsetBits_compl] at h
    rw [subsetAlternating_compl (fun t ↦ phi.eval (subsetBits t)), abs_mul] at h
    simpa using h

lemma subsetAlternating_smul (f : Finset (Fin n) → ℝ) (a : ℝ) :
    subsetAlternating (fun t ↦ a*f t) = a*subsetAlternating f := by
  unfold subsetAlternating
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The exact atom bound, with an arbitrary uniform amplitude bound. -/
theorem atom_parity_amplitude_bound (hn : 0 < n) (phi : FracAtom n)
    (M : ℝ) (hb : ∀ x, |phi.eval x| ≤ M) :
    |subsetAlternating (fun t ↦ phi.eval (subsetBits t))| ≤ 2*M := by
  have hM : 0 ≤ M := (abs_nonneg (phi.eval (fun _ ↦ false))).trans (hb _)
  by_cases hz : M = 0
  · have he (x : Fin n → Bool) : phi.eval x = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa [hz] using hb x) (abs_nonneg _)
    simp [he, hz, subsetAlternating]
  · have hp : 0 < M := lt_of_le_of_ne hM (Ne.symm hz)
    have hu := atom_unit_parity_bound hn (phi.scale (1/M)) (fun x ↦ by
      rw [FracAtom.scale_eval, abs_mul, abs_of_pos (one_div_pos.mpr hp)]
      have h := (div_le_one hp).mpr (hb x)
      simpa [div_eq_mul_inv, mul_comm] using h)
    simp only [FracAtom.scale_eval] at hu
    rw [subsetAlternating_smul, abs_mul, abs_of_pos (one_div_pos.mpr hp)] at hu
    have he : (1/M)*|subsetAlternating (fun t ↦ phi.eval (subsetBits t))| =
        |subsetAlternating (fun t ↦ phi.eval (subsetBits t))|/M := by ring
    rw [he] at hu
    exact (div_le_iff₀ hp).mp hu

lemma subsetAlternating_const (hn : 0 < n) (c : ℝ) :
    subsetAlternating (fun _ : Finset (Fin n) ↦ c) = 0 := by
  have hs : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have he : (∑ t : Finset (Fin n), (-1 : ℝ)^t.card) = 0 := by
    have h := Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
    simp only [Finset.powerset_univ] at h
    exact_mod_cast h
  unfold subsetAlternating
  rw [← Finset.sum_mul, he, zero_mul]

/-- Every parity score has exponentially poor relative head-amplitude margin,
regardless of the number of heads. -/
theorem parity_margin_sum_bound {H : ℕ} (hn : 0 < n)
    (phi : Fin H → FracAtom n) (c μ : ℝ) (M : Fin H → ℝ)
    (hb : ∀ h x, |(phi h).eval x| ≤ M h)
    (hmargin : ∀ t : Finset (Fin n), μ ≤ (-1 : ℝ)^t.card *
      (c+∑ h, (phi h).eval (subsetBits t))) :
    (2 : ℝ)^n*μ ≤ 2*∑ h, M h := by
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun t _ ↦ hmargin t)
  have hcard : Fintype.card (Finset (Fin n)) = 2^n := by simp
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat] at hl
  have he : subsetAlternating (fun t ↦ c+∑ h, (phi h).eval (subsetBits t)) =
      ∑ h, subsetAlternating (fun t ↦ (phi h).eval (subsetBits t)) := by
    unfold subsetAlternating
    simp_rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    have hc : (∑ t : Finset (Fin n), (-1 : ℝ)^t.card*c) = 0 :=
      subsetAlternating_const hn c
    rw [hc, zero_add, Finset.sum_comm]
  change (2 : ℝ)^n*μ ≤ subsetAlternating _ at hl
  rw [he] at hl
  calc
    _ ≤ ∑ h, subsetAlternating (fun t ↦ (phi h).eval (subsetBits t)) := hl
    _ ≤ ∑ h, |subsetAlternating (fun t ↦ (phi h).eval (subsetBits t))| :=
      Finset.sum_le_sum fun h _ ↦ le_abs_self _
    _ ≤ ∑ h, 2*M h := Finset.sum_le_sum fun h _ ↦
      atom_parity_amplitude_bound hn (phi h) (M h) (hb h)
    _ = _ := by rw [Finset.mul_sum]

/-- In the convention of the covering theorem, the bias also contributes to total amplitude. -/
theorem parity_relative_margin_bound {H : ℕ} (hn : 0 < n)
    (phi : Fin H → FracAtom n) (c γ : ℝ) (M : Fin H → ℝ)
    (hb : ∀ h x, |(phi h).eval x| ≤ M h)
    (hpos : 0 < |c|+∑ h, M h)
    (hmargin : ∀ t : Finset (Fin n), γ*(|c|+∑ h, M h) ≤ (-1 : ℝ)^t.card *
      (c+∑ h, (phi h).eval (subsetBits t))) :
    γ ≤ 2/(2 : ℝ)^n := by
  have h := parity_margin_sum_bound hn phi c (γ*(|c|+∑ h, M h)) M hb hmargin
  have hc := abs_nonneg c
  have hpow : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hh : (2 : ℝ)^n*γ ≤ 2 := by
    by_contra hh
    have hx := mul_lt_mul_of_pos_right (lt_of_not_ge hh) hpos
    nlinarith
  exact (le_div_iff₀ hpow).mpr (by nlinarith)

#print axioms atom_subset_affine
#print axioms atom_unit_parity_bound
#print axioms atom_parity_amplitude_bound
#print axioms parity_margin_sum_bound
#print axioms parity_relative_margin_bound
end HeadComplexity.HeadParityAmplitude
