import HeadComplexity.Atoms.AtomicMargin
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.ClearedNormalForm

set_option linter.style.header false

/-! One additional genuine head repairs the origin value after scaling to a
unit margin. This is a normalization lemma, not a head-complexity lower bound. -/
namespace HeadComplexity.OriginMarginRepair
open scoped BigOperators

noncomputable def weight {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ∑ i, boolToReal (x i)

@[simp] theorem weight_origin {n : ℕ} : weight (fun _ : Fin n ↦ false) = 0 := by
  simp [weight, boolToReal]

theorem weight_nonneg {n : ℕ} (x : Fin n → Bool) : 0 ≤ weight x := by
  exact Finset.sum_nonneg fun i _ ↦ by cases x i <;> simp [boolToReal]

theorem one_le_weight {n : ℕ} (x : Fin n → Bool)
    (hx : x ≠ fun _ ↦ false) : 1 ≤ weight x := by
  have he : ∃ i, x i = true := by
    by_contra hn
    apply hx
    funext i
    cases hi : x i with
    | false => rfl
    | true => exact (hn ⟨i, hi⟩).elim
  obtain ⟨i, hi⟩ := he
  have h := Finset.single_le_sum
    (f := fun j ↦ boolToReal (x j))
    (fun j _ ↦ by cases x j <;> simp [boolToReal]) (Finset.mem_univ i)
  simpa [weight, hi, boolToReal] using h

theorem spike_bound {k t : ℝ} (hk : 0 < k) (ht : 1 ≤ t) :
    0 < k / (1 + 2*k*t) ∧ k / (1 + 2*k*t) < 1/2 := by
  have hd : 0 < 1 + 2*k*t := by positivity
  constructor
  · exact div_pos hk hd
  · apply (div_lt_iff₀ hd).mpr
    nlinarith

theorem repair_margin {y sigma k t s : ℝ}
    (hy : y = 1 ∨ y = -1) (hsigma : sigma = 1 ∨ sigma = -1)
    (hk : 0 < k) (ht : 1 ≤ t) (hs : 2 ≤ y*s) :
    3/2 < y*(s-sigma*k/(1+2*k*t)) := by
  obtain ⟨hp, hb⟩ := spike_bound hk ht
  rcases hy with rfl | rfl <;> rcases hsigma with rfl | rfl <;>
    simp only [one_mul, neg_mul, neg_div] at hs ⊢ <;>
    linarith

theorem repair_origin {sigma s k : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1) (hk : k = sigma*s-1) :
    s-sigma*k = sigma := by
  rcases hsigma with rfl | rfl <;> rw [hk] <;> ring

theorem numerator_normalization {k m t : ℝ} (hd : 1+m*t ≠ 0) :
    -k/(1+m*t) = -k + k*m*t/(1+m*t) := by
  field_simp
  ring

/-- A quantitative construction with one additional admissible atom. -/
theorem exists_origin_unit_margin {n H : ℕ}
    (phi : Fin H → FracAtom n) (c delta : ℝ)
    (f : (Fin n → Bool) → Bool) (hdelta : 0 < delta)
    (hmargin : ∀ x, delta ≤ signedLabel f x * (c + ∑ h, (phi h).eval x)) :
    ∃ (psi : Fin (H+1) → FracAtom n) (d : ℝ),
      d + ∑ h, (psi h).eval (fun _ ↦ false) = signedLabel f (fun _ ↦ false) ∧
      (∀ x, 1 ≤ signedLabel f x * (d + ∑ h, (psi h).eval x)) ∧
      (∀ x, x ≠ (fun _ ↦ false) →
        3/2 < signedLabel f x * (d + ∑ h, (psi h).eval x)) := by
  classical
  let z : Fin n → Bool := fun _ ↦ false
  let S := fun x ↦ c + ∑ h, (phi h).eval x
  let q := 2/delta
  let sigma := signedLabel f z
  let k := sigma*(q*S z)-1
  have hq : 0 < q := div_pos (by norm_num) hdelta
  have hqd : q*delta = 2 := by dsimp [q]; field_simp
  have hsigma : sigma = 1 ∨ sigma = -1 := by
    dsimp [sigma, signedLabel]
    split <;> simp
  have hy : ∀ x, signedLabel f x = 1 ∨ signedLabel f x = -1 := by
    intro x; unfold signedLabel; split <;> simp
  have hscaled : ∀ x, 2 ≤ signedLabel f x * (q*S x) := by
    intro x
    have hm := mul_le_mul_of_nonneg_left (hmargin x) hq.le
    rw [hqd] at hm
    dsimp [S]
    nlinarith [hm]
  have hk : 0 < k := by
    have hm := hscaled z
    change 2 ≤ sigma*(q*S z) at hm
    dsimp [k]
    linarith
  let atom := FracAtom.ofPositiveAffineRatio (-sigma*k) (fun _ : Fin n ↦ 0)
    1 (fun _ ↦ 2*k) (by norm_num) (fun _ ↦ by positivity)
  let psi : Fin (H+1) → FracAtom n := Fin.cons atom (fun h ↦ (phi h).scale q)
  have ha : ∀ x, atom.eval x = -sigma*k/(1+2*k*weight x) := by
    intro x
    rw [FracAtom.ofPositiveAffineRatio_eval]
    simp [affineValue, weight, Finset.mul_sum]
  have heq : ∀ x, q*c + ∑ h, (psi h).eval x =
      q*S x-sigma*k/(1+2*k*weight x) := by
    intro x
    rw [Fin.sum_univ_succ]
    simp only [psi, Fin.cons_zero, Fin.cons_succ, FracAtom.scale_eval]
    rw [ha, ← Finset.mul_sum]
    dsimp [S]
    ring
  refine ⟨psi, q*c, ?_, ?_, ?_⟩
  · rw [heq]
    simp only [weight_origin, mul_zero, add_zero, div_one]
    exact repair_origin hsigma rfl
  · intro x
    by_cases hx : x = z
    · subst x
      rw [heq]
      change 1 ≤ sigma*(q*S z-sigma*k/(1+2*k*weight z))
      simp only [z, weight_origin, mul_zero, add_zero, div_one]
      rw [repair_origin hsigma rfl]
      rcases hsigma with hs | hs <;> rw [hs] <;> norm_num
    · rw [heq]
      exact le_trans (by norm_num : (1:ℝ) ≤ 3/2)
        (repair_margin (hy x) hsigma hk (one_le_weight x hx) (hscaled x)).le
  · intro x hx
    rw [heq]
    exact repair_margin (hy x) hsigma hk (one_le_weight x hx) (hscaled x)

/-- No positive-margin or bounded-parameter hypothesis is added to the model. -/
theorem computable_origin_margin_repair {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : computableWithHeadsN n H f) :
    ∃ (psi : Fin (H+1) → FracAtom n) (d : ℝ),
      d + ∑ h, (psi h).eval (fun _ ↦ false) = signedLabel f (fun _ ↦ false) ∧
      (∀ x, 1 ≤ signedLabel f x * (d + ∑ h, (psi h).eval x)) ∧
      (∀ x, x ≠ (fun _ ↦ false) →
        3/2 < signedLabel f x * (d + ∑ h, (psi h).eval x)) := by
  classical
  obtain ⟨phi, c, hstrict⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hf)
  let margin := fun x ↦ signedLabel f x * (c + ∑ h, (phi h).eval x)
  have hpos : ∀ x, 0 < margin x := by
    intro x
    have hs := hstrict x
    cases hx : f x <;> simp [margin, signedLabel, hx] at hs ⊢ <;> linarith
  obtain ⟨x0, _, hmin⟩ :=
    (Finset.univ : Finset (Fin n → Bool)).exists_min_image margin Finset.univ_nonempty
  exact exists_origin_unit_margin phi c (margin x0) f (hpos x0)
    (fun x ↦ hmin x (Finset.mem_univ x))

/-- On a one-head score with origin value one, unit positive singleton
margins force a unit positive margin at the all-one vertex. -/
theorem singleton_margins_force_top {n : ℕ} (u d : Fin n → ℝ) (D : ℝ)
    (hd : ∀ i, 0 < d i) (hD : 0 < D)
    (hmargin : ∀ i, 1 ≤ 1 + u i / d i) :
    1 ≤ 1 + (∑ i, u i) / D := by
  have hu : ∀ i, 0 ≤ u i := by
    intro i
    have hq : 0 ≤ u i / d i := by linarith [hmargin i]
    simpa using (le_div_iff₀ (hd i)).mp hq
  have hsum : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ ↦ hu i
  exact le_add_of_nonneg_right (div_nonneg hsum hD.le)

#print axioms exists_origin_unit_margin
#print axioms computable_origin_margin_repair
#print axioms singleton_margins_force_top
end HeadComplexity.OriginMarginRepair
