import HeadComplexity.Research.RelativeMarginQuantifiers

set_option linter.style.header false

/-!
# Invariance and harmless degenerations of the requested margin

Positive rescaling preserves relative margin. Zero padding preserves it too.
Even at the same positive width, a constant can be moved from the bias into
one genuine head to make the margin arbitrarily small without changing any
score. Thus one ill-conditioned certificate never certifies that its truth
table belongs to the universally quantified low-margin class.
-/

noncomputable section

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace FracAtom

variable {n : ℕ}

/-- Add a constant to an atom while retaining all its positive parameters. -/
def translate (phi : FracAtom n) (a : ℝ) : FracAtom n where
  η := phi.η + a * phi.γ
  δ := phi.δ
  γ := phi.γ
  α := phi.α
  ρ := phi.ρ
  m := fun i ↦ phi.m i + a
  hγ := phi.hγ
  hα := phi.hα
  hρ := phi.hρ

@[simp] theorem translate_eval (phi : FracAtom n) (a : ℝ)
    (x : Fin n → Bool) : (phi.translate a).eval x = phi.eval x + a := by
  have hd := (phi.denom_pos x).ne'
  unfold eval translate
  simp only [wt] at *
  rw [div_add' _ _ _ hd]
  apply congrArg (fun z : ℝ ↦ z / (phi.γ + ∑ i, phi.ρ i *
    (if x i then phi.α else 1)))
  simp_rw [show ∀ i : Fin n,
    phi.ρ i * (if x i then phi.α else 1) *
      (phi.m i + a + if x i then phi.δ else 0) =
    phi.ρ i * (if x i then phi.α else 1) *
      (phi.m i + if x i then phi.δ else 0) +
    a * (phi.ρ i * (if x i then phi.α else 1)) by intro i; ring]
  rw [sum_add_distrib, ← mul_sum]
  ring

end FracAtom

namespace RelativeMarginQuantifiers

variable {n H K : ℕ}

theorem atomSup_scale (phi : FracAtom n) (a : ℝ) :
    atomSup (phi.scale a) = |a| * atomSup phi := by
  unfold atomSup
  simp only [FracAtom.scale_eval, abs_mul]
  apply le_antisymm
  · apply Finset.sup'_le
    intro x _
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun y ↦ |phi.eval y|) (Finset.mem_univ x)) (abs_nonneg a)
  · obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun y ↦ |phi.eval y|)
    rw [heq]
    exact Finset.le_sup' (fun y ↦ |a| * |phi.eval y|) hx

theorem score_scale (phi : Fin H → FracAtom n) (c a : ℝ) (x : Fin n → Bool) :
    score (fun h ↦ (phi h).scale a) (a * c) x = a * score phi c x := by
  simp [score, mul_add, mul_sum]

theorem amplitude_scale (phi : Fin H → FracAtom n) (c a : ℝ) :
    amplitude (fun h ↦ (phi h).scale a) (a * c) = |a| * amplitude phi c := by
  simp [amplitude, atomSup_scale, abs_mul, mul_add, mul_sum]

theorem minimumSignedScore_scale (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    minimumSignedScore f (fun h ↦ (phi h).scale a) (a * c) =
      a * minimumSignedScore f phi c := by
  unfold minimumSignedScore
  simp only [score_scale, mul_left_comm (signedLabel f _) a]
  apply le_antisymm
  · obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_inf'
      Finset.univ_nonempty (fun x ↦ signedLabel f x * score phi c x)
    rw [heq]
    exact Finset.inf'_le _ hx
  · apply Finset.le_inf'
    intro x _
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ x)) ha

/-- Rescaling the complete score by a positive scalar has exactly no effect. -/
theorem relativeMargin_scale (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    relativeMargin f (fun h ↦ (phi h).scale a) (a * c) = relativeMargin f phi c := by
  rw [relativeMargin, minimumSignedScore_scale f phi c ha.le,
    amplitude_scale, abs_of_pos ha, mul_div_mul_left _ _ ha.ne']
  rfl

@[simp] theorem atomSup_zero : atomSup (FracAtom.zero n) = 0 := by
  simp [atomSup]

theorem sum_atomSup_pad (phi : Fin H → FracAtom n) (hHK : H ≤ K) :
    ∑ k : Fin K, atomSup (FracAtom.pad phi k) = ∑ h, atomSup (phi h) := by
  classical
  symm
  let e : Fin H ↪ Fin K := ⟨Fin.castLE hHK, Fin.castLE_injective hHK⟩
  calc
    _ = ∑ k ∈ Finset.univ.image e, atomSup (FracAtom.pad phi k) := by
      rw [Finset.sum_image e.injective.injOn]
      apply Finset.sum_congr rfl
      intro h _
      simp [e, FracAtom.pad]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hnot
      have hk : ¬k.val < H := by
        intro hk
        apply hnot
        apply Finset.mem_image.mpr
        exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
      simp [FracAtom.pad, hk]

theorem relativeMargin_pad (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ) (hHK : H ≤ K) :
    relativeMargin f (FracAtom.pad phi : Fin K → FracAtom n) c =
      relativeMargin f phi c := by
  simp [relativeMargin, minimumSignedScore, amplitude, score,
    FracAtom.sum_pad_eval phi hHK, sum_atomSup_pad phi hHK]

theorem hasRelativeMargin_mono_width {f : (Fin n → Bool) → Bool} {gamma : ℝ}
    (hHK : H ≤ K) (hf : HasRelativeMargin n H f gamma) :
    HasRelativeMargin n K f gamma := by
  obtain ⟨phi, c, hs, hm⟩ := hf
  refine ⟨FracAtom.pad phi, c, ?_, ?_⟩
  · intro x
    simpa [score, FracAtom.sum_pad_eval phi hHK] using hs x
  · simpa [relativeMargin_pad f phi c hHK] using hm

/-- Move a constant from the bias to the first head, at unchanged width. -/
def moveBiasToHead (phi : Fin (H + 1) → FracAtom n) (a : ℝ) :
    Fin (H + 1) → FracAtom n :=
  Fin.cases ((phi 0).translate a) (fun h ↦ phi h.succ)

theorem score_moveBiasToHead (phi : Fin (H + 1) → FracAtom n)
    (c a : ℝ) (x : Fin n → Bool) :
    score (moveBiasToHead phi a) (c - a) x = score phi c x := by
  simp [score, moveBiasToHead, Fin.sum_univ_succ]
  ring

/-- Bad conditioning is possible at the very same nonzero width and with an
identical complete score table. This is not a statement about optimal margin. -/
theorem exists_same_width_same_score_small_margin
    {f : (Fin n → Bool) → Bool} {phi : Fin (H + 1) → FracAtom n} {c : ℝ}
    (hs : StrictlyRepresents f phi c) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (psi : Fin (H + 1) → FracAtom n) (b : ℝ),
      (∀ x, score psi b x = score phi c x) ∧
      StrictlyRepresents f psi b ∧ relativeMargin f psi b < epsilon := by
  let m := minimumSignedScore f phi c
  have hm : 0 < m := minimumSignedScore_pos_iff.mpr hs
  let a : ℝ := c + m / epsilon + 1
  let psi := moveBiasToHead phi a
  have heq (x : Fin n → Bool) : score psi (c - a) x = score phi c x :=
    score_moveBiasToHead phi c a x
  have hs' : StrictlyRepresents f psi (c - a) := by
    intro x
    rw [heq]
    exact hs x
  refine ⟨psi, c - a, heq, hs', ?_⟩
  have hmin : minimumSignedScore f psi (c - a) = m := by
    unfold minimumSignedScore
    simp_rw [heq]
    rfl
  have hca : c - a = -(m / epsilon + 1) := by dsimp [a]; ring
  have hpos : 0 < m / epsilon + 1 := by positivity
  have hamp : m / epsilon + 1 ≤ amplitude psi (c - a) := by
    unfold amplitude
    rw [hca, abs_neg, abs_of_pos hpos]
    exact le_add_of_nonneg_right (sum_nonneg fun h _ ↦ atomSup_nonneg _)
  rw [relativeMargin, hmin, div_lt_iff₀ (amplitude_pos_of_strict hs')]
  have hmul := mul_le_mul_of_nonneg_left hamp hepsilon.le
  have hid : epsilon * (m / epsilon + 1) = m + epsilon := by field_simp
  linarith

#print axioms relativeMargin_scale
#print axioms relativeMargin_pad
#print axioms hasRelativeMargin_mono_width
#print axioms exists_same_width_same_score_small_margin

end RelativeMarginQuantifiers
end HeadComplexity
