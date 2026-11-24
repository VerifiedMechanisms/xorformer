import HeadComplexity.Research.RelativeMarginQuantifiers

/-!
Subtracting each head's full-cube midrange, and transferring the constants to
the free bias, preserves the score exactly and does not increase its amplitude.
All centered atoms remain genuine original-model `FracAtom`s.
-/

noncomputable section

namespace HeadComplexity.MidrangeMarginCentering

open Finset RelativeMarginQuantifiers
open scoped BigOperators

variable {n H : ℕ}

/-- Subtraction of a constant changes only readout parameters. -/
def subtractConstant (phi : FracAtom n) (a : ℝ) : FracAtom n where
  η := phi.η - a * phi.γ
  δ := phi.δ
  γ := phi.γ
  α := phi.α
  ρ := phi.ρ
  m := fun i => phi.m i - a
  hγ := phi.hγ
  hα := phi.hα
  hρ := phi.hρ

@[simp] theorem subtractConstant_eval (phi : FracAtom n) (a : ℝ)
    (x : Fin n → Bool) : (subtractConstant phi a).eval x = phi.eval x - a := by
  have hd := (phi.denom_pos x).ne'
  have hs : (∑ i, phi.wt x i * (phi.m i - a + if x i then phi.δ else 0)) =
      (∑ i, phi.wt x i * (phi.m i + if x i then phi.δ else 0)) -
        a * ∑ i, phi.wt x i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (phi.η - a * phi.γ +
      ∑ i, phi.wt x i * (phi.m i - a + if x i then phi.δ else 0)) /
      (phi.γ + ∑ i, phi.wt x i) = phi.eval x - a
  rw [hs]
  unfold FracAtom.eval
  field_simp
  ring

def rangeMin (phi : FracAtom n) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).inf' Finset.univ_nonempty phi.eval

def rangeMax (phi : FracAtom n) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).sup' Finset.univ_nonempty phi.eval

def midrange (phi : FracAtom n) : ℝ := (rangeMin phi + rangeMax phi) / 2

def radius (phi : FracAtom n) : ℝ := (rangeMax phi - rangeMin phi) / 2

def center (phi : FracAtom n) : FracAtom n := subtractConstant phi (midrange phi)

theorem rangeMin_le_eval (phi : FracAtom n) (x : Fin n → Bool) :
    rangeMin phi ≤ phi.eval x := Finset.inf'_le _ (Finset.mem_univ x)

theorem eval_le_rangeMax (phi : FracAtom n) (x : Fin n → Bool) :
    phi.eval x ≤ rangeMax phi := Finset.le_sup' _ (Finset.mem_univ x)

theorem radius_nonneg (phi : FracAtom n) : 0 ≤ radius phi := by
  have h := (rangeMin_le_eval phi (fun _ => false)).trans
    (eval_le_rangeMax phi (fun _ => false))
  unfold radius
  linarith

@[simp] theorem center_eval (phi : FracAtom n) (x : Fin n → Bool) :
    (center phi).eval x = phi.eval x - midrange phi := subtractConstant_eval _ _ _

theorem atomSup_center_le_radius (phi : FracAtom n) :
    atomSup (center phi) ≤ radius phi := by
  apply Finset.sup'_le
  intro x _
  rw [center_eval]
  apply abs_le.mpr
  have hmin := rangeMin_le_eval phi x
  have hmax := eval_le_rangeMax phi x
  unfold midrange radius
  constructor <;> linarith

theorem abs_midrange_add_radius_le_atomSup (phi : FracAtom n) :
    |midrange phi| + radius phi ≤ atomSup phi := by
  have hlo : -atomSup phi ≤ rangeMin phi := by
    apply Finset.le_inf'
    intro x _
    exact (neg_le_neg (abs_eval_le_atomSup phi x)).trans (neg_abs_le _)
  have hhi : rangeMax phi ≤ atomSup phi := by
    apply Finset.sup'_le
    intro x _
    exact (le_abs_self _).trans (abs_eval_le_atomSup phi x)
  have hm : |midrange phi| ≤ atomSup phi - radius phi := by
    apply abs_le.mpr
    unfold midrange radius
    constructor <;> linarith
  linarith

theorem abs_midrange_add_atomSup_center_le (phi : FracAtom n) :
    |midrange phi| + atomSup (center phi) ≤ atomSup phi :=
  (add_le_add le_rfl (atomSup_center_le_radius phi)).trans
    (abs_midrange_add_radius_le_atomSup phi)

@[simp] theorem rangeMax_center (phi : FracAtom n) :
    rangeMax (center phi) = radius phi := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x _
    rw [center_eval]
    have hx := eval_le_rangeMax phi x
    unfold midrange radius
    linarith
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin n → Bool))) Finset.univ_nonempty phi.eval
    have he := eval_le_rangeMax (center phi) x
    rw [center_eval] at he
    change rangeMax phi = phi.eval x at hxe
    unfold midrange radius at *
    linarith

@[simp] theorem rangeMin_center (phi : FracAtom n) :
    rangeMin (center phi) = -radius phi := by
  apply le_antisymm
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (Fin n → Bool))) Finset.univ_nonempty phi.eval
    have he := rangeMin_le_eval (center phi) x
    rw [center_eval] at he
    change rangeMin phi = phi.eval x at hxe
    unfold midrange radius at *
    linarith
  · apply Finset.le_inf'
    intro x _
    rw [center_eval]
    have hx := rangeMin_le_eval phi x
    unfold midrange radius
    linarith

def centeredHeads (phi : Fin H → FracAtom n) : Fin H → FracAtom n := fun h => center (phi h)

def centeredBias (phi : Fin H → FracAtom n) (c : ℝ) : ℝ := c + ∑ h, midrange (phi h)

theorem centered_score (phi : Fin H → FracAtom n) (c : ℝ) (x : Fin n → Bool) :
    score (centeredHeads phi) (centeredBias phi c) x = score phi c x := by
  simp only [score, centeredHeads, centeredBias, center_eval, Finset.sum_sub_distrib]
  ring

theorem centered_amplitude_le (phi : Fin H → FracAtom n) (c : ℝ) :
    amplitude (centeredHeads phi) (centeredBias phi c) ≤ amplitude phi c := by
  unfold amplitude centeredBias centeredHeads
  calc
    |c + ∑ h, midrange (phi h)| + ∑ h, atomSup (center (phi h))
        ≤ |c| + ∑ h, |midrange (phi h)| + ∑ h, atomSup (center (phi h)) := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _))
    _ = |c| + ∑ h, (|midrange (phi h)| + atomSup (center (phi h))) := by
          rw [Finset.sum_add_distrib]
          ring
    _ ≤ |c| + ∑ h, atomSup (phi h) := by
          gcongr with h
          exact abs_midrange_add_atomSup_center_le (phi h)

theorem centered_relativeMargin_ge {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c : ℝ} (hs : StrictlyRepresents f phi c) :
    relativeMargin f phi c ≤ relativeMargin f (centeredHeads phi) (centeredBias phi c) := by
  have hs' : StrictlyRepresents f (centeredHeads phi) (centeredBias phi c) := by
    intro x
    rw [centered_score]
    exact hs x
  have hm : minimumSignedScore f (centeredHeads phi) (centeredBias phi c) =
      minimumSignedScore f phi c := by
    unfold minimumSignedScore
    simp_rw [centered_score]
  unfold relativeMargin
  rw [hm]
  exact div_le_div_of_nonneg_left (minimumSignedScore_pos_iff.mpr hs).le
    (amplitude_pos_of_strict hs') (centered_amplitude_le phi c)

/-- Every relative-margin certificate admits centered genuine heads at the same
width and at least the same margin. -/
theorem exists_centered_certificate {f : (Fin n → Bool) → Bool} {gamma : ℝ}
    (hf : HasRelativeMargin n H f gamma) :
    ∃ (phi : Fin H → FracAtom n) (c : ℝ),
      StrictlyRepresents f phi c ∧ gamma ≤ relativeMargin f phi c ∧
        ∀ h, rangeMin (phi h) + rangeMax (phi h) = 0 := by
  obtain ⟨phi, c, hs, hg⟩ := hf
  refine ⟨centeredHeads phi, centeredBias phi c, ?_,
    hg.trans (centered_relativeMargin_ge hs), ?_⟩
  · intro x
    rw [centered_score]
    exact hs x
  · intro h
    simp [centeredHeads]

end HeadComplexity.MidrangeMarginCentering
