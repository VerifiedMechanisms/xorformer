import HeadComplexity.Results.CountingLowerBound
import HeadComplexity.Atoms.AtomicMargin

set_option linter.style.header false

/-!
# Relative margins and the unrestricted counting gap

The amplitude is exactly the absolute bias plus the sum of the individual
head suprema on the full Boolean cube. Every atom is a genuine `FracAtom`.
The low-margin class quantifies over all representations at the comparison
width. No quantitative margin-repair hypothesis is proved in this file.
-/

noncomputable section

namespace HeadComplexity.RelativeMarginQuantifiers

open Finset
open scoped BigOperators

variable {n H K : ℕ}

/-- Full-cube supremum norm of the output of a genuine original-model head. -/
def atomSup (phi : FracAtom n) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).sup' Finset.univ_nonempty
    (fun x ↦ |phi.eval x|)

theorem abs_eval_le_atomSup (phi : FracAtom n) (x : Fin n → Bool) :
    |phi.eval x| ≤ atomSup phi :=
  Finset.le_sup' (fun y ↦ |phi.eval y|) (Finset.mem_univ x)

theorem atomSup_nonneg (phi : FracAtom n) : 0 ≤ atomSup phi :=
  (abs_nonneg (phi.eval (fun _ ↦ false))).trans
    (abs_eval_le_atomSup phi _)

/-- The denominator in the requested relative margin. -/
def amplitude (phi : Fin H → FracAtom n) (c : ℝ) : ℝ :=
  |c| + ∑ h, atomSup (phi h)

def score (phi : Fin H → FracAtom n) (c : ℝ) (x : Fin n → Bool) : ℝ :=
  c + ∑ h, (phi h).eval x

theorem amplitude_nonneg (phi : Fin H → FracAtom n) (c : ℝ) :
    0 ≤ amplitude phi c :=
  add_nonneg (abs_nonneg c) (Finset.sum_nonneg fun h _ ↦ atomSup_nonneg (phi h))

theorem abs_score_le_amplitude (phi : Fin H → FracAtom n) (c : ℝ)
    (x : Fin n → Bool) : |score phi c x| ≤ amplitude phi c := by
  calc
    _ ≤ |c| + |∑ h, (phi h).eval x| := abs_add_le _ _
    _ ≤ |c| + ∑ h, |(phi h).eval x| :=
      add_le_add le_rfl (abs_sum_le_sum_abs _ _)
    _ ≤ amplitude phi c := by
      unfold amplitude
      exact add_le_add le_rfl
        (sum_le_sum fun h _ ↦ abs_eval_le_atomSup (phi h) x)

/-- Strict labels at every input, including the original model's false class. -/
def StrictlyRepresents (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ) : Prop :=
  ∀ x, 0 < signedLabel f x * score phi c x

theorem amplitude_pos_of_strict {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c : ℝ} (hs : StrictlyRepresents f phi c) :
    0 < amplitude phi c := by
  let x : Fin n → Bool := fun _ ↦ false
  have h := hs x
  have he : |signedLabel f x * score phi c x| = |score phi c x| := by
    rw [abs_mul, abs_signedLabel, one_mul]
  have hp : 0 < |score phi c x| := by rw [← he, abs_of_pos h]; exact h
  exact hp.trans_le (abs_score_le_amplitude phi c x)

/-- The numerator of the relative margin, minimized over the whole cube. -/
def minimumSignedScore (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n → Bool)).inf' Finset.univ_nonempty
    (fun x ↦ signedLabel f x * score phi c x)

def relativeMargin (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ) : ℝ :=
  minimumSignedScore f phi c / amplitude phi c

theorem minimumSignedScore_pos_iff {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c : ℝ} :
    0 < minimumSignedScore f phi c ↔ StrictlyRepresents f phi c := by
  simp only [minimumSignedScore, Finset.lt_inf'_iff, Finset.mem_univ, true_implies,
    StrictlyRepresents]

theorem relativeMargin_pos {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c : ℝ} (hs : StrictlyRepresents f phi c) :
    0 < relativeMargin f phi c :=
  div_pos (minimumSignedScore_pos_iff.mpr hs) (amplitude_pos_of_strict hs)

theorem le_relativeMargin_iff {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c gamma : ℝ} (hs : StrictlyRepresents f phi c) :
    gamma ≤ relativeMargin f phi c ↔
      ∀ x, gamma * amplitude phi c ≤ signedLabel f x * score phi c x := by
  rw [relativeMargin, le_div_iff₀ (amplitude_pos_of_strict hs)]
  simp only [minimumSignedScore, Finset.le_inf'_iff, Finset.mem_univ, true_implies]

theorem relativeMargin_le_one {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c : ℝ} (hs : StrictlyRepresents f phi c) :
    relativeMargin f phi c ≤ 1 := by
  rw [relativeMargin, div_le_one (amplitude_pos_of_strict hs)]
  let x : Fin n → Bool := fun _ ↦ false
  calc
    minimumSignedScore f phi c ≤ signedLabel f x * score phi c x :=
      Finset.inf'_le _ (Finset.mem_univ x)
    _ ≤ |signedLabel f x * score phi c x| := le_abs_self _
    _ = |score phi c x| := by rw [abs_mul, abs_signedLabel, one_mul]
    _ ≤ amplitude phi c := abs_score_le_amplitude phi c x

/-- A constant output is a valid original head, also in dimension zero. -/
def constantAtom (n : ℕ) (a : ℝ) : FracAtom n where
  η := a * (1 + n)
  δ := 0
  γ := 1
  α := 1
  ρ := fun _ ↦ 1
  m := fun _ ↦ 0
  hγ := one_pos
  hα := one_pos
  hρ := fun _ ↦ one_pos

@[simp] theorem constantAtom_eval (a : ℝ) (x : Fin n → Bool) :
    (constantAtom n a).eval x = a := by
  simp only [constantAtom, FracAtom.eval, FracAtom.wt, ite_self, mul_one,
    add_zero, mul_zero, sum_const_zero, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hn : (1 : ℝ) + n ≠ 0 := by positivity
  field_simp

@[simp] theorem atomSup_constantAtom (a : ℝ) : atomSup (constantAtom n a) = |a| := by
  simp [atomSup]

/-- One additional constant head, cancelled by the free bias. -/
def addCancelledConstant (phi : Fin H → FracAtom n) (a : ℝ) :
    Fin (H + 1) → FracAtom n := Fin.cases (constantAtom n a) phi

theorem score_addCancelledConstant (phi : Fin H → FracAtom n) (c a : ℝ)
    (x : Fin n → Bool) :
    score (addCancelledConstant phi a) (c - a) x = score phi c x := by
  simp [score, addCancelledConstant, Fin.sum_univ_succ]
  ring

theorem amplitude_addCancelledConstant (phi : Fin H → FracAtom n) (c a : ℝ) :
    amplitude (addCancelledConstant phi a) (c - a) =
      |c - a| + |a| + ∑ h, atomSup (phi h) := by
  simp [amplitude, addCancelledConstant, Fin.sum_univ_succ, add_assoc]

/-- Every strict representation can be made arbitrarily ill-conditioned by
one extra admissible head, while keeping its complete score table exactly.
This says nothing about the best margin among alternative representations. -/
theorem exists_same_score_small_margin {f : (Fin n → Bool) → Bool}
    {phi : Fin H → FracAtom n} {c : ℝ} (hs : StrictlyRepresents f phi c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (psi : Fin (H + 1) → FracAtom n) (b : ℝ),
      (∀ x, score psi b x = score phi c x) ∧
      StrictlyRepresents f psi b ∧ relativeMargin f psi b < epsilon := by
  let m := minimumSignedScore f phi c
  have hm : 0 < m := minimumSignedScore_pos_iff.mpr hs
  let a := m / epsilon + 1
  have ha : 0 < a := by dsimp [a]; positivity
  let psi := addCancelledConstant phi a
  have heq (x : Fin n → Bool) : score psi (c - a) x = score phi c x :=
    score_addCancelledConstant phi c a x
  have hs' : StrictlyRepresents f psi (c - a) := by
    intro x
    rw [heq]
    exact hs x
  refine ⟨psi, c - a, heq, hs', ?_⟩
  have hmin : minimumSignedScore f psi (c - a) = m := by
    unfold minimumSignedScore
    simp_rw [heq]
    rfl
  have hamp : a ≤ amplitude psi (c - a) := by
    rw [amplitude_addCancelledConstant, abs_of_pos ha]
    have hsum : 0 ≤ ∑ h, atomSup (phi h) :=
      sum_nonneg fun h _ ↦ atomSup_nonneg _
    linarith [abs_nonneg (c - a)]
  rw [relativeMargin, hmin, div_lt_iff₀ (amplitude_pos_of_strict hs')]
  have hmul := mul_le_mul_of_nonneg_left hamp hepsilon.le
  have hid : epsilon * a = m + epsilon := by
    dsimp [a]
    field_simp
  linarith

/-- Existence of a genuine width-H representation with the requested margin. -/
def HasRelativeMargin (n H : ℕ) (f : (Fin n → Bool) → Bool) (gamma : ℝ) : Prop :=
  ∃ (phi : Fin H → FracAtom n) (c : ℝ),
    StrictlyRepresents f phi c ∧ gamma ≤ relativeMargin f phi c

def highMarginFunctions (n H : ℕ) (gamma : ℝ) :
    Set ((Fin n → Bool) → Bool) :=
  {f | HasRelativeMargin n H f gamma}

theorem hasRelativeMargin_mono {f : (Fin n → Bool) → Bool} {gamma eta : ℝ}
    (hle : eta ≤ gamma) (hf : HasRelativeMargin n H f gamma) :
    HasRelativeMargin n H f eta := by
  obtain ⟨phi, c, hs, hg⟩ := hf
  exact ⟨phi, c, hs, hle.trans hg⟩

theorem computable_of_hasRelativeMargin {f : (Fin n → Bool) → Bool} {gamma : ℝ}
    (hf : HasRelativeMargin n H f gamma) : computableWithHeadsN n H f := by
  obtain ⟨phi, c, hs, _⟩ := hf
  apply computable_of_fracComputable
  refine ⟨phi, c, fun x ↦ ?_⟩
  have hx := hs x
  cases hfx : f x <;> simp [signedLabel, score, hfx] at hx ⊢ <;> linarith

/-- Strictification does not add heads. Its quantitative margin is unspecified. -/
theorem exists_positive_margin_of_computable {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) :
    ∃ gamma : ℝ, 0 < gamma ∧ HasRelativeMargin n H f gamma := by
  obtain ⟨phi, c, hs⟩ := exists_strict_fracCertificate (fracComputable_of_computable hf)
  have hs' : StrictlyRepresents f phi c := by
    intro x
    have hx := hs x
    cases hfx : f x <;> simp [signedLabel, score, hfx] at hx ⊢ <;> linarith
  exact ⟨relativeMargin f phi c, relativeMargin_pos hs', phi, c, hs', le_rfl⟩

/-- Finiteness of truth tables gives a common positive margin at each fixed n,H.
There is no effective estimate on this margin as n or H varies. -/
theorem exists_uniform_positive_margin (n H : ℕ) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ f,
      computableWithHeadsN n H f → HasRelativeMargin n H f gamma := by
  classical
  have hex (f : (Fin n → Bool) → Bool) :
      ∃ gamma : ℝ, 0 < gamma ∧
        (computableWithHeadsN n H f → HasRelativeMargin n H f gamma) := by
    by_cases hf : computableWithHeadsN n H f
    · obtain ⟨gamma, hg, hmargin⟩ := exists_positive_margin_of_computable hf
      exact ⟨gamma, hg, fun _ ↦ hmargin⟩
    · exact ⟨1, one_pos, fun h ↦ (hf h).elim⟩
  choose g hg using hex
  let gamma : ℝ := (Finset.univ : Finset ((Fin n → Bool) → Bool)).inf'
    Finset.univ_nonempty g
  refine ⟨gamma, ?_, ?_⟩
  · change 0 < Finset.univ.inf' Finset.univ_nonempty g
    rw [Finset.lt_inf'_iff]
    exact fun f _ ↦ (hg f).1
  · intro f hf
    exact hasRelativeMargin_mono (Finset.inf'_le g (Finset.mem_univ f)) ((hg f).2 hf)

/-- Truth tables representable at H but having no adequate-margin representation
at K. This is a universal condition over all comparison-width representations. -/
def allRepresentationsLowMargin (n H K : ℕ) (gamma : ℝ) :
    Set ((Fin n → Bool) → Bool) :=
  headComputableFunctions n H \ highMarginFunctions n K gamma

theorem mem_allRepresentationsLowMargin_iff
    (f : (Fin n → Bool) → Bool) (gamma : ℝ) :
    f ∈ allRepresentationsLowMargin n H K gamma ↔
      computableWithHeadsN n H f ∧
        ∀ (phi : Fin K → FracAtom n) (c : ℝ),
          StrictlyRepresents f phi c → relativeMargin f phi c < gamma := by
  simp only [allRepresentationsLowMargin, Set.mem_sdiff, headComputableFunctions,
    highMarginFunctions, Set.mem_ofPred_eq, HasRelativeMargin]
  push Not
  rfl

theorem card_computable_le_high_add_low (gamma : ℝ) :
    (headComputableFunctions n H).ncard ≤
      (highMarginFunctions n K gamma).ncard +
        (allRepresentationsLowMargin n H K gamma).ncard := by
  have hsub : headComputableFunctions n H ⊆
      highMarginFunctions n K gamma ∪ allRepresentationsLowMargin n H K gamma := by
    intro f hf
    by_cases hg : f ∈ highMarginFunctions n K gamma
    · exact Or.inl hg
    · exact Or.inr ⟨hf, hg⟩
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)

/-- The exact finite counting route to the original W(n), with both counts
explicit and without any analytic theorem hidden in the statement. -/
theorem worstCase_gt_of_high_and_low_counts {gamma : ℝ} {A B : ℕ}
    (hhigh : (highMarginFunctions n K gamma).ncard ≤ A)
    (hlow : (allRepresentationsLowMargin n H K gamma).ncard ≤ B)
    (hbudget : A + B < 2 ^ (2 ^ n)) :
    H < worstCaseHeadComplexity n := by
  have hcard : (headComputableFunctions n H).ncard < 2 ^ (2 ^ n) :=
    (card_computable_le_high_add_low gamma).trans_lt
      ((Nat.add_le_add hhigh hlow).trans_lt hbudget)
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt hcard
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

#print axioms exists_uniform_positive_margin
#print axioms exists_same_score_small_margin
#print axioms mem_allRepresentationsLowMargin_iff
#print axioms worstCase_gt_of_high_and_low_counts

end HeadComplexity.RelativeMarginQuantifiers
