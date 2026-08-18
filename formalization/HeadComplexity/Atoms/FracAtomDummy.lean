import HeadComplexity.Atoms.Restriction
import Mathlib.Order.Filter.Finite

set_option linter.style.header false

/-!
# Adding dummy coordinates to fractional atoms

A fractional atom cannot literally ignore an input coordinate, because every
coordinate weight is required to be strictly positive.  On the finite Boolean
cube this causes no loss: give every dummy coordinate one common sufficiently
small positive weight.  At weight zero the resulting rational expression is
exactly the original atom, and continuity plus a finite strict margin preserves
all classifier signs for one positive choice of the weight.
-/

namespace HeadComplexity

open Finset Filter
open scoped BigOperators Topology

variable {m n H : ℕ}

/-- Read an ambient bit vector along an injective list of active coordinates. -/
def pullBitsAlong (e : Fin m ↪ Fin n) (y : Fin n → Bool) : Fin m → Bool :=
  fun i ↦ y (e i)

/-- The coordinate face associated with an embedding.  Its base is irrelevant
for the sum decomposition used below. -/
noncomputable def embeddingFace (e : Fin m ↪ Fin n) : CoordFace m n where
  free := e
  base := fun _ ↦ false

@[simp] theorem pullBitsAlong_embeddingFace_apply (e : Fin m ↪ Fin n)
    (x : Fin m → Bool) :
    pullBitsAlong e ((embeddingFace e).apply x) = x := by
  funext i
  exact (embeddingFace e).apply_free x i

namespace FracAtom

/-- The old coordinate parameter on an active coordinate, and `epsilon` on a
dummy coordinate.  This auxiliary definition is meaningful also at zero. -/
noncomputable def dummyRhoAt (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (j : Fin n) : ℝ :=
  if h : ∃ i, e i = j then phi.ρ (Classical.choose h) else epsilon

/-- Transport the value parameter to active coordinates and put zero on dummy
coordinates. -/
noncomputable def dummyM (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (j : Fin n) : ℝ :=
  if h : ∃ i, e i = j then phi.m (Classical.choose h) else 0

@[simp] theorem dummyRhoAt_active (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (i : Fin m) :
    dummyRhoAt phi e epsilon (e i) = phi.ρ i := by
  rw [dummyRhoAt, dif_pos ⟨i, rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec
    (show ∃ k, e k = e i from ⟨i, rfl⟩))

@[simp] theorem dummyM_active (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (i : Fin m) : dummyM phi e (e i) = phi.m i := by
  rw [dummyM, dif_pos ⟨i, rfl⟩]
  congr 1
  exact e.injective (Classical.choose_spec
    (show ∃ k, e k = e i from ⟨i, rfl⟩))

theorem dummyRhoAt_fixed (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) {j : Fin n} (hj : j ∈ (embeddingFace e).fixedSet) :
    dummyRhoAt phi e epsilon j = epsilon := by
  rw [dummyRhoAt, dif_neg]
  intro h
  exact (Finset.mem_sdiff.mp hj).2 ((embeddingFace e).mem_freeSet j |>.2 h)

theorem dummyM_fixed (phi : FracAtom m) (e : Fin m ↪ Fin n)
    {j : Fin n} (hj : j ∈ (embeddingFace e).fixedSet) :
    dummyM phi e j = 0 := by
  rw [dummyM, dif_neg]
  intro h
  exact (Finset.mem_sdiff.mp hj).2 ((embeddingFace e).mem_freeSet j |>.2 h)

/-- Give all dummy coordinates the same positive weight. -/
noncomputable def liftDummy (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) : FracAtom n where
  η := phi.η
  δ := phi.δ
  γ := phi.γ
  α := phi.α
  ρ := dummyRhoAt phi e epsilon
  m := dummyM phi e
  hγ := phi.hγ
  hα := phi.hα
  hρ := fun j ↦ by
    by_cases h : ∃ i, e i = j
    · rw [dummyRhoAt, dif_pos h]
      exact phi.hρ _
    · rw [dummyRhoAt, dif_neg h]
      exact hepsilon

/-- The denominator contribution of the dummy coordinates with their common
weight factored out. -/
noncomputable def dummyDenomExtra (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (y : Fin n → Bool) : ℝ :=
  ∑ j ∈ (embeddingFace e).fixedSet, if y j then phi.α else 1

/-- The numerator contribution of the dummy coordinates with their common
weight factored out. -/
noncomputable def dummyNumerExtra (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (y : Fin n → Bool) : ℝ :=
  ∑ j ∈ (embeddingFace e).fixedSet,
    (if y j then phi.α else 1) * (if y j then phi.δ else 0)

/-- The ambient rational expression as a function of the common dummy weight.
At zero this is the original atom evaluated on the active coordinates. -/
noncomputable def dummyEvalAt (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (y : Fin n → Bool) : ℝ :=
  let x := pullBitsAlong e y
  ((phi.η + ∑ i, phi.wt x i * (phi.m i + if x i then phi.δ else 0))
      + epsilon * dummyNumerExtra phi e y) /
    ((phi.γ + ∑ i, phi.wt x i) + epsilon * dummyDenomExtra phi e y)

@[simp] theorem dummyEvalAt_zero (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (y : Fin n → Bool) :
    dummyEvalAt phi e 0 y = phi.eval (pullBitsAlong e y) := by
  simp [dummyEvalAt, FracAtom.eval]

private theorem liftDummy_wt_active (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (y : Fin n → Bool) (i : Fin m) :
    (phi.liftDummy e epsilon hepsilon).wt y (e i) =
      phi.wt (pullBitsAlong e y) i := by
  simp [FracAtom.wt, liftDummy, pullBitsAlong]

private theorem liftDummy_wt_fixed (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (y : Fin n → Bool)
    {j : Fin n} (hj : j ∈ (embeddingFace e).fixedSet) :
    (phi.liftDummy e epsilon hepsilon).wt y j =
      epsilon * (if y j then phi.α else 1) := by
  simp [FracAtom.wt, liftDummy, dummyRhoAt_fixed phi e epsilon hj]

/-- For positive weight, the auxiliary rational expression is exactly the
evaluation of the lifted genuine atom. -/
theorem liftDummy_eval (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (y : Fin n → Bool) :
    (phi.liftDummy e epsilon hepsilon).eval y = dummyEvalAt phi e epsilon y := by
  classical
  have hfreeDenom :
      (∑ i, (phi.liftDummy e epsilon hepsilon).wt y
        ((embeddingFace e).free i)) =
        ∑ i, phi.wt (pullBitsAlong e y) i := by
    apply Finset.sum_congr rfl
    intro i _
    change (phi.liftDummy e epsilon hepsilon).wt y (e i) = _
    exact liftDummy_wt_active phi e epsilon hepsilon y i
  have hfreeNumer :
      (∑ i, (phi.liftDummy e epsilon hepsilon).wt y
        ((embeddingFace e).free i) *
          ((phi.liftDummy e epsilon hepsilon).m ((embeddingFace e).free i) +
            if y ((embeddingFace e).free i) then
              (phi.liftDummy e epsilon hepsilon).δ else 0)) =
        ∑ i, phi.wt (pullBitsAlong e y) i *
          (phi.m i + if pullBitsAlong e y i then phi.δ else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    change (phi.liftDummy e epsilon hepsilon).wt y (e i) *
        ((phi.liftDummy e epsilon hepsilon).m (e i) +
          if y (e i) then (phi.liftDummy e epsilon hepsilon).δ else 0) = _
    rw [liftDummy_wt_active]
    simp [liftDummy, pullBitsAlong]
  have hfixedDenom :
      (∑ j ∈ (embeddingFace e).fixedSet,
        (phi.liftDummy e epsilon hepsilon).wt y j) =
        epsilon * dummyDenomExtra phi e y := by
    rw [dummyDenomExtra, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact liftDummy_wt_fixed phi e epsilon hepsilon y hj
  have hfixedNumer :
      (∑ j ∈ (embeddingFace e).fixedSet,
        (phi.liftDummy e epsilon hepsilon).wt y j *
          ((phi.liftDummy e epsilon hepsilon).m j +
            if y j then (phi.liftDummy e epsilon hepsilon).δ else 0)) =
        epsilon * dummyNumerExtra phi e y := by
    rw [dummyNumerExtra, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [liftDummy_wt_fixed phi e epsilon hepsilon y hj]
    simp only [liftDummy]
    rw [dummyM_fixed phi e hj]
    simp only [zero_add]
    ring
  unfold FracAtom.eval dummyEvalAt
  rw [(embeddingFace e).sum_eq_free_add_fixed
      (fun j ↦ (phi.liftDummy e epsilon hepsilon).wt y j)]
  rw [(embeddingFace e).sum_eq_free_add_fixed
      (fun j ↦ (phi.liftDummy e epsilon hepsilon).wt y j *
        ((phi.liftDummy e epsilon hepsilon).m j +
          if y j then (phi.liftDummy e epsilon hepsilon).δ else 0))]
  rw [hfreeDenom, hfixedDenom, hfreeNumer, hfixedNumer]
  simp only [liftDummy]
  congr 1 <;> ring

/-- Dependence of the auxiliary atom value on the dummy weight is continuous
at zero. -/
theorem continuousAt_dummyEvalAt (phi : FracAtom m) (e : Fin m ↪ Fin n)
    (y : Fin n → Bool) :
    ContinuousAt (fun epsilon : ℝ ↦ dummyEvalAt phi e epsilon y) 0 := by
  unfold dummyEvalAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simpa using ne_of_gt (phi.denom_pos (pullBitsAlong e y))

end FracAtom

/-- A finite threshold representation can be shifted so that every cube point,
including every false point, has a nonzero score. -/
private theorem fracComputable.strictCertificate
    {f : (Fin m → Bool) → Bool} (hf : fracComputable m H f) :
    ∃ (phi : Fin H → FracAtom m) (c : ℝ),
      ∀ x : Fin m → Bool,
        ((0 < c + ∑ h, (phi h).eval x ↔ f x = true) ∧
          c + ∑ h, (phi h).eval x ≠ 0) := by
  classical
  rcases hf with ⟨phi, c, hphi⟩
  let score : (Fin m → Bool) → ℝ := fun x ↦ c + ∑ h, (phi h).eval x
  let trueInputs : Finset (Fin m → Bool) :=
    Finset.univ.filter fun x ↦ f x = true
  by_cases hT : trueInputs.Nonempty
  · let margin : ℝ := trueInputs.inf' hT score / 2
    have hmargin_pos : 0 < margin := by
      apply half_pos
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact (hphi x).mpr (Finset.mem_filter.mp hx).2
    refine ⟨phi, c - margin, fun x ↦ ?_⟩
    have hrewrite : c - margin + ∑ h, (phi h).eval x = score x - margin := by
      dsimp [score]
      ring
    rw [hrewrite]
    cases hfx : f x with
    | false =>
        have hnpos : score x ≤ 0 := by
          apply le_of_not_gt
          intro hpos
          have := (hphi x).mp hpos
          simp [hfx] at this
        constructor
        · constructor
          · intro hpos
            exfalso
            linarith
          · simp
        · linarith
    | true =>
        have hxT : x ∈ trueInputs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩
        have hle : trueInputs.inf' hT score ≤ score x :=
          Finset.inf'_le score hxT
        have hpos : 0 < score x - margin := by
          dsimp [margin] at hmargin_pos ⊢
          linarith
        exact ⟨by simp [hpos], ne_of_gt hpos⟩
  · refine ⟨phi, c - 1, fun x ↦ ?_⟩
    have hfalse : f x = false := by
      cases hfx : f x with
      | false => rfl
      | true =>
          exfalso
          exact hT ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩⟩
    have hnpos : score x ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have := (hphi x).mp hpos
      simp [hfalse] at this
    have hrewrite : c - 1 + ∑ h, (phi h).eval x = score x - 1 := by
      dsimp [score]
      ring
    rw [hrewrite]
    constructor
    · constructor
      · intro hpos
        exfalso
        linarith
      · simp [hfalse]
    · linarith

/-- Finitely many continuous nonzero scores at zero retain all their signs at
one common positive parameter. -/
private theorem exists_positive_preserving_cube_signs
    (g : ℝ → (Fin n → Bool) → ℝ)
    (hcontinuous : ∀ y, ContinuousAt (fun epsilon ↦ g epsilon y) 0)
    (hne : ∀ y, g 0 y ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ y, (0 < g epsilon y ↔ 0 < g 0 y) := by
  classical
  have hone : ∀ y, ∀ᶠ epsilon in nhds (0 : ℝ),
      (0 < g epsilon y ↔ 0 < g 0 y) := by
    intro y
    rcases lt_or_gt_of_ne (hne y) with hneg | hpos
    · filter_upwards [hcontinuous y (Iio_mem_nhds hneg)] with epsilon hepsilon
      change g epsilon y < 0 at hepsilon
      constructor <;> intro h <;> linarith
    · filter_upwards [hcontinuous y (Ioi_mem_nhds hpos)] with epsilon hepsilon
      change 0 < g epsilon y at hepsilon
      constructor <;> intro _
      · exact hpos
      · exact hepsilon
  have hall : ∀ᶠ epsilon in nhds (0 : ℝ),
      ∀ y, (0 < g epsilon y ↔ 0 < g 0 y) :=
    Filter.eventually_all.mpr hone
  change {epsilon : ℝ | ∀ y, (0 < g epsilon y ↔ 0 < g 0 y)} ∈ nhds 0 at hall
  rcases Metric.mem_nhds_iff.mp hall with ⟨radius, hradius, hball⟩
  refine ⟨radius / 2, by linarith, ?_⟩
  exact hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_pos (by linarith : 0 < radius / 2)]
    linarith)

/-- Adding any number of dummy coordinates along an arbitrary coordinate
embedding preserves representability with the same number of atoms. -/
theorem fracComputable.liftDummyAlong (e : Fin m ↪ Fin n)
    {f : (Fin m → Bool) → Bool} (hf : fracComputable m H f) :
    fracComputable n H (fun y ↦ f (pullBitsAlong e y)) := by
  classical
  obtain ⟨phi, c, hsign⟩ := hf.strictCertificate
  let scoreAt : ℝ → (Fin n → Bool) → ℝ := fun epsilon y ↦
    c + ∑ h, FracAtom.dummyEvalAt (phi h) e epsilon y
  have hcontinuous : ∀ y,
      ContinuousAt (fun epsilon ↦ scoreAt epsilon y) 0 := by
    intro y
    dsimp [scoreAt]
    apply continuousAt_const.add
    have hsum : ∀ s : Finset (Fin H),
        ContinuousAt
          (fun epsilon ↦ ∑ h ∈ s,
            FracAtom.dummyEvalAt (phi h) e epsilon y) 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using
          (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0)
      | @insert a s ha ih =>
          rw [show (fun epsilon ↦ ∑ h ∈ insert a s,
              FracAtom.dummyEvalAt (phi h) e epsilon y) =
              (fun epsilon ↦ FracAtom.dummyEvalAt (phi a) e epsilon y +
                ∑ h ∈ s, FracAtom.dummyEvalAt (phi h) e epsilon y) by
            funext epsilon
            rw [Finset.sum_insert ha]]
          exact (FracAtom.continuousAt_dummyEvalAt (phi a) e y).add ih
    exact hsum Finset.univ
  have hzero (y : Fin n → Bool) :
      scoreAt 0 y = c + ∑ h, (phi h).eval (pullBitsAlong e y) := by
    simp [scoreAt]
  have hne : ∀ y, scoreAt 0 y ≠ 0 := by
    intro y
    rw [hzero]
    exact (hsign (pullBitsAlong e y)).2
  obtain ⟨epsilon, hepsilon, hpreserve⟩ :=
    exists_positive_preserving_cube_signs scoreAt hcontinuous hne
  refine ⟨fun h ↦ (phi h).liftDummy e epsilon hepsilon, c, fun y ↦ ?_⟩
  simp_rw [FracAtom.liftDummy_eval]
  change 0 < scoreAt epsilon y ↔ f (pullBitsAlong e y) = true
  rw [hpreserve y, hzero]
  exact (hsign (pullBitsAlong e y)).1

/-- Adding dummy coordinates preserves computability with a fixed number of
attention heads. -/
theorem computableWithHeadsN.liftDummyAlong (e : Fin m ↪ Fin n)
    {f : (Fin m → Bool) → Bool} (hf : computableWithHeadsN m H f) :
    computableWithHeadsN n H (fun y ↦ f (pullBitsAlong e y)) :=
  computable_of_fracComputable
    (fracComputable.liftDummyAlong e (fracComputable_of_computable hf))

end HeadComplexity
