import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Atoms.FracComputableMonotone
import HeadComplexity.Results.LowComplexity
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.header false

/-!
# Multiway sign-tensor rank

This module records the multiway analogue of the tangent matrix bound.  A
CP decomposition is kept elementary: it is a finite sum of products of
one-mode functions.  The active terms in a tangent expansion are indexed by
a block assignment together with a block hit by that assignment.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H k : ℕ}
variable {X : Fin k → Type*}

/-- An order-`k` tensor whose `j`th mode has index type `X j`. -/
abbrev MultiwayTensor (X : Fin k → Type*) := (∀ j, X j) → ℝ

/-- A tensor is a sum of at most `r` pure tensors. -/
def CPRankLE (T : MultiwayTensor X) (r : ℕ) : Prop :=
  ∃ (coefficient : Fin r → ℝ)
    (factor : Fin r → ∀ j, X j → ℝ),
    ∀ x, T x = ∑ q, coefficient q * ∏ j, factor q j (x j)

/-- Strict sign realization of a Boolean multiway tensor. -/
def StrictSignTensor (T : MultiwayTensor X) (f : (∀ j, X j) → Bool) : Prop :=
  ∀ x, if f x then 0 < T x else T x < 0

/-- Sign CP rank is the least length of a strict CP realization. -/
noncomputable def signCPRank (f : (∀ j, X j) → Bool) : ℕ :=
  sInf {r | ∃ T : MultiwayTensor X, StrictSignTensor T f ∧ CPRankLE T r}

/-- Any displayed strict CP realization upper-bounds sign CP rank. -/
theorem signCPRank_le_of_strict
    {f : (∀ j, X j) → Bool} {T : MultiwayTensor X} {r : ℕ}
    (hstrict : StrictSignTensor T f) (hrank : CPRankLE T r) :
    signCPRank f ≤ r := by
  exact Nat.sInf_le ⟨T, hstrict, hrank⟩

/-- Assignments of the `H` factors to the `k` coordinate blocks. -/
abbrev BlockAssignment (H k : ℕ) := Fin H → Fin k

/-- An active tangent term is an assignment and a block occurring in its
image. -/
def ActiveTangentTerm (H k : ℕ) :=
  {p : BlockAssignment H k × Fin k // ∃ h, p.1 h = p.2}

noncomputable instance : Fintype (ActiveTangentTerm H k) := by
  classical
  unfold ActiveTangentTerm
  infer_instance

/-- Reindex active pairs by their active block. -/
def activeTangentTermEquivSigma :
    ActiveTangentTerm H k ≃
      Σ j : Fin k, { τ : BlockAssignment H k // ∃ h, τ h = j } where
  toFun q := ⟨q.1.2, q.1.1, q.2⟩
  invFun q := ⟨(q.2.1, q.1), q.2.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q with | mk j q => cases q; rfl

/-- Assignments avoiding `j` are functions into the other `k - 1`
blocks. -/
def avoidsBlockEquiv (j : Fin k) :
    { τ : BlockAssignment H k // ∀ h, τ h ≠ j } ≃
      (Fin H → { ℓ : Fin k // ℓ ≠ j }) where
  toFun τ h := ⟨τ.1 h, τ.2 h⟩
  invFun τ := ⟨fun h ↦ (τ h).1, fun h ↦ (τ h).2⟩
  left_inv τ := by ext h; rfl
  right_inv τ := by funext h; exact Subtype.ext rfl

private theorem card_blocks_ne (j : Fin k) :
    Fintype.card { ℓ : Fin k // ℓ ≠ j } = k - 1 := by
  rw [Fintype.card_subtype_compl (fun ℓ : Fin k ↦ ℓ = j)]
  simp

private theorem card_assignments_using (j : Fin k) :
    Fintype.card { τ : BlockAssignment H k // ∃ h, τ h = j } =
      k ^ H - (k - 1) ^ H := by
  classical
  let e : { τ : BlockAssignment H k // ∃ h, τ h = j } ≃
      { τ : BlockAssignment H k // ¬ ∀ h, τ h ≠ j } :=
    Equiv.subtypeEquivRight fun τ ↦ by simp
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl
    (fun τ : BlockAssignment H k ↦ ∀ h, τ h ≠ j)]
  rw [Fintype.card_congr (avoidsBlockEquiv (H := H) j)]
  simp

/-- Double counting active assignment-block pairs gives exactly the bound in
the multiway theorem. -/
theorem card_activeTangentTerm :
    Fintype.card (ActiveTangentTerm H k) =
      k * (k ^ H - (k - 1) ^ H) := by
  classical
  rw [Fintype.card_congr (activeTangentTermEquivSigma (H := H) (k := k))]
  rw [Fintype.card_sigma]
  simp [card_assignments_using]

/-- The factors assigned by `τ` to block `j`. -/
def assignmentFiber (τ : BlockAssignment H k) (j : Fin k) : Finset (Fin H) :=
  Finset.univ.filter fun h ↦ τ h = j

/-- The block-local tangent factor associated with one assignment. -/
def localTangentFactor
    (a b : Fin H → ∀ j, X j → ℝ)
    (τ : BlockAssignment H k) (j : Fin k) (x : X j) : ℝ :=
  ∑ h ∈ assignmentFiber τ j,
    a h j x * ∏ g ∈ (assignmentFiber τ j).erase h, b g j x

/-- One-mode factor in the pure tensor indexed by `(τ,j)`. -/
def activeTangentFactor
    (a b : Fin H → ∀ j, X j → ℝ)
    (q : ActiveTangentTerm H k) (j : Fin k) (x : X j) : ℝ :=
  if hj : j = q.1.2 then
    localTangentFactor a b q.1.1 q.1.2 (hj ▸ x)
  else
    ∏ g ∈ assignmentFiber q.1.1 j, b g j x

/-- The pure tensor attached to an assignment-block pair.  It is zero when
the displayed block is not hit by the assignment. -/
def assignmentBlockPureTensor
    (a b : Fin H → ∀ j, X j → ℝ)
    (τ : BlockAssignment H k) (j : Fin k) (x : ∀ j, X j) : ℝ :=
  ∏ ℓ, if hℓ : ℓ = j then
      localTangentFactor a b τ j (hℓ ▸ x ℓ)
    else
      ∏ g ∈ assignmentFiber τ ℓ, b g ℓ (x ℓ)

/-- The pure tensor attached to an active assignment-block pair. -/
def activeTangentPureTensor
    (a b : Fin H → ∀ j, X j → ℝ)
    (q : ActiveTangentTerm H k) (x : ∀ j, X j) : ℝ :=
  assignmentBlockPureTensor a b q.1.1 q.1.2 x

theorem activeTangentPureTensor_eq_prod_factors
    (a b : Fin H → ∀ j, X j → ℝ)
    (q : ActiveTangentTerm H k) (x : ∀ j, X j) :
    activeTangentPureTensor a b q x =
      ∏ j, activeTangentFactor a b q j (x j) := by
  rfl

/-- The tangent expression obtained by replacing every affine factor by its
sum of block-local parts. -/
def multiwayTangentValue
    (a b : Fin H → ∀ j, X j → ℝ) (x : ∀ j, X j) : ℝ :=
  ∑ h, (∑ j, a h j (x j)) *
    ∏ g ∈ Finset.univ.erase h, ∑ j, b g j (x j)

private theorem prod_block_fibers_erase
    (b : Fin H → Fin k → ℝ) (τ : BlockAssignment H k)
    (h : Fin H) (j : Fin k) (hhj : τ h = j) :
    (∏ g ∈ (assignmentFiber τ j).erase h, b g j) *
        ∏ ℓ ∈ Finset.univ.erase j,
          ∏ g ∈ assignmentFiber τ ℓ, b g ℓ =
      ∏ g ∈ Finset.univ.erase h, b g (τ g) := by
  classical
  rw [← Finset.prod_fiberwise (s := Finset.univ.erase h) τ
    (fun g ↦ b g (τ g))]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun ℓ ↦ ∏ g ∈ Finset.univ.erase h with τ g = ℓ, b g (τ g))
    (Finset.mem_univ j)]
  congr 1
  · apply Finset.prod_congr
    · ext g
      simp [assignmentFiber]
    · intro g hg
      have hgτ : τ g = j := by
        exact (Finset.mem_filter.mp hg).2
      simp [hgτ]
  · apply Finset.prod_congr rfl
    intro ℓ hℓ
    apply Finset.prod_congr
    · ext g
      simp [assignmentFiber]
      aesop
    · intro g hg
      have hgτ : τ g = ℓ := by
        exact (Finset.mem_filter.mp hg).2
      simp [hgτ]

private theorem prod_sum_except_eq_assignment_sum
    (b : Fin H → Fin k → ℝ) (h : Fin H) (j : Fin k) :
    ∏ g ∈ Finset.univ.erase h, ∑ ℓ, b g ℓ =
      ∑ τ : BlockAssignment H k,
        if τ h = j then ∏ g ∈ Finset.univ.erase h, b g (τ g) else 0 := by
  classical
  let F : Fin H → Fin k → ℝ := fun g ℓ ↦
    if g = h then (if ℓ = j then 1 else 0) else b g ℓ
  have hexpand := Fintype.prod_sum F
  have hleft : (∏ g, ∑ ℓ, F g ℓ) =
      ∏ g ∈ Finset.univ.erase h, ∑ ℓ, b g ℓ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun g ↦ ∑ ℓ, F g ℓ)
      (Finset.mem_univ h)]
    simp only [F, if_pos, Finset.sum_ite_eq', Finset.mem_univ, one_mul]
    apply Finset.prod_congr rfl
    intro g hg
    simp [Finset.ne_of_mem_erase hg]
  rw [hleft] at hexpand
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro τ _
  by_cases hτ : τ h = j
  · simp only [hτ, if_pos]
    rw [← Finset.mul_prod_erase Finset.univ (fun g ↦ F g (τ g))
      (Finset.mem_univ h)]
    simp only [F, if_pos, hτ, one_mul]
    apply Finset.prod_congr rfl
    intro g hg
    simp [Finset.ne_of_mem_erase hg]
  · simp only [hτ]
    apply Finset.prod_eq_zero (Finset.mem_univ h)
    simp [F, hτ]

private theorem assignmentBlockPureTensor_eq
    (a b : Fin H → ∀ j, X j → ℝ)
    (τ : BlockAssignment H k) (j : Fin k) (x : ∀ j, X j) :
    assignmentBlockPureTensor a b τ j x =
      ∑ h ∈ assignmentFiber τ j,
        a h j (x j) *
          ∏ g ∈ Finset.univ.erase h,
            b g (τ g) (x (τ g)) := by
  classical
  unfold assignmentBlockPureTensor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun ℓ ↦ if hℓ : ℓ = j then
      localTangentFactor a b τ j (hℓ ▸ x ℓ)
    else ∏ g ∈ assignmentFiber τ ℓ, b g ℓ (x ℓ))
    (Finset.mem_univ j)]
  simp only [dif_pos]
  have hrest :
      (∏ ℓ ∈ Finset.univ.erase j,
        if hℓ : ℓ = j then
          localTangentFactor a b τ j (hℓ ▸ x ℓ)
        else ∏ g ∈ assignmentFiber τ ℓ, b g ℓ (x ℓ)) =
      ∏ ℓ ∈ Finset.univ.erase j,
        ∏ g ∈ assignmentFiber τ ℓ, b g ℓ (x ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    simp [Finset.ne_of_mem_erase hℓ]
  rw [hrest]
  unfold localTangentFactor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  have hhj : τ h = j := by
    simpa [assignmentFiber] using hh
  have hprod := prod_block_fibers_erase (H := H) (k := k)
    (b := fun g ℓ ↦ b g ℓ (x ℓ)) τ h j hhj
  calc
    (a h j (x j) *
        ∏ g ∈ (assignmentFiber τ j).erase h,
          b g j (x j)) *
        ∏ ℓ ∈ Finset.univ.erase j,
          ∏ g ∈ assignmentFiber τ ℓ, b g ℓ (x ℓ) =
      a h j (x j) *
        ((∏ g ∈ (assignmentFiber τ j).erase h,
            b g j (x j)) *
          ∏ ℓ ∈ Finset.univ.erase j,
            ∏ g ∈ assignmentFiber τ ℓ, b g ℓ (x ℓ)) := by ring
    _ = a h j (x j) *
        ∏ g ∈ Finset.univ.erase h,
          b g (τ g) (x (τ g)) := by rw [hprod]

private theorem sum_comm_three {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (F : A → B → C → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ b, ∑ a, F a b c := by
  calc
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

/-- The multiway tangent expression is the sum of the assignment-block pure
tensors. -/
theorem multiwayTangentValue_eq_sum_assignmentBlocks
    (a b : Fin H → ∀ j, X j → ℝ) (x : ∀ j, X j) :
    multiwayTangentValue a b x =
      ∑ τ : BlockAssignment H k, ∑ j,
        assignmentBlockPureTensor a b τ j x := by
  classical
  unfold multiwayTangentValue
  simp_rw [Finset.sum_mul]
  calc
    (∑ h, ∑ j, a h j (x j) *
        ∏ g ∈ Finset.univ.erase h, ∑ j, b g j (x j)) =
      ∑ h, ∑ j, ∑ τ : BlockAssignment H k,
        a h j (x j) *
          (if τ h = j then
            ∏ g ∈ Finset.univ.erase h, b g (τ g) (x (τ g)) else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro j _
      rw [prod_sum_except_eq_assignment_sum
        (b := fun g j ↦ b g j (x j)) h j, Finset.mul_sum]
    _ = ∑ τ : BlockAssignment H k, ∑ j,
        assignmentBlockPureTensor a b τ j x := by
      let F : Fin H → Fin k → BlockAssignment H k → ℝ :=
        fun h j τ ↦ if τ h = j then
          a h j (x j) * ∏ g ∈ Finset.univ.erase h,
            b g (τ g) (x (τ g)) else 0
      have hleft :
          (∑ (h : Fin H), ∑ (j : Fin k), ∑ (τ : BlockAssignment H k), a h j (x j) *
            (if τ h = j then
              ∏ g ∈ Finset.univ.erase h, b g (τ g) (x (τ g)) else 0)) =
          ∑ (h : Fin H), ∑ (j : Fin k), ∑ (τ : BlockAssignment H k), F h j τ := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro τ _
        by_cases hh : τ h = j <;> simp [F, hh]
      have hright :
          (∑ (τ : BlockAssignment H k), ∑ (j : Fin k),
            assignmentBlockPureTensor a b τ j x) =
          ∑ (τ : BlockAssignment H k), ∑ (j : Fin k), ∑ (h : Fin H), F h j τ := by
        apply Finset.sum_congr rfl
        intro τ _
        apply Finset.sum_congr rfl
        intro j _
        rw [assignmentBlockPureTensor_eq]
        simp [F, assignmentFiber, Finset.sum_filter]
      rw [hleft, sum_comm_three F, ← hright]

/-- Inactive assignment-block pairs contribute zero. -/
theorem assignmentBlockPureTensor_eq_zero_of_inactive
    (a b : Fin H → ∀ j, X j → ℝ)
    (τ : BlockAssignment H k) (j : Fin k)
    (hinactive : ¬ ∃ h, τ h = j) (x : ∀ j, X j) :
    assignmentBlockPureTensor a b τ j x = 0 := by
  rw [assignmentBlockPureTensor_eq]
  apply Finset.sum_eq_zero
  intro h hh
  exact (hinactive ⟨h, (Finset.mem_filter.mp hh).2⟩).elim

/-- Equivalently, only active assignment-block pairs are needed. -/
theorem multiwayTangentValue_eq_sum_active
    (a b : Fin H → ∀ j, X j → ℝ) (x : ∀ j, X j) :
    multiwayTangentValue a b x =
      ∑ q : ActiveTangentTerm H k, activeTangentPureTensor a b q x := by
  classical
  rw [multiwayTangentValue_eq_sum_assignmentBlocks]
  rw [← Fintype.sum_prod_type
    (fun p : BlockAssignment H k × Fin k ↦
      assignmentBlockPureTensor a b p.1 p.2 x)]
  change (∑ p : BlockAssignment H k × Fin k,
      assignmentBlockPureTensor a b p.1 p.2 x) =
    ∑ q : {p : BlockAssignment H k × Fin k // ∃ h, p.1 h = p.2},
      assignmentBlockPureTensor a b q.1.1 q.1.2 x
  rw [← Finset.sum_subtype
    (s := Finset.univ.filter (fun p : BlockAssignment H k × Fin k ↦
      ∃ h, p.1 h = p.2))
    (fun p ↦ by simp)
    (fun p ↦ assignmentBlockPureTensor a b p.1 p.2 x)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ∃ h, p.1 h = p.2
  · simp only [hp, if_pos]
  · simp only [hp]
    exact assignmentBlockPureTensor_eq_zero_of_inactive a b p.1 p.2 hp x

/-- The active tangent expansion gives a CP decomposition with one summand
per active assignment-block pair. -/
theorem multiwayTangentValue_cpRankLE_card_active
    (a b : Fin H → ∀ j, X j → ℝ) :
    CPRankLE (multiwayTangentValue a b)
      (Fintype.card (ActiveTangentTerm H k)) := by
  classical
  let e := Fintype.equivFin (ActiveTangentTerm H k)
  refine ⟨fun _ ↦ 1, fun q ↦ activeTangentFactor a b (e.symm q), ?_⟩
  intro x
  rw [multiwayTangentValue_eq_sum_active]
  have hsum := Fintype.sum_equiv e
    (fun q ↦ activeTangentPureTensor a b q x)
    (fun q ↦ activeTangentPureTensor a b (e.symm q) x)
    (fun q ↦ by simp)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro q _
  rw [activeTangentPureTensor_eq_prod_factors]
  simp

/-- Closed-form multiway tangent CP-rank cap. -/
theorem multiwayTangentValue_cpRankLE
    (a b : Fin H → ∀ j, X j → ℝ) :
    CPRankLE (multiwayTangentValue a b)
      (k * (k ^ H - (k - 1) ^ H)) := by
  simpa [card_activeTangentTerm] using
    multiwayTangentValue_cpRankLE_card_active a b

/-- Input to every mode except `j₀`. -/
abbrev OtherModeInput (X : Fin k → Type*) (j₀ : Fin k) :=
  ∀ j : {j : Fin k // j ≠ j₀}, X j.1

/-- Insert the distinguished-mode value into an input of all other modes. -/
def insertMode (j₀ : Fin k) (q : OtherModeInput X j₀)
    (z : X j₀) : ∀ j, X j :=
  fun j ↦ if h : j = j₀ then h.symm ▸ z else q ⟨j, h⟩

/-- Restrict a full tensor input to every mode except `j₀`. -/
def removeMode (j₀ : Fin k) (x : ∀ j, X j) : OtherModeInput X j₀ :=
  fun j ↦ x j.1

theorem insertMode_removeMode (j₀ : Fin k) (x : ∀ j, X j) :
    insertMode j₀ (removeMode j₀ x) (x j₀) = x := by
  funext j
  by_cases h : j = j₀
  · subst j
    simp [insertMode]
  · simp [insertMode, removeMode, h]

/-- Pure factor used by the standard fiber expansion along `j₀`. -/
noncomputable def ambientCPFactor (T : MultiwayTensor X) (j₀ : Fin k)
    (q : OtherModeInput X j₀) (j : Fin k) (z : X j) : ℝ := by
  classical
  exact if h : j = j₀ then T (insertMode j₀ q (h ▸ z))
    else if z = q ⟨j, h⟩ then 1 else 0

private theorem ambient_sum_pure (T : MultiwayTensor X) (j₀ : Fin k)
    [∀ j, Fintype (X j)] (x : ∀ j, X j) :
    T x = ∑ q : OtherModeInput X j₀,
      ∏ j, ambientCPFactor T j₀ q j (x j) := by
  classical
  symm
  have hsum : (∑ q : OtherModeInput X j₀,
      ∏ j, ambientCPFactor T j₀ q j (x j)) =
      ∏ j, ambientCPFactor T j₀ (removeMode j₀ x) j (x j) := by
    apply Finset.sum_eq_single (removeMode j₀ x)
    · intro q _ hq
      have hne : ∃ j : {j : Fin k // j ≠ j₀}, q j ≠ x j.1 := by
        by_contra hall
        push Not at hall
        apply hq
        funext j
        exact hall j
      obtain ⟨j, hj⟩ := hne
      apply Finset.prod_eq_zero (Finset.mem_univ j.1)
      simp only [ambientCPFactor, dif_neg j.2]
      apply if_neg
      intro heq
      exact hj heq.symm
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  rw [hsum]
  rw [show (∏ j, ambientCPFactor T j₀ (removeMode j₀ x) j (x j)) =
        ambientCPFactor T j₀ (removeMode j₀ x) j₀ (x j₀) *
          ∏ j ∈ Finset.univ.erase j₀,
            ambientCPFactor T j₀ (removeMode j₀ x) j (x j) by
      exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)).symm]
  have hrest : (∏ j ∈ Finset.univ.erase j₀,
      ambientCPFactor T j₀ (removeMode j₀ x) j (x j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [ambientCPFactor, removeMode, Finset.ne_of_mem_erase hj]
  rw [hrest, mul_one]
  simp [ambientCPFactor, insertMode_removeMode]

/-- Every finite tensor has CP rank at most the number of index tuples in all
modes except one. -/
theorem cpRankLE_card_otherModes (T : MultiwayTensor X) (j₀ : Fin k)
    [∀ j, Fintype (X j)] :
    CPRankLE T (Fintype.card (OtherModeInput X j₀)) := by
  classical
  let e := Fintype.equivFin (OtherModeInput X j₀)
  refine ⟨fun _ ↦ 1, fun q ↦ ambientCPFactor T j₀ (e.symm q), ?_⟩
  intro x
  rw [ambient_sum_pure T j₀ x]
  have hsum := Fintype.sum_equiv e
    (fun q ↦ ∏ j, ambientCPFactor T j₀ q j (x j))
    (fun q ↦ ∏ j, ambientCPFactor T j₀ (e.symm q) j (x j))
    (fun q ↦ by simp)
  rw [hsum]
  simp

/-- Canonical strict `±1` realization of a Boolean tensor. -/
noncomputable def booleanSignTensor (f : (∀ j, X j) → Bool) :
    MultiwayTensor X :=
  fun x ↦ if f x then 1 else -1

theorem booleanSignTensor_strict (f : (∀ j, X j) → Bool) :
    StrictSignTensor (booleanSignTensor f) f := by
  intro x
  cases h : f x <;> simp [booleanSignTensor, h]

/-- Ambient sign-CP-rank ceiling obtained by expanding in basis tensors along
every mode except one. -/
theorem signCPRank_le_card_otherModes [∀ j, Fintype (X j)]
    (f : (∀ j, X j) → Bool) (j₀ : Fin k) :
    signCPRank f ≤ Fintype.card (OtherModeInput X j₀) :=
  signCPRank_le_of_strict (booleanSignTensor_strict f)
    (cpRankLE_card_otherModes (booleanSignTensor f) j₀)

/-- For nonzero tensor order, the least sign CP-rank bound is attained. -/
theorem signCPRank_spec [∀ j, Fintype (X j)]
    (f : (∀ j, X j) → Bool) (j₀ : Fin k) :
    ∃ T : MultiwayTensor X,
      StrictSignTensor T f ∧ CPRankLE T (signCPRank f) := by
  change signCPRank f ∈
    {r | ∃ T : MultiwayTensor X, StrictSignTensor T f ∧ CPRankLE T r}
  unfold signCPRank
  apply Nat.sInf_mem
  exact ⟨Fintype.card (OtherModeInput X j₀), booleanSignTensor f,
    booleanSignTensor_strict f,
    cpRankLE_card_otherModes (booleanSignTensor f) j₀⟩

section CoordinatePartition

variable {I : Fin k → Type*} [∀ j, Fintype (I j)]

noncomputable local instance modeInputFintype (j : Fin k) :
    Fintype (I j → Bool) := by
  classical
  exact Pi.instFintype

/-- Merge the inputs of all coordinate blocks into one Boolean assignment. -/
def mergeMultiwayBits (part : Fin n ≃ Σ j, I j)
    (x : ∀ j, I j → Bool) (i : Fin n) : Bool :=
  x (part i).1 (part i).2

/-- Boolean tensor induced by a coordinate partition. -/
def multiwayPartitionFunction (part : Fin n ≃ Σ j, I j)
    (f : (Fin n → Bool) → Bool) : (∀ j, (I j → Bool)) → Bool :=
  fun x ↦ f (mergeMultiwayBits part x)

/-- The part of an affine polynomial living on block `j`; its constant is
assigned to the distinguished block `j₀`. -/
noncomputable def affineBlockPart (part : Fin n ≃ Σ j, I j)
    (j₀ : Fin k) (P : MvPolynomial (Fin n) ℝ)
    (j : Fin k) (x : I j → Bool) : ℝ :=
  (if j = j₀ then P.coeff 0 else 0) +
    ∑ i, P.coeff (Finsupp.single (part.symm ⟨j, i⟩) 1) *
      boolToReal (x i)

/-- Every affine polynomial is the sum of its block-local parts. -/
theorem eval_mergeMultiwayBits_eq_affineBlockParts
    (part : Fin n ≃ Σ j, I j) (j₀ : Fin k)
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1)
    (x : ∀ j, I j → Bool) :
    MvPolynomial.eval (cubePoint (mergeMultiwayBits part x)) P =
      ∑ j, affineBlockPart part j₀ P j (x j) := by
  classical
  rw [eval_cubePoint_affine P hP]
  unfold affineBlockPart
  rw [Finset.sum_add_distrib]
  have hconstant : (∑ j : Fin k, if j = j₀ then P.coeff 0 else 0) =
      P.coeff 0 := by simp
  rw [hconstant]
  congr 1
  have hsum := Fintype.sum_equiv part
    (fun i : Fin n ↦ P.coeff (Finsupp.single i 1) *
      boolToReal (mergeMultiwayBits part x i))
    (fun p : Σ j, I j ↦ P.coeff (Finsupp.single (part.symm p) 1) *
      boolToReal (x p.1 p.2))
    (fun i ↦ by simp [mergeMultiwayBits])
  rw [hsum, Fintype.sum_sigma]

/-- Evaluation tensor of the denominator-cleared affine score. -/
noncomputable def clearedAffineMultiwayTensor
    (part : Fin n ≃ Σ j, I j) (A : AffineFractionFamily n H) (c : ℝ) :
    MultiwayTensor (fun j ↦ I j → Bool) :=
  fun x ↦ MvPolynomial.eval (cubePoint (mergeMultiwayBits part x))
    (clearedAffinePoly A c)

/-- After bias absorption, the cleared evaluation tensor is precisely the
abstract multiway tangent expression. -/
theorem clearedAffineMultiwayTensor_eq_tangent
    (part : Fin n ≃ Σ j, I j) (A : AffineFractionFamily n H) (c : ℝ)
    (h₀ : Fin H) (j₀ : Fin k) :
    clearedAffineMultiwayTensor part A c =
      multiwayTangentValue
        (fun h j ↦ affineBlockPart part j₀ (A.absorbBias c h₀ h) j)
        (fun h j ↦ affineBlockPart part j₀ (A.den h) j) := by
  funext x
  unfold clearedAffineMultiwayTensor
  rw [clearedAffinePoly_eq_sum_absorbBias A c h₀]
  simp only [map_sum, map_mul, map_prod]
  simp_rw [eval_mergeMultiwayBits_eq_affineBlockParts part j₀
    (A.absorbBias c h₀ _) (A.absorbBias_degree c h₀ _)]
  simp_rw [eval_mergeMultiwayBits_eq_affineBlockParts part j₀
    (A.den _) (A.den_degree _)]
  rfl

/-- Sign CP rank of the Boolean tensor induced by a coordinate partition. -/
noncomputable def multiwaySignCPRank (part : Fin n ≃ Σ j, I j)
    (f : (Fin n → Bool) → Bool) : ℕ :=
  signCPRank (multiwayPartitionFunction part f)

/-- Cardinality of the other-mode Boolean index tuples. -/
theorem card_otherModeBooleanInputs (j₀ : Fin k) :
    Fintype.card (OtherModeInput (fun j ↦ I j → Bool) j₀) =
      ∏ j : {j : Fin k // j ≠ j₀}, 2 ^ Fintype.card (I j.1) := by
  classical
  change Fintype.card
      ((j : {j : Fin k // j ≠ j₀}) → (I j.1 → Bool)) = _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro j _
  simp

/-- Ambient CP-rank ceiling for an induced Boolean tensor, displayed with a
chosen omitted mode. -/
theorem multiwaySignCPRank_le_otherModeProduct
    (part : Fin n ≃ Σ j, I j) (f : (Fin n → Bool) → Bool)
    (j₀ : Fin k) :
    multiwaySignCPRank part f ≤
      ∏ j : {j : Fin k // j ≠ j₀}, 2 ^ Fintype.card (I j.1) := by
  classical
  unfold multiwaySignCPRank
  rw [← card_otherModeBooleanInputs (I := I) j₀]
  exact signCPRank_le_card_otherModes (X := fun j ↦ I j → Bool) _ j₀

/-- Numerical form of the ambient ceiling: omitting block `j₀` leaves
`n - |I_{j₀}|` Boolean coordinates. -/
theorem multiwaySignCPRank_le_two_pow_complement
    (part : Fin n ≃ Σ j, I j) (f : (Fin n → Bool) → Bool)
    (j₀ : Fin k) :
    multiwaySignCPRank part f ≤ 2 ^ (n - Fintype.card (I j₀)) := by
  classical
  have hcard : n = ∑ j : Fin k, Fintype.card (I j) := by
    calc
      n = Fintype.card (Fin n) := by simp
      _ = Fintype.card (Σ j, I j) := Fintype.card_congr part
      _ = ∑ j : Fin k, Fintype.card (I j) := Fintype.card_sigma
  have hsum :
      (∑ j ∈ Finset.univ.erase j₀, Fintype.card (I j)) =
        n - Fintype.card (I j₀) := by
    have hs := Finset.sum_erase_add Finset.univ
      (fun j : Fin k ↦ Fintype.card (I j)) (Finset.mem_univ j₀)
    omega
  have hprod :
      (∏ j : {j : Fin k // j ≠ j₀}, 2 ^ Fintype.card (I j.1)) =
        ∏ j ∈ Finset.univ.erase j₀, 2 ^ Fintype.card (I j) := by
    symm
    apply Finset.prod_subtype
    intro j
    simp
  calc
    multiwaySignCPRank part f ≤
        ∏ j : {j : Fin k // j ≠ j₀}, 2 ^ Fintype.card (I j.1) :=
      multiwaySignCPRank_le_otherModeProduct part f j₀
    _ = ∏ j ∈ Finset.univ.erase j₀, 2 ^ Fintype.card (I j) := hprod
    _ = 2 ^ (∑ j ∈ Finset.univ.erase j₀, Fintype.card (I j)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = 2 ^ (n - Fintype.card (I j₀)) := by rw [hsum]

omit [∀ j, Fintype (I j)] in
/-- A strict shifted atom score gives a strict realization of the induced
multiway sign tensor after clearing its positive denominators. -/
theorem clearedAtomMultiwayTensor_strict
    (part : Fin n ≃ Σ j, I j) (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (c : ℝ)
    (hscore : ∀ x : Fin n → Bool,
      if f x then 0 < c + ∑ h, (phi h).eval x
      else c + ∑ h, (phi h).eval x < 0) :
    StrictSignTensor
      (clearedAffineMultiwayTensor part (FracAtom.affineFamily phi) c)
      (multiwayPartitionFunction part f) := by
  intro x
  let y := mergeMultiwayBits part x
  change if f y then
      0 < MvPolynomial.eval (cubePoint y) (clearedAtomPoly phi c)
    else MvPolynomial.eval (cubePoint y) (clearedAtomPoly phi c) < 0
  rw [clearedAtomPoly_eval]
  cases hfy : f y with
  | false =>
      have hs := hscore y
      rw [hfy] at hs
      exact mul_neg_of_pos_of_neg (atomDenProduct_eval_pos phi y) hs
  | true =>
      have hs := hscore y
      rw [hfy] at hs
      exact mul_pos (atomDenProduct_eval_pos phi y) hs

/-- Every `H`-head computation satisfies the multiway tangent CP-rank cap
for every partition into at least two blocks. -/
theorem multiwaySignCPRank_le_of_computableWithHeadsN
    (hH : 0 < H) (hk : 2 ≤ k) (part : Fin n ≃ Σ j, I j)
    (f : (Fin n → Bool) → Bool) (hf : computableWithHeadsN n H f) :
    multiwaySignCPRank part f ≤ k * (k ^ H - (k - 1) ^ H) := by
  classical
  obtain ⟨phi, c, hscore⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hf)
  let A := FracAtom.affineFamily phi
  let h₀ : Fin H := ⟨0, hH⟩
  let j₀ : Fin k := ⟨0, by omega⟩
  have hstrict := clearedAtomMultiwayTensor_strict part f phi c hscore
  change signCPRank (multiwayPartitionFunction part f) ≤
    k * (k ^ H - (k - 1) ^ H)
  refine signCPRank_le_of_strict hstrict ?_
  rw [clearedAffineMultiwayTensor_eq_tangent part A c h₀ j₀]
  exact multiwayTangentValue_cpRankLE _ _

/-- **Theorem 192, multiway sign-tensor rank bound.** If a nonconstant
Boolean function has head complexity at most `H`, every partition into
`k ≥ 2` blocks has sign CP rank at most
`k * (k^H - (k-1)^H)`. -/
theorem multiwaySignCPRank_le_of_HStar_le
    (hk : 2 ≤ k) (part : Fin n ≃ Σ j, I j)
    (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) (hle : HStar n f ≤ H) :
    multiwaySignCPRank part f ≤ k * (k ^ H - (k - 1) ^ H) := by
  have hHstar : 0 < HStar n f := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnonconstant ((HStar_eq_zero_iff f).mp hzero)
  have hH : 0 < H := hHstar.trans_le hle
  exact multiwaySignCPRank_le_of_computableWithHeadsN hH hk part f
    (computableWithHeadsN_mono hle (HStar_computable f))

/-- At two blocks, the multiway count is the existing tangent matrix count. -/
theorem two_block_tangent_count (H : ℕ) :
    2 * (2 ^ H - (2 - 1) ^ H) = 2 ^ (H + 1) - 2 := by
  simp only [Nat.reduceSubDiff, one_pow, pow_succ]
  have hp : 0 < 2 ^ H := pow_pos (by omega) H
  omega

private theorem pow_le_tangent_count {H k : ℕ} (hH : 0 < H) (hk : 0 < k) :
    k ^ H ≤ k * (k ^ H - (k - 1) ^ H) := by
  have hpow : (k - 1) ^ (H - 1) ≤ k ^ (H - 1) :=
    Nat.pow_le_pow_left (Nat.sub_le k 1) _
  have hsum : (k - 1) ^ H + k ^ (H - 1) ≤ k ^ H := by
    calc
      (k - 1) ^ H + k ^ (H - 1) =
          (k - 1) * (k - 1) ^ (H - 1) + k ^ (H - 1) := by
            conv_lhs => lhs; rw [show H = (H - 1) + 1 by omega, pow_succ]
            ring
      _ ≤ (k - 1) * k ^ (H - 1) + k ^ (H - 1) := by gcongr
      _ = k * k ^ (H - 1) := by
        have : k - 1 + 1 = k := by omega
        calc
          (k - 1) * k ^ (H - 1) + k ^ (H - 1) =
              ((k - 1) + 1) * k ^ (H - 1) := by ring
          _ = k * k ^ (H - 1) := by rw [this]
      _ = k ^ H := by
        conv_rhs => rw [show H = (H - 1) + 1 by omega, pow_succ]
        ring
  have hdiff : k ^ (H - 1) ≤ k ^ H - (k - 1) ^ H :=
    Nat.le_sub_of_add_le (by simpa [add_comm] using hsum)
  calc
    k ^ H = k * k ^ (H - 1) := by
      conv_lhs => rw [show H = (H - 1) + 1 by omega, pow_succ]
      ring
    _ ≤ k * (k ^ H - (k - 1) ^ H) := Nat.mul_le_mul_left k hdiff

private theorem four_mul_sixteen_pow_le_twenty_seven_pow {H : ℕ}
    (hH : 3 ≤ H) : 4 * 16 ^ H ≤ 27 ^ H := by
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ H hH ih =>
      calc
        4 * 16 ^ (H + 1) = (4 * 16 ^ H) * 16 := by rw [pow_succ]; ring
        _ ≤ 27 ^ H * 16 := Nat.mul_le_mul_right 16 ih
        _ ≤ 27 ^ H * 27 := Nat.mul_le_mul_left (27 ^ H) (by norm_num)
        _ = 27 ^ (H + 1) := by rw [pow_succ]

private theorem two_pow_le_three_pow_of_three_mul_le {s H : ℕ}
    (hH : 2 ≤ H) (hs : 3 * s ≤ 4 * H + 2) : 2 ^ s ≤ 3 ^ H := by
  by_cases h2 : H = 2
  · subst H
    have hsexp : s ≤ 3 := by omega
    calc
      2 ^ s ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) hsexp
      _ ≤ 3 ^ 2 := by norm_num
  · have hH3 : 3 ≤ H := by omega
    apply (Nat.pow_le_pow_iff_left (by norm_num : 3 ≠ 0)).mp
    calc
      (2 ^ s) ^ 3 = 2 ^ (3 * s) := by rw [mul_comm, pow_mul]
      _ ≤ 2 ^ (4 * H + 2) := Nat.pow_le_pow_right (by omega) hs
      _ = 4 * 16 ^ H := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ 27 ^ H := four_mul_sixteen_pow_le_twenty_seven_pow hH3
      _ = (3 ^ H) ^ 3 := by
        rw [show 27 = 3 ^ 3 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega

/-- **Theorem 192, universal input-count barrier.** If `H ≥ 2` and there
are at most `2H + 1` input coordinates, then the ambient CP-rank ceiling of
every partition into at least two nonempty blocks already lies below the
multiway tangent count. -/
theorem multiwaySignCPRank_le_tangent_count_of_input_bound
    [∀ j, Nonempty (I j)]
    (hH : 2 ≤ H) (hk : 2 ≤ k) (hn : n ≤ 2 * H + 1)
    (part : Fin n ≃ Σ j, I j) (f : (Fin n → Bool) → Bool) :
    multiwaySignCPRank part f ≤ k * (k ^ H - (k - 1) ^ H) := by
  classical
  have hcard : n = ∑ j, Fintype.card (I j) := by
    calc
      n = Fintype.card (Fin n) := by simp
      _ = Fintype.card (Σ j, I j) := Fintype.card_congr part
      _ = ∑ j, Fintype.card (I j) := Fintype.card_sigma
  by_cases hk2 : k = 2
  · subst k
    simp only [Fin.sum_univ_two] at hcard
    by_cases h01 : Fintype.card (I 0) ≤ Fintype.card (I 1)
    · have hsmall : Fintype.card (I 0) ≤ H := by omega
      calc
        multiwaySignCPRank part f ≤ 2 ^ (n - Fintype.card (I 1)) :=
          multiwaySignCPRank_le_two_pow_complement part f 1
        _ = 2 ^ Fintype.card (I 0) := by congr 1; omega
        _ ≤ 2 ^ H := Nat.pow_le_pow_right (by omega) hsmall
        _ ≤ 2 * (2 ^ H - (2 - 1) ^ H) :=
          pow_le_tangent_count (by omega) (by omega)
    · have hsmall : Fintype.card (I 1) ≤ H := by omega
      calc
        multiwaySignCPRank part f ≤ 2 ^ (n - Fintype.card (I 0)) :=
          multiwaySignCPRank_le_two_pow_complement part f 0
        _ = 2 ^ Fintype.card (I 1) := by congr 1; omega
        _ ≤ 2 ^ H := Nat.pow_le_pow_right (by omega) hsmall
        _ ≤ 2 * (2 ^ H - (2 - 1) ^ H) :=
          pow_le_tangent_count (by omega) (by omega)
  · by_cases hk3 : k = 3
    · subst k
      rw [Fin.sum_univ_three] at hcard
      have finish (j : Fin 3)
          (hj : 3 * (n - Fintype.card (I j)) ≤ 4 * H + 2) :
          multiwaySignCPRank part f ≤ 3 * (3 ^ H - (3 - 1) ^ H) := by
        calc
          multiwaySignCPRank part f ≤ 2 ^ (n - Fintype.card (I j)) :=
            multiwaySignCPRank_le_two_pow_complement part f j
          _ ≤ 3 ^ H := two_pow_le_three_pow_of_three_mul_le hH hj
          _ ≤ 3 * (3 ^ H - (3 - 1) ^ H) :=
            pow_le_tangent_count (by omega) (by omega)
      by_cases h01 : Fintype.card (I 0) ≤ Fintype.card (I 1)
      · by_cases h12 : Fintype.card (I 1) ≤ Fintype.card (I 2)
        · apply finish 2
          omega
        · apply finish 1
          omega
      · by_cases h02 : Fintype.card (I 0) ≤ Fintype.card (I 2)
        · apply finish 2
          omega
        · apply finish 0
          omega
    · have hk4 : 4 ≤ k := by omega
      let j₀ : Fin k := ⟨0, by omega⟩
      have hblock : 0 < Fintype.card (I j₀) := Fintype.card_pos
      have hexp : n - Fintype.card (I j₀) ≤ 2 * H := by omega
      calc
        multiwaySignCPRank part f ≤ 2 ^ (n - Fintype.card (I j₀)) :=
          multiwaySignCPRank_le_two_pow_complement part f j₀
        _ ≤ 2 ^ (2 * H) := Nat.pow_le_pow_right (by omega) hexp
        _ = 4 ^ H := by rw [pow_mul]; norm_num
        _ ≤ k ^ H := Nat.pow_le_pow_left hk4 H
        _ ≤ k * (k ^ H - (k - 1) ^ H) :=
          pow_le_tangent_count (by omega) (by omega)

end CoordinatePartition

end HeadComplexity
