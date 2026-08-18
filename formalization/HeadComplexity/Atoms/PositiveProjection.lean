import HeadComplexity.Atoms.PositiveWeightedSignDegree
import HeadComplexity.Polynomial.OrderedSignChanges
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Ordered positive projections

This is the literal ordered-image presentation of the positive-projection
invariant.  A certificate lists every value of a positive weighted statistic
in increasing order and records the Boolean label at each value.  Its cost is
the number of adjacent label changes.

The main equivalence identifies these certificates with the polynomial
presentation `PositiveWeightedSignDegLE`.  Consequently their two minimum
invariants are equal.
-/

namespace HeadComplexity

open Finset Polynomial

variable {n K L : ℕ} {f : (Fin n → Bool) → Bool}

/-- A positive weighted projection together with the complete increasing list
of its image values and their labels. -/
structure PositiveProjection (f : (Fin n → Bool) → Bool) where
  lam : Fin n → ℝ
  lam_pos : ∀ i, 0 < lam i
  steps : ℕ
  node : Fin (steps + 1) → ℝ
  node_strictMono : StrictMono node
  label : Fin (steps + 1) → Bool
  realized : ∀ i, ∃ bits, node i = wT lam bits
  covers : ∀ bits, ∃ i, node i = wT lam bits
  agrees : ∀ bits i, node i = wT lam bits → f bits = label i

namespace PositiveProjection

/-- Extend the finite label vector to a natural-number profile. -/
def profile (C : PositiveProjection f) : ℕ → Bool := fun k =>
  if hk : k ≤ C.steps then C.label (orderedNodeIndex C.steps k hk) else false

@[simp] theorem profile_at (C : PositiveProjection f) (i : Fin (C.steps + 1)) :
    C.profile i = C.label i := by
  rw [profile, dif_pos (Nat.lt_succ_iff.mp i.isLt)]
  congr

/-- The number of adjacent label changes along this ordered projection. -/
def alternations (C : PositiveProjection f) : ℕ :=
  signChanges C.steps C.profile

/-- A fixed ordered positive projection supplies a univariate sign polynomial
with exactly its alternation count as a degree upper bound. -/
theorem univariateThresholdDegLE (C : PositiveProjection f) :
    UnivariateThresholdDegLE (wT C.lam) f C.alternations := by
  obtain ⟨P, hPdeg, hPsign⟩ :=
    exists_ordered_sign_poly C.node C.node_strictMono C.profile
  refine ⟨P, hPdeg, ?_⟩
  intro bits
  obtain ⟨i, hi⟩ := C.covers bits
  have hik : (i : ℕ) ≤ C.steps := Nat.lt_succ_iff.mp i.isLt
  have hnode : C.node (orderedNodeIndex C.steps i hik) = C.node i := by
    congr
  have hagree := C.agrees bits i hi
  simpa [hnode, hi, C.profile_at i, hagree] using hPsign i hik

/-- Conversely, every polynomial through the same statistic has degree at
least the ordered projection's alternation count. -/
theorem alternations_le_of_univariateThresholdDegLE (C : PositiveProjection f)
    (h : UnivariateThresholdDegLE (wT C.lam) f K) : C.alternations ≤ K := by
  obtain ⟨P, hPdeg, hPsign⟩ := h
  refine (ordered_signChanges_le_of_sign_iff P C.node C.node_strictMono C.profile ?_).trans hPdeg
  intro k hk
  let i : Fin (C.steps + 1) := orderedNodeIndex C.steps k hk
  obtain ⟨bits, hbits⟩ := C.realized i
  have hsign := hPsign bits
  rw [← hbits] at hsign
  have hagree := C.agrees bits i hbits
  rw [profile, dif_pos hk]
  simpa [i, hagree] using hsign

/-- The least univariate sign degree available through this fixed statistic. -/
noncomputable def signDegree (C : PositiveProjection f) : ℕ := by
  classical
  exact Nat.find ⟨C.alternations, C.univariateThresholdDegLE⟩

theorem signDegree_spec (C : PositiveProjection f) :
    UnivariateThresholdDegLE (wT C.lam) f C.signDegree := by
  classical
  exact Nat.find_spec ⟨C.alternations, C.univariateThresholdDegLE⟩

/-- For a fixed projection, least univariate sign degree equals the adjacent
label-change count. -/
theorem signDegree_eq_alternations (C : PositiveProjection f) :
    C.signDegree = C.alternations := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' _ C.univariateThresholdDegLE
  · exact C.alternations_le_of_univariateThresholdDegLE C.signDegree_spec

end PositiveProjection

/-- There is an ordered positive projection with at most `K` label changes. -/
def PositiveProjectionChangesLE (f : (Fin n → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ C : PositiveProjection f, C.alternations ≤ K

namespace PositiveProjection

/-- Build a canonical ordered-image certificate from a positive weighted
univariate polynomial certificate. -/
theorem changesLE_of_positiveWeightedSignDegLE
    (h : PositiveWeightedSignDegLE f K) : PositiveProjectionChangesLE f K := by
  classical
  obtain ⟨lam, hlam, P, hPdeg, hPsign⟩ := h
  let S : Finset ℝ := Finset.univ.image (wT lam)
  have hS : S.Nonempty := by
    exact ⟨wT lam (fun _ => false), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hcard : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (Finset.card_pos.mpr hS)
  let e : Fin (S.card - 1 + 1) ≃o Fin S.card := Fin.castOrderIso hcard
  let nodes : Fin (S.card - 1 + 1) → ℝ :=
    fun i => S.orderEmbOfFin rfl (e i)
  let C : PositiveProjection f :=
    { lam := lam
      lam_pos := hlam
      steps := S.card - 1
      node := nodes
      node_strictMono := (S.orderEmbOfFin rfl).strictMono.comp e.strictMono
      label := fun i => decide (0 < P.eval (nodes i))
      realized := by
        intro i
        have hiS : nodes i ∈ S := by
          exact S.orderEmbOfFin_mem rfl (e i)
        change nodes i ∈ Finset.univ.image (wT lam) at hiS
        rw [Finset.mem_image] at hiS
        obtain ⟨bits, -, hbits⟩ := hiS
        exact ⟨bits, hbits.symm⟩
      covers := by
        intro bits
        have hmem : wT lam bits ∈ S := by
          exact Finset.mem_image_of_mem _ (Finset.mem_univ bits)
        let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨wT lam bits, hmem⟩
        refine ⟨e.symm j, ?_⟩
        change S.orderEmbOfFin rfl (e (e.symm j)) = wT lam bits
        rw [e.apply_symm_apply]
        exact congrArg Subtype.val
          ((S.orderIsoOfFin rfl).apply_symm_apply ⟨wT lam bits, hmem⟩)
      agrees := by
        intro bits i hi
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        rw [hi]
        exact (hPsign bits).symm }
  refine ⟨C, C.alternations_le_of_univariateThresholdDegLE ?_⟩
  exact ⟨P, hPdeg, by simpa [C] using hPsign⟩

end PositiveProjection

/-- Ordered projection changes and positive weighted sign degree are the same
bounded certificate notion. -/
theorem positiveProjectionChangesLE_iff_positiveWeightedSignDegLE
    (f : (Fin n → Bool) → Bool) (K : ℕ) :
    PositiveProjectionChangesLE f K ↔ PositiveWeightedSignDegLE f K := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C.lam, C.lam_pos, C.univariateThresholdDegLE.mono hC⟩
  · intro h
    exact PositiveProjection.changesLE_of_positiveWeightedSignDegLE h

/-- Every Boolean function has an ordered positive projection certificate. -/
theorem exists_positiveProjectionChangesLE (f : (Fin n → Bool) → Bool) :
    ∃ K, PositiveProjectionChangesLE f K := by
  obtain ⟨K, hK⟩ := exists_positiveWeightedSignDegLE f
  exact ⟨K,
    (positiveProjectionChangesLE_iff_positiveWeightedSignDegLE f K).2 hK⟩

/-- The literal positive-projection sign-change invariant `C_+`. -/
noncomputable def positiveProjectionSignChanges
    (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_positiveProjectionChangesLE f)

/-- The minimum ordered positive-projection change count is attained. -/
theorem positiveProjectionSignChanges_spec (f : (Fin n → Bool) → Bool) :
    PositiveProjectionChangesLE f (positiveProjectionSignChanges f) := by
  classical
  exact Nat.find_spec (exists_positiveProjectionChangesLE f)

/-- Every explicit ordered positive projection upper-bounds `C_+`. -/
theorem positiveProjectionSignChanges_le {f : (Fin n → Bool) → Bool}
    (h : PositiveProjectionChangesLE f K) :
    positiveProjectionSignChanges f ≤ K := by
  classical
  exact Nat.find_min' (exists_positiveProjectionChangesLE f) h

/-- The ordered-image sign-change invariant is exactly the existing polynomial
certificate invariant. -/
theorem positiveProjectionSignChanges_eq_positiveWeightedSignDeg
    (f : (Fin n → Bool) → Bool) :
    positiveProjectionSignChanges f = positiveWeightedSignDeg f := by
  apply Nat.le_antisymm
  · exact positiveProjectionSignChanges_le
      ((positiveProjectionChangesLE_iff_positiveWeightedSignDegLE f
        (positiveWeightedSignDeg f)).2 (positiveWeightedSignDeg_spec f))
  · exact positiveWeightedSignDeg_le
      ((positiveProjectionChangesLE_iff_positiveWeightedSignDegLE f
        (positiveProjectionSignChanges f)).1 (positiveProjectionSignChanges_spec f))

end HeadComplexity
