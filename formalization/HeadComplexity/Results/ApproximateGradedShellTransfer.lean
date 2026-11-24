import HeadComplexity.Results.GradedShellTransfer
import HeadComplexity.Atoms.AtomicMargin

set_option linter.style.header false

/-!
# Limits of admissible scores and graded shell assembly

Limits are taken in the finite-dimensional space of scores on the entire
Boolean cube. A strict sign pattern attained by a limit is attained by actual
original-model atoms with the same number of heads. Intermediate numerators
may diverge, and no uniform convergence rate is required.
-/

namespace HeadComplexity.AxisZeroGluing

open Filter
open scoped BigOperators Topology

def headScoreRange (n : ℕ) (I : Type*) [Fintype I] :
    Set ((Fin n → Bool) → ℝ) :=
  Set.range fun φ : I → FracAtom n ↦ fun x ↦ ∑ h, (φ h).eval x

def HeadScoreClosure (n : ℕ) (I : Type*) [Fintype I]
    (F : (Fin n → Bool) → ℝ) : Prop :=
  F ∈ closure (headScoreRange n I)

/-- Strict signs on any finite set pass from a limiting score to actual
admissible heads, with exactly the same index type. -/
theorem HeadScoreClosure.strict_signs {n : ℕ} {I : Type*} [Fintype I]
    {F : (Fin n → Bool) → ℝ} (hF : HeadScoreClosure n I F)
    (P : Finset (Fin n → Bool)) (σ : (Fin n → Bool) → ℝ)
    (hpos : ∀ x ∈ P, 0 < σ x * F x) :
    ∃ φ : I → FracAtom n, ∀ x ∈ P, 0 < σ x * ∑ h, (φ h).eval x := by
  classical
  have hevent : ∀ᶠ G in 𝓝 F, ∀ x ∈ P, 0 < σ x * G x := by
    apply (Finset.eventually_all P).mpr
    intro x hx
    exact (tendsto_const_nhds.mul (continuous_apply x).continuousAt).eventually
      (eventually_gt_nhds (hpos x hx))
  obtain ⟨G, hG, φ, rfl⟩ := (mem_closure_iff_nhds.mp hF) _ hevent
  exact ⟨φ, hG⟩

/-- Finite sums of independently approximable score modules remain
approximable with the sum of their head counts. -/
theorem HeadScoreClosure.sum {n : ℕ} {J : Type*} [Fintype J]
    {I : J → Type*} [∀ j, Fintype (I j)]
    (F : J → (Fin n → Bool) → ℝ) (scale : J → ℝ)
    (hF : ∀ j, HeadScoreClosure n (I j) (F j)) :
    HeadScoreClosure n ((j : J) × I j) (fun x ↦ ∑ j, scale j * F j x) := by
  classical
  let S := Set.pi Set.univ (fun j ↦ headScoreRange n (I j))
  have hmem : F ∈ closure S := mem_closure_pi.mpr (fun j _ ↦ hF j)
  let add : (J → (Fin n → Bool) → ℝ) → (Fin n → Bool) → ℝ :=
    fun G x ↦ ∑ j, scale j * G j x
  have hadd : Continuous add := by
    unfold add
    fun_prop
  have himage := mem_closure_image hadd.continuousAt hmem
  apply closure_mono (s := add '' S) (t := headScoreRange n ((j : J) × I j)) ?_ himage
  rintro _ ⟨G, hG, rfl⟩
  have hchoice : ∀ j, ∃ φ : I j → FracAtom n, (fun x ↦ ∑ h, (φ h).eval x) = G j := by
    intro j
    exact hG j (Set.mem_univ j)
  choose φ hφ using hchoice
  refine ⟨fun h ↦ (φ h.1 h.2).scale (scale h.1), ?_⟩
  funext x
  simp only [Fintype.sum_sigma, FracAtom.scale_eval, ← Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ congrArg (fun V ↦ scale j * V x) (hφ j))

/-- Closure under an arbitrary pointwise convergent family on the finite cube.
This also permits repeated limits and arbitrarily large intermediate residues. -/
theorem HeadScoreClosure.of_tendsto {n : ℕ} {I A : Type*} [Fintype I]
    {l : Filter A} [NeBot l] {F : A → (Fin n → Bool) → ℝ}
    {G : (Fin n → Bool) → ℝ}
    (hlim : ∀ x, Tendsto (fun a ↦ F a x) l (𝓝 (G x)))
    (hF : ∀ᶠ a in l, HeadScoreClosure n I (F a)) : HeadScoreClosure n I G := by
  exact isClosed_closure.mem_of_tendsto (tendsto_pi_nhds.mpr hlim) hF

/-- A nonnegative affine denominator penalty makes a score vanish outside
its zero set in the closure of the same admissible head family. -/
theorem positive_ratios_restrict_closure {n : ℕ} {I : Type*} [Fintype I]
    (D : Finset (Fin n → Bool)) (a₀ b₀ : I → ℝ)
    (a b : I → Fin n → ℝ) (q : Fin n → ℝ)
    (hb₀ : ∀ h, 0 < b₀ h) (hb : ∀ h i, 0 < b h i)
    (hq : ∀ i, 0 ≤ q i)
    (hzero : ∀ x ∈ D, affineValue 0 q x = 0)
    (hout : ∀ x, x ∉ D → 0 < affineValue 0 q x) :
    HeadScoreClosure n I (fun x ↦ if x ∈ D then
      ∑ h, affineValue (a₀ h) (a h) x / affineValue (b₀ h) (b h) x else 0) := by
  classical
  let Ft (t : ℝ) (x : Fin n → Bool) := ∑ h,
    affineValue (a₀ h) (a h) x /
      (affineValue (b₀ h) (b h) x + t * affineValue 0 q x)
  apply mem_closure_of_tendsto (f := Ft) (b := atTop)
  · apply tendsto_pi_nhds.mpr
    intro x
    by_cases hx : x ∈ D
    · simp [Ft, hx, hzero x hx]
    · simpa only [hx, ite_false] using ratios_tendsto_zero
        (fun h ↦ affineValue (a₀ h) (a h) x)
        (fun h ↦ affineValue (b₀ h) (b h) x) _ (hout x hx)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hex : ∀ h, ∃ φ : FracAtom n, ∀ x, φ.eval x =
        affineValue (a₀ h) (a h) x /
          (affineValue (b₀ h) (b h) x + t * affineValue 0 q x) :=
      fun h ↦ penalty_admissible _ _ _ _ _ _ (hb₀ h) (hb h) hq ht
    choose φ hφ using hex
    refine ⟨φ, ?_⟩
    funext x
    exact Finset.sum_congr rfl (fun h _ ↦ hφ h x)

/-- Centering and suppressing a reverse module costs no additional heads,
even when only a limiting realization is needed. -/
theorem ReverseGradedData.centered_closure {n d H : ℕ}
    (L : ReverseGradedData n d H) (C : Finset (Fin n)) :
    HeadScoreClosure n (Fin H) (fun x ↦ if x ∈ gradedDownset C then
      L.score (centerDeletion (gradedCenter C) x) else 0) := by
  classical
  let center := gradedCenter C
  let A₀ (h : Fin H) := affineValue (L.a₀ h) (L.a h) center
  let B₀ (h : Fin H) := affineValue (L.b₀ h) (L.b h) center
  let A (h : Fin H) (j : Fin n) := if center j then -L.a h j else 0
  let B (h : Fin H) (j : Fin n) := if center j then -L.b h j else 1
  let q (j : Fin n) : ℝ := if center j then 0 else 1
  have hscore (x : Fin n → Bool) (hx : x ∈ gradedDownset C) :
      (∑ h, affineValue (A₀ h) (A h) x / affineValue (B₀ h) (B h) x) =
        L.score (centerDeletion center x) := by
    have hdown := (gradedDownset_iff C x).mp hx
    apply Finset.sum_congr rfl
    intro h _
    rw [show affineValue (A₀ h) (A h) x =
        affineValue (L.a₀ h) (L.a h) (centerDeletion center x) from
      centerDeletion_affine _ _ (fun _ ↦ 0) _ _ hdown]
    rw [show affineValue (B₀ h) (B h) x =
        affineValue (L.b₀ h) (L.b h) (centerDeletion center x) from
      centerDeletion_affine _ _ (fun _ ↦ 1) _ _ hdown]
  have h := positive_ratios_restrict_closure (gradedDownset C) A₀ B₀ A B q
    (fun h ↦ L.positive h center)
    (fun h ↦ (centerDeletion_denominator (L.b₀ h) (L.b h) center
      (L.positive h) (L.negative h)).2)
    (centerPenalty_nonneg center)
    (fun x hx ↦ (centerPenalty_eq_zero_iff center x).mpr ((gradedDownset_iff C x).mp hx))
    (fun x hx ↦ centerPenalty_pos center x (fun h ↦ hx ((gradedDownset_iff C x).mpr h)))
  convert h using 1
  funext x
  split_ifs with hx
  · exact (hscore x hx).symm
  · rfl

/-- A reverse score may cancel proper layers only in the limit. All actual
approximants still have strictly negative slopes and positive denominators
throughout the entire Boolean cube. -/
structure ReverseApproxGradedData (n d H : ℕ) where
  approx : ℝ → ReverseGradedData n 0 H
  limit : (Fin n → Bool) → ℝ
  tendsto : ∀ x, Tendsto (fun t ↦ (approx t).score x) atTop (𝓝 (limit x))
  zero_below : ∀ x, (gradedSupport x).card < d → limit x = 0

theorem ReverseApproxGradedData.centered_closure {n d H : ℕ}
    (L : ReverseApproxGradedData n d H) (C : Finset (Fin n)) :
    HeadScoreClosure n (Fin H) (fun x ↦ if x ∈ gradedDownset C then
      L.limit (centerDeletion (gradedCenter C) x) else 0) := by
  classical
  apply HeadScoreClosure.of_tendsto
    (F := fun t x ↦ if x ∈ gradedDownset C then
      (L.approx t).score (centerDeletion (gradedCenter C) x) else 0)
    (l := atTop)
  · intro x
    by_cases hx : x ∈ gradedDownset C
    · simpa only [hx, ite_true] using L.tendsto (centerDeletion (gradedCenter C) x)
    · simp only [hx, ite_false]
      exact tendsto_const_nhds
  · exact Filter.Eventually.of_forall (fun t ↦ (L.approx t).centered_closure C)

/-- Sign-compatible limiting modules assemble with the sum of their head
counts. Every approximation is chosen only after all ideal margins are fixed. -/
theorem glue_headScoreClosure {n : ℕ} (N : ℕ) (H : ℕ → ℕ)
    (C : ℕ → Finset (Fin n → Bool)) (F : ℕ → (Fin n → Bool) → ℝ)
    (σ : (Fin n → Bool) → ℝ)
    (hclosure : ∀ i < N, HeadScoreClosure n (Fin (H i)) (F i))
    (hlocal : ∀ i < N, ∀ x ∈ C i, 0 < σ x * F i x)
    (hcompat : ∀ i < N, ∀ j < i, ∀ x ∈ C j, 0 ≤ σ x * F i x) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom n,
      ∀ x, (∃ i < N, x ∈ C i) → 0 < σ x * ∑ h, (φ h).eval x := by
  classical
  obtain ⟨scale, param, _, hsign⟩ := glue_finite C (fun _ ↦ Finset.univ) σ F
    (fun i _ ↦ F i) N (by simp) hlocal
    (fun i hi j hj x hx _ ↦ hcompat i hi j hj x hx)
    (by intros; rfl) (by simp)
  have hcl := HeadScoreClosure.sum (fun i : Fin N ↦ F i.val)
    (fun i ↦ scale i.val) (fun i ↦ hclosure i.val i.isLt)
  obtain ⟨φ, hφ⟩ := hcl.strict_signs ((Finset.range N).biUnion C) σ (by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hx⟩
    rw [show (∑ j : Fin N, scale j.val * F j.val x) =
      ∑ j ∈ Finset.range N, scale j * F j x from
      Fin.sum_univ_eq_sum_range (fun j ↦ scale j * F j x) N]
    exact hsign x ⟨i, Finset.mem_range.mp hi, hx⟩)
  refine ⟨φ, fun x hx ↦ hφ x ?_⟩
  rcases hx with ⟨i, hi, hx⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hx⟩

/-- Proper deletion layers need only vanish in the limit, not identically in
each approximant. Overlaps and all earlier strict signs are still charged. -/
theorem glue_reverse_approx_graded_shell_modules {n : ℕ} (N : ℕ) (H d : ℕ → ℕ)
    (C : ℕ → Finset (Fin n))
    (L : (i : ℕ) → ReverseApproxGradedData n (d i) (H i))
    (f : (Fin n → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hlocal : ∀ i < N, ∀ x ∈ gradedShell (C i) (d i),
      0 < outputSign (f x) * (L i).limit (centerDeletion (gradedCenter (C i)) x)) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom n,
      ∀ x, (∃ i < N, x ∈ gradedShell (C i) (d i)) →
        0 < outputSign (f x) * ∑ h, (φ h).eval x := by
  classical
  let F (i : ℕ) (x : Fin n → Bool) := if x ∈ gradedDownset (C i) then
    (L i).limit (centerDeletion (gradedCenter (C i)) x) else 0
  apply glue_headScoreClosure N H (fun i ↦ gradedShell (C i) (d i)) F
    (fun x ↦ outputSign (f x)) (fun i _ ↦ (L i).centered_closure (C i))
  · intro i hi x hx
    simpa only [F, gradedShell_subset_downset (C i) (d i) hx, ite_true] using
      hlocal i hi x hx
  · intro i hi j hj x hx
    by_cases hd : x ∈ gradedDownset (C i)
    · dsimp only [F]
      rw [ite_eq_left hd]
      rcases gradedShell_descending_geometry hx hd (horder i hi j hj) with hz | hc
      · rw [(L i).zero_below _ hz]
        simp
      · exact (hlocal i hi x hc).le
    · simp only [F, hd, ite_false, mul_zero, le_refl]

/-- Exact total count for a full shell cover whose local scores are available
only as limits of admissible reverse heads. -/
theorem HStar_le_approx_graded_shell_cover {n : ℕ} (N : ℕ) (H d : ℕ → ℕ)
    (C : ℕ → Finset (Fin n))
    (L : (i : ℕ) → ReverseApproxGradedData n (d i) (H i))
    (f : (Fin n → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hlocal : ∀ i < N, ∀ x ∈ gradedShell (C i) (d i),
      0 < outputSign (f x) * (L i).limit (centerDeletion (gradedCenter (C i)) x))
    (hcover : ∀ x, ∃ i < N, x ∈ gradedShell (C i) (d i)) :
    HStar n f ≤ ∑ i ∈ Finset.range N, H i := by
  classical
  obtain ⟨φ, hφ⟩ := glue_reverse_approx_graded_shell_modules N H d C L f horder hlocal
  let I := ((i : Fin N) × Fin (H i.val))
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfrac : fracComputable n (Fintype.card I) f := by
    refine ⟨fun h ↦ φ (e h), 0, fun x ↦ ?_⟩
    have heq := e.sum_comp (fun h ↦ (φ h).eval x)
    have hs := (strict_of_outputSign (hφ x (hcover x))).1
    simpa only [zero_add, heq] using hs
  have hbound := HStar_le_of_computableWithHeadsN (computable_of_fracComputable hfrac)
  simpa only [I, glued_head_count] using hbound

/-- Global transfer against the unchanged original worst-case quantity.
Existence of a sufficiently efficient local decoder remains a hypothesis. -/
theorem worstCaseHeadComplexity_le_approx_graded_shell_cover {n : ℕ} (N : ℕ)
    (H d : ℕ → ℕ) (C : ℕ → Finset (Fin n))
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hcover : ∀ x, ∃ i < N, x ∈ gradedShell (C i) (d i))
    (hcompiler : ∀ f : (Fin n → Bool) → Bool,
      ∃ L : (i : ℕ) → ReverseApproxGradedData n (d i) (H i),
        ∀ i < N, ∀ x ∈ gradedShell (C i) (d i),
          0 < outputSign (f x) *
            (L i).limit (centerDeletion (gradedCenter (C i)) x)) :
    worstCaseHeadComplexity n ≤ ∑ i ∈ Finset.range N, H i := by
  apply Finset.sup_le
  intro f _
  obtain ⟨L, hL⟩ := hcompiler f
  exact HStar_le_approx_graded_shell_cover N H d C L f horder hL hcover

end HeadComplexity.AxisZeroGluing
