import HeadComplexity.Results.AxisZeroTransfer

set_option linter.style.header false

/-!
# Gluing reverse modules on downward shells

The ordering uses target rank rather than center rank. Different deletion
depths, including singleton exceptions of depth zero, may occur in one cover.
The exact lower-layer cancellation condition is explicit. No efficient shell
decoder is asserted to exist.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

def gradedSupport {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = true

def gradedCenter {n : ℕ} (C : Finset (Fin n)) : Fin n → Bool :=
  fun i ↦ decide (i ∈ C)

def gradedDownset {n : ℕ} (C : Finset (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x ↦ gradedSupport x ⊆ C

def gradedShell {n : ℕ} (C : Finset (Fin n)) (d : ℕ) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter fun x ↦ gradedSupport x ⊆ C ∧
    C.card = (gradedSupport x).card + d

theorem gradedSupport_deletion {n : ℕ} (C : Finset (Fin n))
    (x : Fin n → Bool) :
    gradedSupport (centerDeletion (gradedCenter C) x) = C \ gradedSupport x := by
  ext i
  cases hx : x i <;> simp [gradedSupport, centerDeletion, gradedCenter, hx]

theorem gradedDownset_iff {n : ℕ} (C : Finset (Fin n)) (x : Fin n → Bool) :
    x ∈ gradedDownset C ↔ ∀ i, x i = true → gradedCenter C i = true := by
  simp only [gradedDownset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    simpa [gradedCenter] using h (by simp [gradedSupport, hi])
  · intro h i hi
    have hx : x i = true := (Finset.mem_filter.mp hi).2
    simpa [gradedCenter] using h i hx

theorem gradedShell_subset_downset {n : ℕ} (C : Finset (Fin n)) (d : ℕ) :
    gradedShell C d ⊆ gradedDownset C := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1⟩

/-- Earlier targets inside a later center have deletion depth at most that
center's prescribed depth. This works for different depths and overlaps. -/
theorem gradedShell_descending_geometry {n : ℕ} {C U : Finset (Fin n)}
    {c d : ℕ} {x : Fin n → Bool}
    (hx : x ∈ gradedShell U d) (hdown : x ∈ gradedDownset C)
    (horder : C.card - c ≤ U.card - d) :
    (gradedSupport (centerDeletion (gradedCenter C) x)).card < c ∨
      x ∈ gradedShell C c := by
  have hU := (Finset.mem_filter.mp hx).2.2
  have hC := (Finset.mem_filter.mp hdown).2
  have hle := Finset.card_le_card hC
  have hcard : (C \ gradedSupport x).card = C.card - (gradedSupport x).card :=
    Finset.card_sdiff_of_subset hC
  rw [gradedSupport_deletion, hcard]
  by_cases hlt : C.card - (gradedSupport x).card < c
  · exact Or.inl hlt
  · right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC, by omega⟩

/-- An admissible reverse score that cancels exactly on all proper deletion
layers. At the target layer its labels will be supplied separately. -/
structure ReverseGradedData (n d H : ℕ) where
  a₀ : Fin H → ℝ
  b₀ : Fin H → ℝ
  a : Fin H → Fin n → ℝ
  b : Fin H → Fin n → ℝ
  positive : ∀ h x, 0 < affineValue (b₀ h) (b h) x
  negative : ∀ h i, b h i < 0
  zero_below : ∀ x : Fin n → Bool, (gradedSupport x).card < d →
    (∑ h, affineValue (a₀ h) (a h) x / affineValue (b₀ h) (b h) x) = 0

noncomputable def ReverseGradedData.score {n d H : ℕ}
    (L : ReverseGradedData n d H) (x : Fin n → Bool) : ℝ :=
  ∑ h, affineValue (L.a₀ h) (L.a h) x / affineValue (L.b₀ h) (L.b h) x

/-- One admissible score for an entire finite family of graded shells.
Every prior sign is protected by lower-layer cancellation, a current target
sign, or a nonnegative affine suppression penalty outside the center. -/
theorem glue_reverse_graded_shell_modules {n : ℕ} (N : ℕ) (H d : ℕ → ℕ)
    (C : ℕ → Finset (Fin n)) (L : (i : ℕ) → ReverseGradedData n (d i) (H i))
    (f : (Fin n → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hlocal : ∀ i < N, ∀ x ∈ gradedShell (C i) (d i),
      0 < outputSign (f x) * (L i).score (centerDeletion (gradedCenter (C i)) x)) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom n,
      ∀ x, (∃ i < N, x ∈ gradedShell (C i) (d i)) →
        0 < outputSign (f x) * ∑ h, (φ h).eval x := by
  classical
  let center (i : ℕ) := gradedCenter (C i)
  let A₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).a₀ h) ((L i).a h) (center i)
  let B₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).b₀ h) ((L i).b h) (center i)
  let A (i : ℕ) (h : Fin (H i)) (j : Fin n) :=
    if center i j then -(L i).a h j else 0
  let B (i : ℕ) (h : Fin (H i)) (j : Fin n) :=
    if center i j then -(L i).b h j else 1
  let q (i : ℕ) (j : Fin n) : ℝ := if center i j then 0 else 1
  have hscore (i : ℕ) (x : Fin n → Bool) (hx : x ∈ gradedDownset (C i)) :
      (∑ h, affineValue (A₀ i h) (A i h) x / affineValue (B₀ i h) (B i h) x) =
        (L i).score (centerDeletion (center i) x) := by
    have hdown := (gradedDownset_iff (C i) x).mp hx
    apply Finset.sum_congr rfl
    intro h _
    rw [show affineValue (A₀ i h) (A i h) x =
        affineValue ((L i).a₀ h) ((L i).a h) (centerDeletion (center i) x) from
      centerDeletion_affine _ _ (fun _ ↦ 0) _ _ hdown]
    rw [show affineValue (B₀ i h) (B i h) x =
        affineValue ((L i).b₀ h) ((L i).b h) (centerDeletion (center i) x) from
      centerDeletion_affine _ _ (fun _ ↦ 1) _ _ hdown]
  apply glue_positive_affine_ratios N H (fun i ↦ gradedShell (C i) (d i))
    (fun i ↦ gradedDownset (C i)) (fun x ↦ outputSign (f x)) A₀ B₀ A B q
  · intro i _ h
    exact (L i).positive h (center i)
  · intro i _ h j
    exact (centerDeletion_denominator ((L i).b₀ h) ((L i).b h) (center i)
      ((L i).positive h) ((L i).negative h)).2 j
  · intro i _ j
    exact centerPenalty_nonneg (center i) j
  · intro i _
    exact gradedShell_subset_downset (C i) (d i)
  · intro i hi x hx
    rw [hscore i x (gradedShell_subset_downset (C i) (d i) hx)]
    exact hlocal i hi x hx
  · intro i hi j hj x hx hd
    rw [hscore i x hd]
    rcases gradedShell_descending_geometry hx hd (horder i hi j hj) with hz | hc
    · rw [show (L i).score (centerDeletion (center i) x) = 0 from
        (L i).zero_below _ hz]
      simp
    · exact (hlocal i hi x hc).le
  · intro i _ x hx
    exact (centerPenalty_eq_zero_iff (center i) x).mpr
      ((gradedDownset_iff (C i) x).mp hx)
  · intro i _ x hx
    exact centerPenalty_pos (center i) x
      (fun h ↦ hx ((gradedDownset_iff (C i) x).mpr h))

/-- Exact global count for a full shell cover, with arbitrary overlaps and
depth-zero exception modules already included in the sum. -/
theorem HStar_le_graded_shell_cover {n : ℕ} (N : ℕ) (H d : ℕ → ℕ)
    (C : ℕ → Finset (Fin n)) (L : (i : ℕ) → ReverseGradedData n (d i) (H i))
    (f : (Fin n → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hlocal : ∀ i < N, ∀ x ∈ gradedShell (C i) (d i),
      0 < outputSign (f x) * (L i).score (centerDeletion (gradedCenter (C i)) x))
    (hcover : ∀ x, ∃ i < N, x ∈ gradedShell (C i) (d i)) :
    HStar n f ≤ ∑ i ∈ Finset.range N, H i := by
  classical
  obtain ⟨φ, hφ⟩ := glue_reverse_graded_shell_modules N H d C L f horder hlocal
  let I := ((i : Fin N) × Fin (H i.val))
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfrac : fracComputable n (Fintype.card I) f := by
    refine ⟨fun h ↦ φ (e h), 0, fun x ↦ ?_⟩
    have heq := e.sum_comp (fun h ↦ (φ h).eval x)
    have hs := (strict_of_outputSign (hφ x (hcover x))).1
    simpa only [zero_add, heq] using hs
  have hbound := HStar_le_of_computableWithHeadsN (computable_of_fracComputable hfrac)
  simpa only [I, glued_head_count] using hbound

/-- The shell transfer against the original worst-case quantity. The local
compiler hypothesis quantifies over completely arbitrary global labels. -/
theorem worstCaseHeadComplexity_le_graded_shell_cover {n : ℕ} (N : ℕ)
    (H d : ℕ → ℕ) (C : ℕ → Finset (Fin n))
    (horder : ∀ i < N, ∀ j < i, (C i).card - d i ≤ (C j).card - d j)
    (hcover : ∀ x, ∃ i < N, x ∈ gradedShell (C i) (d i))
    (hcompiler : ∀ f : (Fin n → Bool) → Bool,
      ∃ L : (i : ℕ) → ReverseGradedData n (d i) (H i),
        ∀ i < N, ∀ x ∈ gradedShell (C i) (d i),
          0 < outputSign (f x) *
            (L i).score (centerDeletion (gradedCenter (C i)) x)) :
    worstCaseHeadComplexity n ≤ ∑ i ∈ Finset.range N, H i := by
  apply Finset.sup_le
  intro f _
  obtain ⟨L, hL⟩ := hcompiler f
  exact HStar_le_graded_shell_cover N H d C L f horder hL hcover

/-- Singleton exceptions need one head each, with no lower-layer condition.
The denominator remains strictly positive on the entire cube. -/
theorem exists_reverseGradedData_depth_zero (n : ℕ) (label : Bool) :
    ∃ L : ReverseGradedData n 0 1, ∀ x,
      0 < outputSign label * L.score x := by
  have hpos (x : Fin n → Bool) :
      0 < affineValue ((n : ℝ) + 1) (fun _ ↦ (-1 : ℝ)) x := by
    have hs : (∑ i : Fin n, boolToReal (x i)) ≤ (n : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ by
          cases x i <;> norm_num [boolToReal])
        _ = n := by simp
    simp only [affineValue, neg_one_mul, Finset.sum_neg_distrib]
    linarith
  let L : ReverseGradedData n 0 1 :=
    { a₀ := fun _ ↦ outputSign label
      b₀ := fun _ ↦ (n : ℝ) + 1
      a := fun _ _ ↦ 0
      b := fun _ _ ↦ -1
      positive := fun _ ↦ hpos
      negative := by intros; norm_num
      zero_below := by intro x hx; omega }
  refine ⟨L, fun x ↦ ?_⟩
  have hp := hpos x
  cases label
  · simpa [ReverseGradedData.score, L, outputSign, affineValue, boolToReal]
      using div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) hp
  · simpa [ReverseGradedData.score, L, outputSign, affineValue, boolToReal]
      using one_div_pos.mpr hp

end HeadComplexity.AxisZeroGluing
