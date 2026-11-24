import HeadComplexity.Results.AxisZeroTransfer

set_option linter.style.header false

/-!
# Full-cube rows and one-star columns

This transfer treats all row inputs jointly before decoding. Its local
compiler hypothesis is explicit; no improved asymptotic compiler is assumed
to exist. The original model and worst-case complexity are unchanged.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- A full cube of row addresses crossed with one column-star vertex. -/
def cubeStarInput {k s : ℕ} (x : Fin k → Bool) (j : Fin s) :
    Fin (k + s) → Bool := Fin.addCases x (fun l ↦ decide (l = j))

/-- Only the zero-column axis must vanish; row addresses range over the whole
cube. Positivity is required on the full ambient cube, including multihot
column inputs, and all denominator slopes are strictly negative. -/
structure ReverseCubeStarData (k s H : ℕ) where
  a₀ : Fin H → ℝ
  b₀ : Fin H → ℝ
  a : Fin H → Fin (k + s) → ℝ
  b : Fin H → Fin (k + s) → ℝ
  positive : ∀ h bits, 0 < affineValue (b₀ h) (b h) bits
  negative : ∀ h i, b h i < 0
  zero_column : ∀ x : Fin k → Bool,
    (∑ h, affineValue (a₀ h) (a h) (Fin.addCases x (fun _ : Fin s ↦ false)) /
      affineValue (b₀ h) (b h) (Fin.addCases x (fun _ : Fin s ↦ false))) = 0

noncomputable def ReverseCubeStarData.score {k s H : ℕ}
    (L : ReverseCubeStarData k s H) (bits : Fin (k + s) → Bool) : ℝ :=
  ∑ h, affineValue (L.a₀ h) (L.a h) bits / affineValue (L.b₀ h) (L.b h) bits

/-- The unrestricted, independent-label local compiler needed by this route. -/
def HasReverseCubeStarCompiler (k s M : ℕ) : Prop :=
  ∀ table : (Fin k → Bool) → Fin s → Bool,
    ∃ H ≤ M, ∃ L : ReverseCubeStarData k s H,
      ∀ x j, 0 < outputSign (table x j) * L.score (cubeStarInput x j)

def cubeStarCell {k s : ℕ} (T : Finset (Fin s)) :
    Finset (Fin (k + s) → Bool) :=
  Finset.univ.filter fun bits ↦ ∃ j ∈ T, T.erase j = rightOnes bits

theorem cubeStarCell_subset_downset {k s : ℕ} (T : Finset (Fin s)) :
    cubeStarCell (k := k) T ⊆ centerDownset Finset.univ T := by
  intro bits hbits
  obtain ⟨j, _, hj⟩ := (Finset.mem_filter.mp hbits).2
  simp only [centerDownset, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨Finset.subset_univ _, ?_⟩
  rw [← hj]
  exact Finset.erase_subset _ _

theorem cubeStar_centerDeletion {k s : ℕ} (T : Finset (Fin s))
    (x : Fin k → Bool) (j : Fin s) (hj : j ∈ T) :
    centerDeletion (centerBits Finset.univ T)
      (Fin.addCases (fun i ↦ !(x i)) (fun l ↦ decide (l ∈ T.erase j))) =
        cubeStarInput x j := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro l
    simp [centerDeletion, centerBits, cubeStarInput]
  · intro l
    by_cases hlj : l = j
    · subst l
      simp [centerDeletion, centerBits, cubeStarInput, hj]
    · by_cases hl : l ∈ T <;>
        simp [centerDeletion, centerBits, cubeStarInput, hlj, hl]

theorem ReverseCubeStarData.zero_center {k s H : ℕ}
    (L : ReverseCubeStarData k s H) (T : Finset (Fin s))
    (bits : Fin (k + s) → Bool) (h : rightOnes bits = T) :
    L.score (centerDeletion (centerBits Finset.univ T) bits) = 0 := by
  conv_lhs => arg 2; arg 2; rw [← centerBits_ones bits, h]
  rw [centerDeletion_centerBits]
  simp only [Finset.sdiff_self]
  unfold ReverseCubeStarData.score centerBits
  simpa using L.zero_column (fun i ↦ decide (i ∈ Finset.univ \ leftOnes bits))

theorem ReverseCubeStarData.sign_center {k s H : ℕ}
    (L : ReverseCubeStarData k s H) (T : Finset (Fin s))
    (f : (Fin (k + s) → Bool) → Bool)
    (hsign : ∀ x j,
      0 < outputSign (f (Fin.addCases (fun i ↦ !(x i))
        (fun l ↦ decide (l ∈ T.erase j)))) * L.score (cubeStarInput x j))
    (bits : Fin (k + s) → Bool) (hbits : bits ∈ cubeStarCell T) :
    0 < outputSign (f bits) * L.score (centerDeletion (centerBits Finset.univ T) bits) := by
  obtain ⟨j, hj, heq⟩ := (Finset.mem_filter.mp hbits).2
  let x : Fin k → Bool := fun i ↦ !(bits (Fin.castAdd s i))
  have hb : bits = Fin.addCases (fun i ↦ !(x i))
      (fun l ↦ decide (l ∈ T.erase j)) := by
    rw [heq]
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro l <;> simp [x, rightOnes]
  rw [hb, cubeStar_centerDeletion T x j hj]
  exact hsign x j

/-- The one-star ordering invariant. Full row cubes introduce no additional
exceptional boundaries or row-axis repair. -/
theorem cubeStar_descending_geometry {s : ℕ} {Y T U : Finset (Fin s)}
    (hYT : Y ⊆ T) (horder : T.card ≤ U.card)
    (hU : ∃ j ∈ U, U.erase j = Y) :
    Y = T ∨ ∃ j ∈ T, T.erase j = Y := by
  obtain ⟨j, hj, hUY⟩ := hU
  have hUc : U.card = Y.card + 1 := by
    rw [← hUY, Finset.card_erase_of_mem hj]
    have := Finset.card_pos.mpr ⟨j, hj⟩
    omega
  have hcard := Finset.card_le_card hYT
  by_cases h : T.card = Y.card
  · exact Or.inl (Finset.eq_of_subset_of_card_le hYT h.le)
  · exact Or.inr (exists_erase_of_subset_card hYT (by omega))

/-- All cells use one score on their entire row cube. Descending column
centers preserve prior signs by an exact zero or the required target sign.
Outside a center downset, a nonnegative affine penalty suppresses the new
score. The resulting heads satisfy the original admissibility conditions. -/
theorem glue_reverse_cube_star_modules {k s : ℕ} (N : ℕ) (H : ℕ → ℕ)
    (T : ℕ → Finset (Fin s)) (L : (i : ℕ) → ReverseCubeStarData k s (H i))
    (f : (Fin (k + s) → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (T i).card ≤ (T j).card)
    (hlocal : ∀ i < N, ∀ x j,
      0 < outputSign (f (Fin.addCases (fun l ↦ !(x l))
        (fun l ↦ decide (l ∈ (T i).erase j)))) * (L i).score (cubeStarInput x j)) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom (k + s),
      ∀ bits, (∃ i < N, bits ∈ cubeStarCell (T i)) →
        0 < outputSign (f bits) * ∑ h, (φ h).eval bits := by
  classical
  let center (i : ℕ) := centerBits (Finset.univ : Finset (Fin k)) (T i)
  let A₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).a₀ h) ((L i).a h) (center i)
  let B₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).b₀ h) ((L i).b h) (center i)
  let A (i : ℕ) (h : Fin (H i)) (j : Fin (k + s)) :=
    if center i j then -(L i).a h j else 0
  let B (i : ℕ) (h : Fin (H i)) (j : Fin (k + s)) :=
    if center i j then -(L i).b h j else 1
  let q (i : ℕ) (j : Fin (k + s)) : ℝ := if center i j then 0 else 1
  have hdown (i : ℕ) (bits : Fin (k + s) → Bool)
      (hbits : bits ∈ centerDownset Finset.univ (T i)) :
      ∀ j, bits j = true → center i j = true :=
    (center_downset_iff Finset.univ (T i) bits).mpr (Finset.mem_filter.mp hbits).2
  have hscore (i : ℕ) (bits : Fin (k + s) → Bool)
      (hbits : bits ∈ centerDownset Finset.univ (T i)) :
      (∑ h, affineValue (A₀ i h) (A i h) bits / affineValue (B₀ i h) (B i h) bits) =
        (L i).score (centerDeletion (center i) bits) := by
    apply Finset.sum_congr rfl
    intro h _
    rw [show affineValue (A₀ i h) (A i h) bits =
        affineValue ((L i).a₀ h) ((L i).a h) (centerDeletion (center i) bits) from
      centerDeletion_affine _ _ (fun _ ↦ 0) _ _ (hdown i bits hbits)]
    rw [show affineValue (B₀ i h) (B i h) bits =
        affineValue ((L i).b₀ h) ((L i).b h) (centerDeletion (center i) bits) from
      centerDeletion_affine _ _ (fun _ ↦ 1) _ _ (hdown i bits hbits)]
  apply glue_positive_affine_ratios N H (fun i ↦ cubeStarCell (T i))
    (fun i ↦ centerDownset Finset.univ (T i)) (fun bits ↦ outputSign (f bits)) A₀ B₀ A B q
  · intro i _ h
    exact (L i).positive h (center i)
  · intro i _ h j
    exact (centerDeletion_denominator ((L i).b₀ h) ((L i).b h) (center i)
      ((L i).positive h) ((L i).negative h)).2 j
  · intro i _ j
    exact centerPenalty_nonneg (center i) j
  · intro i _
    exact cubeStarCell_subset_downset (T i)
  · intro i hi bits hbits
    rw [hscore i bits (cubeStarCell_subset_downset (T i) hbits)]
    exact (L i).sign_center (T i) f (hlocal i hi) bits hbits
  · intro i hi j hj bits hbits hd
    rw [hscore i bits hd]
    have hYT := (Finset.mem_filter.mp hd).2.2
    have hU := (Finset.mem_filter.mp hbits).2
    rcases cubeStar_descending_geometry hYT (horder i hi j hj) hU with hzero | hcell
    · rw [(L i).zero_center (T i) bits hzero]
      simp
    · exact ((L i).sign_center (T i) f (hlocal i hi) bits
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩)).le
  · intro i _ bits hbits
    exact (centerPenalty_eq_zero_iff (center i) bits).mpr (hdown i bits hbits)
  · intro i _ bits hbits
    apply centerPenalty_pos (center i) bits
    intro h
    apply hbits
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (center_downset_iff Finset.univ (T i) bits).mp h⟩

/-- Exact finite cover budget. The two identical exceptional-face repairs
give a conservative cost of `2^(k+1)`; there is only one exceptional face. -/
theorem HStar_le_cube_star_cover_of_compiler {k s M : ℕ}
    (hcompiler : HasReverseCubeStarCompiler k s M)
    (D : Finset (Finset (Fin s))) (hD : OpenDownwardCovers D)
    (f : (Fin (k + s) → Bool) → Bool) :
    HStar (k + s) f ≤ D.card * M + 2 ^ (k + 1) := by
  classical
  obtain ⟨T, _hmem, hcover, horder⟩ := enumerate_descending D Finset.card
  have hex (i : ℕ) : ∃ H ≤ M, ∃ L : ReverseCubeStarData k s H,
      ∀ x j, 0 < outputSign (f (Fin.addCases (fun l ↦ !(x l))
        (fun l ↦ decide (l ∈ (T i).erase j)))) * L.score (cubeStarInput x j) :=
    hcompiler (fun x j ↦ f (Fin.addCases (fun l ↦ !(x l))
      (fun l ↦ decide (l ∈ (T i).erase j))))
  choose H hH L hsign using hex
  obtain ⟨φ, hφ⟩ := glue_reverse_cube_star_modules D.card H T L f horder
    (fun i _ ↦ hsign i)
  let I := ((i : Fin D.card) × Fin (H i.val))
  let equiv : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ψ : Fin (Fintype.card I) → FracAtom (k + s) := fun h ↦ φ (equiv h)
  have hsum (bits : Fin (k + s) → Bool) :
      (∑ h, (ψ h).eval bits) = ∑ h, (φ h).eval bits :=
    equiv.sum_comp (fun h ↦ (φ h).eval bits)
  have houtside (bits : Fin (k + s) → Bool)
      (hright : ¬OnPositiveFace (rightFullFace k s) bits) :
      (0 < 0 + ∑ h, (ψ h).eval bits ↔ f bits = true) ∧
        0 + ∑ h, (ψ h).eval bits ≠ 0 := by
    have hY : rightOnes bits ≠ Finset.univ :=
      fun h ↦ hright (on_rightFullFace_of_rightOnes bits h)
    obtain ⟨U, hU, j, hj, hUj⟩ := hD (rightOnes bits) hY
    obtain ⟨i, hi, hT⟩ := hcover U hU
    have hcell : bits ∈ cubeStarCell (T i) := by
      simp only [cubeStarCell, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hT]
      exact ⟨j, hj, hUj⟩
    have hpos := hφ bits ⟨i, hi, hcell⟩
    simpa only [zero_add, hsum] using strict_of_outputSign hpos
  have hrepair := HStar_le_repair_two_positive_faces
    (rightFullFace k s) (rightFullFace k s) (fun _ ↦ rfl) (fun _ ↦ rfl)
    ψ 0 f (fun bits h _ ↦ houtside bits h)
  have hcount : Fintype.card I ≤ D.card * M := by
    rw [show Fintype.card I = ∑ i ∈ Finset.range D.card, H i from glued_head_count _ _]
    calc
      ∑ i ∈ Finset.range D.card, H i ≤ ∑ _i ∈ Finset.range D.card, M :=
        Finset.sum_le_sum (fun i _ ↦ hH i)
      _ = D.card * M := by simp
  rw [pow_succ]
  omega

/-- One-star cover transfer for an arbitrary full-cube row decoder. It
includes overlap protection, exact axis compatibility, and exceptions. -/
theorem HStar_real_le_of_cube_star_compiler {k s M : ℕ} (hs : 0 < s)
    (hcompiler : HasReverseCubeStarCompiler k s M)
    (f : (Fin (k + s) → Bool) → Bool) :
    (HStar (k + s) f : ℝ) ≤ 22 * (2 : ℝ) ^ s * M / s + 2 ^ (k + 1) := by
  obtain ⟨D, hD, hcard⟩ := exists_openDownwardCover s hs
  have hfinite := HStar_le_cube_star_cover_of_compiler hcompiler D hD f
  have hcast : (HStar (k + s) f : ℝ) ≤ (D.card : ℝ) * M + 2 ^ (k + 1) := by
    exact_mod_cast hfinite
  calc
    (HStar (k + s) f : ℝ) ≤ (D.card : ℝ) * M + 2 ^ (k + 1) := hcast
    _ ≤ (22 * (2 : ℝ) ^ s / s) * M + 2 ^ (k + 1) := by gcongr
    _ = 22 * (2 : ℝ) ^ s * M / s + 2 ^ (k + 1) := by ring

/-- Conditional global consequence against the authoritative original
`worstCaseHeadComplexity`. An improved decoder remains a separate obligation. -/
theorem worstCaseHeadComplexity_real_le_of_cube_star_compiler {k s M : ℕ}
    (hs : 0 < s) (hcompiler : HasReverseCubeStarCompiler k s M) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      22 * (2 : ℝ) ^ s * M / s + 2 ^ (k + 1) := by
  let B : ℝ := 22 * (2 : ℝ) ^ s * M / s + 2 ^ (k + 1)
  have hnat : worstCaseHeadComplexity (k + s) ≤ ⌊B⌋₊ := by
    apply Finset.sup_le
    intro f _
    exact Nat.le_floor (HStar_real_le_of_cube_star_compiler hs hcompiler f)
  exact (by exact_mod_cast hnat : (worstCaseHeadComplexity (k + s) : ℝ) ≤ (⌊B⌋₊ : ℝ)).trans
    (Nat.floor_le (by dsimp [B]; positivity))

end HeadComplexity.AxisZeroGluing
