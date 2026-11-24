import HeadComplexity.Results.CubeStarTransfer

set_option linter.style.header false

/-!
Full row cubes crossed with two open stars. This is the outer stage of a
joint row-family construction. The compiler hypothesis is explicit; no
improved decoder or asymptotic upper bound is assumed to exist.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

def cubeTwoStarInput {k a b : ℕ} (x : Fin k → Bool) (i : Fin a) (j : Fin b) :
    Fin (k + (a + b)) → Bool := Fin.addCases x (localGrid i j)

/-- All row inputs are decoded jointly. Both star axes vanish for every row
input and every multihot input on the other star axis. -/
structure ReverseCubeTwoStarData (k r s H : ℕ) where
  a₀ : Fin H → ℝ
  b₀ : Fin H → ℝ
  a : Fin H → Fin (k + (r + s)) → ℝ
  b : Fin H → Fin (k + (r + s)) → ℝ
  positive : ∀ h bits, 0 < affineValue (b₀ h) (b h) bits
  negative : ∀ h i, b h i < 0
  zero_left : ∀ (x : Fin k → Bool) (w : Fin s → Bool),
    (∑ h, affineValue (a₀ h) (a h)
        (Fin.addCases x (Fin.addCases (fun _ : Fin r ↦ false) w)) /
      affineValue (b₀ h) (b h)
        (Fin.addCases x (Fin.addCases (fun _ : Fin r ↦ false) w))) = 0
  zero_right : ∀ (x : Fin k → Bool) (z : Fin r → Bool),
    (∑ h, affineValue (a₀ h) (a h)
        (Fin.addCases x (Fin.addCases z (fun _ : Fin s ↦ false))) /
      affineValue (b₀ h) (b h)
        (Fin.addCases x (Fin.addCases z (fun _ : Fin s ↦ false)))) = 0

noncomputable def ReverseCubeTwoStarData.score {k a b H : ℕ}
    (L : ReverseCubeTwoStarData k a b H) (bits : Fin (k + (a + b)) → Bool) : ℝ :=
  ∑ h, affineValue (L.a₀ h) (L.a h) bits / affineValue (L.b₀ h) (L.b h) bits

def HasReverseCubeTwoStarCompiler (k a b M : ℕ) : Prop :=
  ∀ table : (Fin k → Bool) → Fin a → Fin b → Bool,
    ∃ H ≤ M, ∃ L : ReverseCubeTwoStarData k a b H,
      ∀ x i j, 0 < outputSign (table x i j) * L.score (cubeTwoStarInput x i j)

theorem affineValue_addCases {k s : ℕ} (c : ℝ) (w : Fin (k + s) → ℝ)
    (x : Fin k → Bool) (y : Fin s → Bool) :
    affineValue c w (Fin.addCases x y) =
      affineValue (c + ∑ i, w (Fin.castAdd s i) * boolToReal (x i))
        (fun j ↦ w (Fin.natAdd k j)) y := by
  simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  ring

noncomputable def ReverseCubeTwoStarData.slice {k a b H : ℕ}
    (L : ReverseCubeTwoStarData k a b H) (x : Fin k → Bool) :
    ReverseAxisData a b H where
  a₀ h := L.a₀ h + ∑ i, L.a h (Fin.castAdd (a + b) i) * boolToReal (x i)
  b₀ h := L.b₀ h + ∑ i, L.b h (Fin.castAdd (a + b) i) * boolToReal (x i)
  a h j := L.a h (Fin.natAdd k j)
  b h j := L.b h (Fin.natAdd k j)
  positive h y := by simpa only [affineValue_addCases] using L.positive h (Fin.addCases x y)
  negative h j := L.negative h (Fin.natAdd k j)
  zero_left w := by simpa only [affineValue_addCases] using L.zero_left x w
  zero_right z := by simpa only [affineValue_addCases] using L.zero_right x z

theorem ReverseCubeTwoStarData.score_slice {k a b H : ℕ}
    (L : ReverseCubeTwoStarData k a b H) (x : Fin k → Bool) (y : Fin (a + b) → Bool) :
    L.score (Fin.addCases x y) = (L.slice x).score y := by
  simp only [ReverseCubeTwoStarData.score, ReverseAxisData.score,
    ReverseCubeTwoStarData.slice, affineValue_addCases]

def cubeTwoStarCell {k a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    Finset (Fin (k + (a + b)) → Bool) :=
  Finset.univ.filter fun bits ↦ (fun j ↦ bits (Fin.natAdd k j)) ∈ starCell S T

def cubeTwoStarDownset {k a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    Finset (Fin (k + (a + b)) → Bool) :=
  Finset.univ.filter fun bits ↦ (fun j ↦ bits (Fin.natAdd k j)) ∈ centerDownset S T

def cubeTwoStarCenter {k a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    Fin (k + (a + b)) → Bool := Fin.addCases (fun _ ↦ true) (centerBits S T)

theorem cubeTwoStarCell_subset_downset {k a b : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) :
    cubeTwoStarCell (k := k) S T ⊆ cubeTwoStarDownset S T := by
  intro bits hbits
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    starCell_subset_downset S T (Finset.mem_filter.mp hbits).2⟩

theorem cubeTwoStar_downset_iff {k a b : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (bits : Fin (k + (a + b)) → Bool) :
    bits ∈ cubeTwoStarDownset S T ↔
      ∀ i, bits i = true → cubeTwoStarCenter S T i = true := by
  simp only [cubeTwoStarDownset, Finset.mem_filter, Finset.mem_univ, true_and,
    centerDownset]
  rw [← center_downset_iff]
  constructor
  · intro h i
    refine Fin.addCases ?_ ?_ i
    · intro j _; simp [cubeTwoStarCenter]
    · intro j hj; simpa [cubeTwoStarCenter] using h j hj
  · intro h j hj
    simpa [cubeTwoStarCenter] using h (Fin.natAdd k j) hj

theorem cubeTwoStar_deletion {k a b : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (bits : Fin (k + (a + b)) → Bool) :
    centerDeletion (cubeTwoStarCenter S T) bits =
      Fin.addCases (fun i ↦ !(bits (Fin.castAdd (a + b) i)))
        (centerDeletion (centerBits S T) (fun j ↦ bits (Fin.natAdd k j))) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [centerDeletion, cubeTwoStarCenter]

theorem ReverseCubeTwoStarData.sign_center {k a b H : ℕ}
    (L : ReverseCubeTwoStarData k a b H) (S : Finset (Fin a)) (T : Finset (Fin b))
    (f : (Fin (k + (a + b)) → Bool) → Bool)
    (hsign : ∀ x i j,
      0 < outputSign (f (Fin.addCases (fun l ↦ !(x l))
        (centerBits (S.erase i) (T.erase j)))) * L.score (cubeTwoStarInput x i j))
    (bits : Fin (k + (a + b)) → Bool) (hbits : bits ∈ cubeTwoStarCell S T) :
    0 < outputSign (f bits) * L.score (centerDeletion (cubeTwoStarCenter S T) bits) := by
  let x : Fin k → Bool := fun i ↦ !(bits (Fin.castAdd (a + b) i))
  let y : Fin (a + b) → Bool := fun j ↦ bits (Fin.natAdd k j)
  have heq : Fin.addCases (fun i ↦ !(x i)) y = bits := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [x, y]
  rw [cubeTwoStar_deletion, L.score_slice]
  have h := (L.slice x).sign_center S T (fun z ↦ f (Fin.addCases (fun i ↦ !(x i)) z))
    (fun i j ↦ by rw [← L.score_slice]; exact hsign x i j)
    y (Finset.mem_filter.mp hbits).2
  simpa only [heq] using h

/-- A single score for each full row family is assembled in descending
two-star order. Overlaps have the target sign, axes are exact zeros, and the
localization penalties suppress all other prior inputs. -/
theorem glue_reverse_cube_two_star_modules {k a b : ℕ} (N : ℕ) (H : ℕ → ℕ)
    (S : ℕ → Finset (Fin a)) (T : ℕ → Finset (Fin b))
    (L : (i : ℕ) → ReverseCubeTwoStarData k a b (H i))
    (f : (Fin (k + (a + b)) → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (S i).card + (T i).card ≤ (S j).card + (T j).card)
    (hlocal : ∀ i < N, ∀ x u v,
      0 < outputSign (f (Fin.addCases (fun l ↦ !(x l))
        (centerBits ((S i).erase u) ((T i).erase v)))) *
        (L i).score (cubeTwoStarInput x u v)) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom (k + (a + b)),
      ∀ bits, (∃ i < N, bits ∈ cubeTwoStarCell (S i) (T i)) →
        0 < outputSign (f bits) * ∑ h, (φ h).eval bits := by
  classical
  let center (i : ℕ) := cubeTwoStarCenter (k := k) (S i) (T i)
  let A₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).a₀ h) ((L i).a h) (center i)
  let B₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).b₀ h) ((L i).b h) (center i)
  let A (i : ℕ) (h : Fin (H i)) (j : Fin (k + (a + b))) :=
    if center i j then -(L i).a h j else 0
  let B (i : ℕ) (h : Fin (H i)) (j : Fin (k + (a + b))) :=
    if center i j then -(L i).b h j else 1
  let q (i : ℕ) (j : Fin (k + (a + b))) : ℝ := if center i j then 0 else 1
  have hdown (i : ℕ) (bits : Fin (k + (a + b)) → Bool)
      (hb : bits ∈ cubeTwoStarDownset (S i) (T i)) :
      ∀ j, bits j = true → center i j = true := (cubeTwoStar_downset_iff _ _ _).mp hb
  have hscore (i : ℕ) (bits : Fin (k + (a + b)) → Bool)
      (hb : bits ∈ cubeTwoStarDownset (S i) (T i)) :
      (∑ h, affineValue (A₀ i h) (A i h) bits / affineValue (B₀ i h) (B i h) bits) =
        (L i).score (centerDeletion (center i) bits) := by
    apply Finset.sum_congr rfl
    intro h _
    rw [show affineValue (A₀ i h) (A i h) bits =
        affineValue ((L i).a₀ h) ((L i).a h) (centerDeletion (center i) bits) from
      centerDeletion_affine _ _ (fun _ ↦ 0) _ _ (hdown i bits hb)]
    rw [show affineValue (B₀ i h) (B i h) bits =
        affineValue ((L i).b₀ h) ((L i).b h) (centerDeletion (center i) bits) from
      centerDeletion_affine _ _ (fun _ ↦ 1) _ _ (hdown i bits hb)]
  apply glue_positive_affine_ratios N H (fun i ↦ cubeTwoStarCell (S i) (T i))
    (fun i ↦ cubeTwoStarDownset (S i) (T i)) (fun bits ↦ outputSign (f bits)) A₀ B₀ A B q
  · intro i _ h; exact (L i).positive h (center i)
  · intro i _ h j
    exact (centerDeletion_denominator ((L i).b₀ h) ((L i).b h) (center i)
      ((L i).positive h) ((L i).negative h)).2 j
  · intro i _ j; exact centerPenalty_nonneg (center i) j
  · intro i _; exact cubeTwoStarCell_subset_downset (S i) (T i)
  · intro i hi bits hb
    rw [hscore i bits (cubeTwoStarCell_subset_downset (S i) (T i) hb)]
    exact (L i).sign_center (S i) (T i) f (hlocal i hi) bits hb
  · intro i hi j hj bits hb hd
    rw [hscore i bits hd]
    obtain ⟨hXS, hYT⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).2).2
    obtain ⟨hR, hU⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).2).2
    rcases descending_center_geometry hXS hYT (horder i hi j hj) hR hU with
      hleft | hright | hcell
    · rw [show center i = cubeTwoStarCenter (S i) (T i) from rfl,
        cubeTwoStar_deletion, (L i).score_slice]
      rw [((L i).slice _).zero_center_left (S i) (T i) _ hleft]
      simp
    · rw [show center i = cubeTwoStarCenter (S i) (T i) from rfl,
        cubeTwoStar_deletion, (L i).score_slice]
      rw [((L i).slice _).zero_center_right (S i) (T i) _ hright]
      simp
    · exact ((L i).sign_center (S i) (T i) f (hlocal i hi) bits
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩⟩)).le
  · intro i _ bits hb
    exact (centerPenalty_eq_zero_iff (center i) bits).mpr (hdown i bits hb)
  · intro i _ bits hb
    apply centerPenalty_pos (center i) bits
    exact fun h ↦ hb ((cubeTwoStar_downset_iff _ _ _).mpr h)

/-- Add unrestricted leading coordinates to a coordinate face. -/
def cubeTwoStarLiftFace {m n : ℕ} (k : ℕ) (rho : CoordFace m n) :
    CoordFace (k + m) (k + n) where
  free :=
    { toFun := Fin.addCases (Fin.castAdd n) (fun j ↦ Fin.natAdd k (rho.free j))
      inj' := by
        intro i j
        refine Fin.addCases ?_ ?_ i <;> intro u <;>
          refine Fin.addCases ?_ ?_ j <;> intro v <;>
          simp only [Fin.addCases_left, Fin.addCases_right]
        · exact fun h ↦ congrArg (Fin.castAdd m) (Fin.castAdd_inj.mp h)
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · intro h
          exact congrArg (Fin.natAdd k) (rho.free.injective ((Fin.natAddEmb k).injective h)) }
  base := fun _ ↦ true

theorem on_cubeTwoStarLiftFace {k m n : ℕ} (rho : CoordFace m n)
    (bits : Fin (k + n) → Bool)
    (h : OnPositiveFace rho (fun j ↦ bits (Fin.natAdd k j))) :
    OnPositiveFace (cubeTwoStarLiftFace k rho) bits := by
  intro i hi
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro j hj
    have hm : Fin.castAdd n j ∈ (cubeTwoStarLiftFace k rho).freeSet := by
      apply (CoordFace.mem_freeSet _ _).mpr
      refine ⟨Fin.castAdd m j, ?_⟩
      change (Fin.addCases (Fin.castAdd n) (fun v ↦ Fin.natAdd k (rho.free v)) :
        Fin (k + m) → Fin (k + n)) (Fin.castAdd m j) = _
      simp
    exact False.elim ((Finset.mem_sdiff.mp hj).2 hm)
  · intro j hj
    apply h j
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hm
    obtain ⟨v, hv⟩ := (CoordFace.mem_freeSet _ _).mp hm
    apply (Finset.mem_sdiff.mp hj).2
    apply (CoordFace.mem_freeSet _ _).mpr
    refine ⟨Fin.natAdd k v, ?_⟩
    change (Fin.addCases (Fin.castAdd n) (fun v ↦ Fin.natAdd k (rho.free v)) :
      Fin (k + m) → Fin (k + n)) (Fin.natAdd k v) = _
    simpa using congrArg (Fin.natAdd k) hv

/-- Exact global budget, including both exceptional full faces. -/
theorem HStar_le_cube_two_star_cover_of_compiler {k a b M : ℕ}
    (hcompiler : HasReverseCubeTwoStarCompiler k a b M)
    (D : Finset (Finset (Fin a))) (E : Finset (Finset (Fin b)))
    (hD : OpenDownwardCovers D) (hE : OpenDownwardCovers E)
    (f : (Fin (k + (a + b)) → Bool) → Bool) :
    HStar (k + (a + b)) f ≤ (D ×ˢ E).card * M + 2 ^ (k + a) + 2 ^ (k + b) := by
  classical
  let P := D ×ˢ E
  obtain ⟨center, _hmem, hcover, horder⟩ :=
    enumerate_descending P (fun ST ↦ ST.1.card + ST.2.card)
  let S (i : ℕ) := (center i).1
  let T (i : ℕ) := (center i).2
  have hex (i : ℕ) : ∃ H ≤ M, ∃ L : ReverseCubeTwoStarData k a b H,
      ∀ x u v, 0 < outputSign (f (Fin.addCases (fun l ↦ !(x l))
        (centerBits ((S i).erase u) ((T i).erase v)))) *
        L.score (cubeTwoStarInput x u v) :=
    hcompiler (fun x u v ↦ f (Fin.addCases (fun l ↦ !(x l))
      (centerBits ((S i).erase u) ((T i).erase v))))
  choose H hH L hsign using hex
  obtain ⟨φ, hφ⟩ := glue_reverse_cube_two_star_modules P.card H S T L f horder
    (fun i _ ↦ hsign i)
  let I := ((i : Fin P.card) × Fin (H i.val))
  let equiv : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ψ : Fin (Fintype.card I) → FracAtom (k + (a + b)) := fun h ↦ φ (equiv h)
  have hsum (bits : Fin (k + (a + b)) → Bool) :
      (∑ h, (ψ h).eval bits) = ∑ h, (φ h).eval bits :=
    equiv.sum_comp (fun h ↦ (φ h).eval bits)
  let rho := cubeTwoStarLiftFace k (leftFullFace a b)
  let tau := cubeTwoStarLiftFace k (rightFullFace a b)
  have houtside (bits : Fin (k + (a + b)) → Bool)
      (hleft : ¬OnPositiveFace rho bits) (hright : ¬OnPositiveFace tau bits) :
      (0 < 0 + ∑ h, (ψ h).eval bits ↔ f bits = true) ∧
        0 + ∑ h, (ψ h).eval bits ≠ 0 := by
    let y : Fin (a + b) → Bool := fun j ↦ bits (Fin.natAdd k j)
    have hX : leftOnes y ≠ Finset.univ :=
      fun h ↦ hleft (on_cubeTwoStarLiftFace _ bits (on_leftFullFace_of_leftOnes y h))
    have hY : rightOnes y ≠ Finset.univ :=
      fun h ↦ hright (on_cubeTwoStarLiftFace _ bits (on_rightFullFace_of_rightOnes y h))
    obtain ⟨ST, hST, hS, hT⟩ :=
      product_openDownwardCover D E hD hE (leftOnes y) (rightOnes y) hX hY
    obtain ⟨i, hi, hc⟩ := hcover ST hST
    have hcell : bits ∈ cubeTwoStarCell (S i) (T i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [starCell, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [S, T]
      rw [hc]
      exact ⟨hS, hT⟩
    have hpos := hφ bits ⟨i, hi, hcell⟩
    simpa only [zero_add, hsum] using strict_of_outputSign hpos
  have hrepair := HStar_le_repair_two_positive_faces rho tau
    (fun _ ↦ rfl) (fun _ ↦ rfl) ψ 0 f houtside
  have hcount : Fintype.card I ≤ P.card * M := by
    rw [show Fintype.card I = ∑ i ∈ Finset.range P.card, H i from glued_head_count _ _]
    calc
      ∑ i ∈ Finset.range P.card, H i ≤ ∑ _i ∈ Finset.range P.card, M :=
        Finset.sum_le_sum (fun i _ ↦ hH i)
      _ = P.card * M := by simp
  dsimp [P] at hrepair hcount ⊢
  omega

/-- Quantitative transfer for a jointly decoded row family. The factors
`2^(k+a)` and `2^(k+b)` charge the two exceptional faces explicitly. -/
theorem worstCaseHeadComplexity_real_le_of_cube_two_star_compiler {k a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcompiler : HasReverseCubeTwoStarCompiler k a b M) :
    (worstCaseHeadComplexity (k + (a + b)) : ℝ) ≤
      484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
        2 ^ (k + a) + 2 ^ (k + b) := by
  obtain ⟨D, E, hD, hE, hcount⟩ := exists_product_openDownwardCover a b ha hb
  let B : ℝ := 484 * (2 : ℝ) ^ (a + b) * M / ((a : ℝ) * b) +
    2 ^ (k + a) + 2 ^ (k + b)
  have hall (f : (Fin (k + (a + b)) → Bool) → Bool) :
      (HStar (k + (a + b)) f : ℝ) ≤ B := by
    have hfinite := HStar_le_cube_two_star_cover_of_compiler hcompiler D E hD hE f
    have hcast : (HStar (k + (a + b)) f : ℝ) ≤
        ((D ×ˢ E).card : ℝ) * M + (2 : ℝ) ^ (k + a) + (2 : ℝ) ^ (k + b) := by
      exact_mod_cast hfinite
    calc
      _ ≤ ((D ×ˢ E).card : ℝ) * M + (2 : ℝ) ^ (k + a) + (2 : ℝ) ^ (k + b) := hcast
      _ ≤ (484 * (2 : ℝ) ^ (a + b) / ((a : ℝ) * b)) * M +
          2 ^ (k + a) + 2 ^ (k + b) := by gcongr
      _ = B := by dsimp [B]; ring
  have hnat : worstCaseHeadComplexity (k + (a + b)) ≤ ⌊B⌋₊ := by
    apply Finset.sup_le
    intro f _
    exact Nat.le_floor (hall f)
  exact (by exact_mod_cast hnat :
    (worstCaseHeadComplexity (k + (a + b)) : ℝ) ≤ (⌊B⌋₊ : ℝ)).trans
      (Nat.floor_le (by dsimp [B]; positivity))

end HeadComplexity.AxisZeroGluing
