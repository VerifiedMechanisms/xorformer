import HeadComplexity.Results.AxisZeroGluing
import HeadComplexity.Results.AxisZeroCover
import HeadComplexity.Results.AxisZeroFaces
import Mathlib.Data.List.Sort

set_option linter.style.header false

/-!
# Concrete geometry and budgets for reverse axis-zero gluing

These results transfer an explicit local-module hypothesis to the unchanged
`HStar` and `worstCaseHeadComplexity`. They do not assert the missing sublinear
local compiler.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Finset
open scoped BigOperators

section Geometry

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A one-element gap in a finite downset is exactly one open-star edge. -/
theorem exists_erase_of_subset_card {X S : Finset α}
    (hXS : X ⊆ S) (hcard : S.card = X.card + 1) :
    ∃ i ∈ S, S.erase i = X := by
  obtain ⟨i, hi⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (show X.card < S.card by omega)
  obtain ⟨hiS, hiX⟩ := Finset.mem_sdiff.mp hi
  refine ⟨i, hiS, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro j hj
    exact Finset.mem_erase.mpr ⟨fun hji ↦ hiX (hji ▸ hj), hXS hj⟩
  · rw [Finset.card_erase_of_mem hiS]
    omega

/-- Inside a later downset, an earlier product-star vertex is either on an
axis of that downset or is itself in its product star. -/
theorem descending_center_geometry {X S R : Finset α} {Y T U : Finset β}
    (hXS : X ⊆ S) (hYT : Y ⊆ T)
    (horder : S.card + T.card ≤ R.card + U.card)
    (hR : ∃ i ∈ R, R.erase i = X) (hU : ∃ j ∈ U, U.erase j = Y) :
    X = S ∨ Y = T ∨
      ((∃ i ∈ S, S.erase i = X) ∧ (∃ j ∈ T, T.erase j = Y)) := by
  obtain ⟨i, hi, hRi⟩ := hR
  obtain ⟨j, hj, hUj⟩ := hU
  have hRc : R.card = X.card + 1 := by
    rw [← hRi, Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hUc : U.card = Y.card + 1 := by
    rw [← hUj, Finset.card_erase_of_mem hj]
    have := Finset.card_pos.mpr ⟨j, hj⟩
    omega
  rcases deletion_counts (Finset.card_le_card hXS) (Finset.card_le_card hYT)
    horder (by omega : R.card + U.card = X.card + Y.card + 2) with h | h | ⟨hS, hT⟩
  · exact Or.inl (Finset.eq_of_subset_of_card_le hXS h.le)
  · exact Or.inr (Or.inl (Finset.eq_of_subset_of_card_le hYT h.le))
  · exact Or.inr (Or.inr ⟨exists_erase_of_subset_card hXS hS,
      exists_erase_of_subset_card hYT hT⟩)

end Geometry

/- A finite list ordered by decreasing rank supplies the exact order required
by the strict-sign gluing theorem. Equal-rank centers may occur in any order. -/
theorem enumerate_descending {X : Type*} [Inhabited X] (P : Finset X) (rank : X → ℕ) :
    ∃ center : ℕ → X,
      (∀ i < P.card, center i ∈ P) ∧
      (∀ x ∈ P, ∃ i < P.card, center i = x) ∧
      (∀ i < P.card, ∀ j < i, rank (center i) ≤ rank (center j)) := by
  classical
  let r : X → X → Prop := fun x y ↦ rank y ≤ rank x
  letI : Std.Total r := ⟨fun x y ↦ le_total (rank y) (rank x)⟩
  letI : IsTrans X r := ⟨fun _ _ _ hxy hyz ↦ le_trans hyz hxy⟩
  let L := P.toList.mergeSort (fun x y ↦ decide (r x y))
  have hlen : L.length = P.card := by simp [L]
  have hmem (x : X) : x ∈ L ↔ x ∈ P := by
    rw [(List.mergeSort_perm P.toList (fun x y ↦ decide (r x y))).mem_iff]
    exact Finset.mem_toList
  have hpair : L.Pairwise r := List.pairwise_mergeSort' r P.toList
  let center : ℕ → X := fun i ↦ if hi : i < L.length then L.get ⟨i, hi⟩ else default
  have heq (i : ℕ) (hi : i < P.card) :
      center i = L.get ⟨i, by omega⟩ := by simp [center, show i < L.length by omega]
  refine ⟨center, ?_, ?_, ?_⟩
  · intro i hi
    rw [heq i hi]
    exact (hmem _).mp (List.get_mem L _)
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((hmem x).mpr hx)
    refine ⟨i.val, by omega, ?_⟩
    rw [heq i.val (by omega)]
    exact hi
  · intro i hi j hj
    rw [heq i hi, heq j (by omega)]
    exact (List.pairwise_iff_get.mp hpair) ⟨j, by omega⟩ ⟨i, by omega⟩ hj

section Reversal

/-- Reverse precisely the coordinates selected by a center, and set all
other local coordinates to zero. -/
def centerDeletion {n : ℕ} (center bits : Fin n → Bool) : Fin n → Bool :=
  fun i ↦ center i && !(bits i)

/-- The affine substitution used to turn negative local slopes into positive
ambient slopes. Outside slopes are arbitrary because those coordinates vanish
on the center downset. -/
theorem centerDeletion_affine {n : ℕ} (c : ℝ) (a outside : Fin n → ℝ)
    (center bits : Fin n → Bool)
    (hdown : ∀ i, bits i = true → center i = true) :
    affineValue (affineValue c a center)
        (fun i ↦ if center i then -a i else outside i) bits =
      affineValue c a (centerDeletion center bits) := by
  unfold affineValue
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi := hdown i
  cases hc : center i <;> cases hb : bits i <;>
    simp_all [centerDeletion, boolToReal]

/-- A negative-slope denominator positive on the full local cube becomes an
original-model positive affine denominator on the original input dimension. -/
theorem centerDeletion_denominator {n : ℕ} (b₀ : ℝ) (b : Fin n → ℝ)
    (center : Fin n → Bool)
    (hpositive : ∀ bits, 0 < affineValue b₀ b bits)
    (hnegative : ∀ i, b i < 0) :
    0 < affineValue b₀ b center ∧
      ∀ i, 0 < (if center i then -b i else (1 : ℝ)) := by
  refine ⟨hpositive center, ?_⟩
  intro i
  cases center i <;> simp [neg_pos.mpr (hnegative i)]

/-- The localization penalty is nonnegative in every coordinate. -/
theorem centerPenalty_nonneg {n : ℕ} (center : Fin n → Bool) (i : Fin n) :
    0 ≤ (if center i then (0 : ℝ) else 1) := by
  cases center i <;> norm_num

/-- The localization penalty vanishes exactly on the center downset. -/
theorem centerPenalty_eq_zero_iff {n : ℕ} (center bits : Fin n → Bool) :
    affineValue 0 (fun i ↦ if center i then (0 : ℝ) else 1) bits = 0 ↔
      ∀ i, bits i = true → center i = true := by
  have hnonneg (i : Fin n) :
      0 ≤ (if center i then (0 : ℝ) else 1) * boolToReal (bits i) := by
    cases center i <;> cases bits i <;> norm_num [boolToReal]
  simp only [affineValue, zero_add]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hnonneg i)]
  constructor
  · intro h i hi
    have hterm := h i (Finset.mem_univ i)
    cases hc : center i <;> simp_all [boolToReal]
  · intro h i _
    have hi := h i
    cases hc : center i <;> cases hb : bits i <;> simp_all [boolToReal]

/-- Outside the center downset the localization penalty is strictly positive. -/
theorem centerPenalty_pos {n : ℕ} (center bits : Fin n → Bool)
    (h : ¬∀ i, bits i = true → center i = true) :
    0 < affineValue 0 (fun i ↦ if center i then (0 : ℝ) else 1) bits := by
  have hnonneg : 0 ≤ affineValue 0 (fun i ↦ if center i then (0 : ℝ) else 1) bits := by
    unfold affineValue
    apply add_nonneg le_rfl
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (centerPenalty_nonneg center i)
      (by cases bits i <;> simp [boolToReal])
  exact lt_of_le_of_ne hnonneg
    (Ne.symm (fun heq ↦ h ((centerPenalty_eq_zero_iff center bits).mp heq)))

end Reversal

section LocalCompiler

/-- The numerical sign attached to a Boolean output. -/
def outputSign (v : Bool) : ℝ := if v then 1 else -1

/-- The local product-star input. -/
def localGrid {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b) → Bool :=
  Fin.addCases (fun k ↦ decide (k = i)) (fun k ↦ decide (k = j))

/-- A local reverse module with its scalar bias already absorbed. Every
denominator is positive on the entire local cube, not only its grid. -/
structure ReverseAxisData (r s H : ℕ) where
  a₀ : Fin H → ℝ
  b₀ : Fin H → ℝ
  a : Fin H → Fin (r + s) → ℝ
  b : Fin H → Fin (r + s) → ℝ
  positive : ∀ h bits, 0 < affineValue (b₀ h) (b h) bits
  negative : ∀ h k, b h k < 0
  zero_left : ∀ w : Fin s → Bool,
    (∑ h, affineValue (a₀ h) (a h) (Fin.addCases (fun _ : Fin r ↦ false) w) /
      affineValue (b₀ h) (b h) (Fin.addCases (fun _ : Fin r ↦ false) w)) = 0
  zero_right : ∀ z : Fin r → Bool,
    (∑ h, affineValue (a₀ h) (a h) (Fin.addCases z (fun _ : Fin s ↦ false)) /
      affineValue (b₀ h) (b h) (Fin.addCases z (fun _ : Fin s ↦ false))) = 0

noncomputable def ReverseAxisData.score {a b H : ℕ} (L : ReverseAxisData a b H)
    (bits : Fin (a + b) → Bool) : ℝ :=
  ∑ h, affineValue (L.a₀ h) (L.a h) bits / affineValue (L.b₀ h) (L.b h) bits

/-- Explicit local hypothesis used by the transfer theorem. No instance of a
sublinear budget is asserted in this file. -/
def HasReverseAxisCompiler (a b M : ℕ) : Prop :=
  ∀ table : Fin a → Fin b → Bool, ∃ H ≤ M, ∃ L : ReverseAxisData a b H,
    ∀ i j, 0 < outputSign (table i j) * L.score (localGrid i j)

/-- A center as a vertex of the unchanged ambient cube. -/
def centerBits {a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    Fin (a + b) → Bool :=
  Fin.addCases (fun i ↦ decide (i ∈ S)) (fun j ↦ decide (j ∈ T))

def leftOnes {a b : ℕ} (bits : Fin (a + b) → Bool) : Finset (Fin a) :=
  Finset.univ.filter (fun i ↦ bits (Fin.castAdd b i) = true)

def rightOnes {a b : ℕ} (bits : Fin (a + b) → Bool) : Finset (Fin b) :=
  Finset.univ.filter (fun j ↦ bits (Fin.natAdd a j) = true)

theorem centerBits_ones {a b : ℕ} (bits : Fin (a + b) → Bool) :
    centerBits (leftOnes bits) (rightOnes bits) = bits := by
  funext k
  refine Fin.addCases ?_ ?_ k <;> intro i <;>
    simp [centerBits, leftOnes, rightOnes]

theorem center_downset_iff {a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b))
    (bits : Fin (a + b) → Bool) :
    (∀ i, bits i = true → centerBits S T i = true) ↔
      leftOnes bits ⊆ S ∧ rightOnes bits ⊆ T := by
  constructor
  · intro h
    constructor
    · intro i hi
      have := h (Fin.castAdd b i) (by simpa [leftOnes] using hi)
      simpa [centerBits] using this
    · intro j hj
      have := h (Fin.natAdd a j) (by simpa [rightOnes] using hj)
      simpa [centerBits] using this
  · rintro ⟨hS, hT⟩ k
    refine Fin.addCases ?_ ?_ k
    · intro i hi
      simpa [centerBits] using hS (by simpa [leftOnes] using hi)
    · intro j hj
      simpa [centerBits] using hT (by simpa [rightOnes] using hj)

theorem centerDeletion_grid {a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b))
    (i : Fin a) (j : Fin b) (hi : i ∈ S) (hj : j ∈ T) :
    centerDeletion (centerBits S T) (centerBits (S.erase i) (T.erase j)) =
      localGrid i j := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro l
    by_cases hli : l = i
    · subst l; simp [centerDeletion, centerBits, localGrid, hi]
    · by_cases hlS : l ∈ S <;>
        simp [centerDeletion, centerBits, localGrid, hli, hlS]
  · intro l
    by_cases hlj : l = j
    · subst l; simp [centerDeletion, centerBits, localGrid, hj]
    · by_cases hlT : l ∈ T <;>
        simp [centerDeletion, centerBits, localGrid, hlj, hlT]

theorem centerDeletion_centerBits {a b : ℕ}
    (S X : Finset (Fin a)) (T Y : Finset (Fin b)) :
    centerDeletion (centerBits S T) (centerBits X Y) = centerBits (S \ X) (T \ Y) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    by_cases hiS : i ∈ S <;> by_cases hiX : i ∈ X <;>
      simp [centerDeletion, centerBits, hiS, hiX]
  · intro j
    by_cases hjT : j ∈ T <;> by_cases hjY : j ∈ Y <;>
      simp [centerDeletion, centerBits, hjT, hjY]

theorem ReverseAxisData.zero_center_left {a b H : ℕ} (L : ReverseAxisData a b H)
    (S : Finset (Fin a)) (T : Finset (Fin b)) (bits : Fin (a + b) → Bool)
    (h : leftOnes bits = S) :
    L.score (centerDeletion (centerBits S T) bits) = 0 := by
  conv_lhs => arg 2; arg 2; rw [← centerBits_ones bits, h]
  rw [centerDeletion_centerBits]
  simp only [Finset.sdiff_self]
  unfold ReverseAxisData.score centerBits
  simpa using
    L.zero_left (fun j ↦ decide (j ∈ T \ rightOnes bits))

theorem ReverseAxisData.zero_center_right {a b H : ℕ} (L : ReverseAxisData a b H)
    (S : Finset (Fin a)) (T : Finset (Fin b)) (bits : Fin (a + b) → Bool)
    (h : rightOnes bits = T) :
    L.score (centerDeletion (centerBits S T) bits) = 0 := by
  conv_lhs => arg 2; arg 2; rw [← centerBits_ones bits, h]
  rw [centerDeletion_centerBits]
  simp only [Finset.sdiff_self]
  unfold ReverseAxisData.score centerBits
  simpa using
    L.zero_right (fun i ↦ decide (i ∈ S \ leftOnes bits))

/-- The product of the two open stars of a center. -/
def starCell {a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    Finset (Fin (a + b) → Bool) :=
  Finset.univ.filter fun bits ↦
    (∃ i ∈ S, S.erase i = leftOnes bits) ∧ (∃ j ∈ T, T.erase j = rightOnes bits)

/-- The Boolean downset of a center. -/
def centerDownset {a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    Finset (Fin (a + b) → Bool) :=
  Finset.univ.filter fun bits ↦ leftOnes bits ⊆ S ∧ rightOnes bits ⊆ T

theorem starCell_subset_downset {a b : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) :
    starCell S T ⊆ centerDownset S T := by
  intro bits hbits
  obtain ⟨⟨i, _, hi⟩, ⟨j, _, hj⟩⟩ := (Finset.mem_filter.mp hbits).2
  simp only [centerDownset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hi, ← hj]
  exact ⟨Finset.erase_subset _ _, Finset.erase_subset _ _⟩

theorem ReverseAxisData.sign_center {a b H : ℕ} (L : ReverseAxisData a b H)
    (S : Finset (Fin a)) (T : Finset (Fin b)) (f : (Fin (a + b) → Bool) → Bool)
    (hsign : ∀ i j, 0 < outputSign (f (centerBits (S.erase i) (T.erase j))) *
      L.score (localGrid i j))
    (bits : Fin (a + b) → Bool) (hbits : bits ∈ starCell S T) :
    0 < outputSign (f bits) * L.score (centerDeletion (centerBits S T) bits) := by
  obtain ⟨⟨i, hi, hiX⟩, ⟨j, hj, hjY⟩⟩ := (Finset.mem_filter.mp hbits).2
  have heq : bits = centerBits (S.erase i) (T.erase j) := by
    rw [hiX, hjY, centerBits_ones]
  rw [heq, centerDeletion_grid S T i j hi hj]
  exact hsign i j

end LocalCompiler

/-- Concrete descending-center assembly. The local hypotheses refer only to
negative-slope, full-cube-positive modules with axis zeros. All output atoms
have the original input dimension and strict original admissibility. -/
theorem glue_reverse_axis_modules {a b : ℕ} (N : ℕ) (H : ℕ → ℕ)
    (S : ℕ → Finset (Fin a)) (T : ℕ → Finset (Fin b))
    (L : (i : ℕ) → ReverseAxisData a b (H i)) (f : (Fin (a + b) → Bool) → Bool)
    (horder : ∀ i < N, ∀ j < i, (S i).card + (T i).card ≤ (S j).card + (T j).card)
    (hlocal : ∀ i < N, ∀ k l,
      0 < outputSign (f (centerBits ((S i).erase k) ((T i).erase l))) *
        (L i).score (localGrid k l)) :
    ∃ φ : ((i : Fin N) × Fin (H i.val)) → FracAtom (a + b),
      ∀ bits, (∃ i < N, bits ∈ starCell (S i) (T i)) →
        0 < outputSign (f bits) * ∑ h, (φ h).eval bits := by
  classical
  let center (i : ℕ) := centerBits (S i) (T i)
  let A₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).a₀ h) ((L i).a h) (center i)
  let B₀ (i : ℕ) (h : Fin (H i)) := affineValue ((L i).b₀ h) ((L i).b h) (center i)
  let A (i : ℕ) (h : Fin (H i)) (k : Fin (a + b)) :=
    if center i k then -(L i).a h k else 0
  let B (i : ℕ) (h : Fin (H i)) (k : Fin (a + b)) :=
    if center i k then -(L i).b h k else 1
  let q (i : ℕ) (k : Fin (a + b)) : ℝ := if center i k then 0 else 1
  have hdown (i : ℕ) (bits : Fin (a + b) → Bool)
      (hbits : bits ∈ centerDownset (S i) (T i)) :
      ∀ k, bits k = true → center i k = true :=
    (center_downset_iff (S i) (T i) bits).mpr (Finset.mem_filter.mp hbits).2
  have hscore (i : ℕ) (bits : Fin (a + b) → Bool)
      (hbits : bits ∈ centerDownset (S i) (T i)) :
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
  apply glue_positive_affine_ratios N H (fun i ↦ starCell (S i) (T i))
    (fun i ↦ centerDownset (S i) (T i)) (fun bits ↦ outputSign (f bits)) A₀ B₀ A B q
  · intro i _ h
    exact (L i).positive h (center i)
  · intro i _ h k
    exact (centerDeletion_denominator ((L i).b₀ h) ((L i).b h) (center i)
      ((L i).positive h) ((L i).negative h)).2 k
  · intro i _ k
    exact centerPenalty_nonneg (center i) k
  · intro i _
    exact starCell_subset_downset (S i) (T i)
  · intro i hi bits hbits
    rw [hscore i bits (starCell_subset_downset (S i) (T i) hbits)]
    exact (L i).sign_center (S i) (T i) f (hlocal i hi) bits hbits
  · intro i hi j hj bits hbits hd
    rw [hscore i bits hd]
    obtain ⟨hXS, hYT⟩ := (Finset.mem_filter.mp hd).2
    obtain ⟨hR, hU⟩ := (Finset.mem_filter.mp hbits).2
    rcases descending_center_geometry hXS hYT (horder i hi j hj) hR hU with
      hleft | hright | hcell
    · rw [(L i).zero_center_left (S i) (T i) bits hleft]
      simp
    · rw [(L i).zero_center_right (S i) (T i) bits hright]
      simp
    · exact ((L i).sign_center (S i) (T i) f (hlocal i hi) bits
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩)).le
  · intro i _ bits hbits
    exact (centerPenalty_eq_zero_iff (center i) bits).mpr (hdown i bits hbits)
  · intro i _ bits hbits
    apply centerPenalty_pos (center i) bits
    intro h
    apply hbits
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (center_downset_iff (S i) (T i) bits).mp h⟩

end AxisZeroGluing
end HeadComplexity
