import HeadComplexity.Results.AffineSlab
import HeadComplexity.Polynomial.UnivariateReduction

set_option linter.style.header false

/-!
# Two-block affine grid strips

A split of the coordinates is encoded by a Boolean block indicator. Giving
the two blocks constant coefficients turns an affine strip in their two
Hamming weights into an ordinary affine slab on the Boolean cube.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- Membership in a closed affine strip in the two block-weight statistics.
`side i = true` selects the coefficient `a`, and `side i = false` selects
`b`. -/
noncomputable def twoBlockAffineGridStrip (side : Fin n → Bool)
    (a b c lo hi : ℝ) : (Fin n → Bool) → Bool :=
  affineSlab c (fun i ↦ if side i then a else b) lo hi

/-- Two-block affine strips are literally affine slabs after lifting from the
block-weight grid to the cube. -/
theorem twoBlockAffineGridStrip_eq_affineSlab (side : Fin n → Bool)
    (a b c lo hi : ℝ) :
    twoBlockAffineGridStrip side a b c lo hi =
      affineSlab c (fun i ↦ if side i then a else b) lo hi := rfl

/-- Every two-block affine grid strip has head complexity at most two. -/
theorem HStar_twoBlockAffineGridStrip_le_two (side : Fin n → Bool)
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    HStar n (twoBlockAffineGridStrip side a b c lo hi) ≤ 2 :=
  HStar_affineSlab_le_two c (fun i ↦ if side i then a else b) lo hi hlohi

/-- Exact zero-head branch for two-block affine grid strips. -/
theorem HStar_twoBlockAffineGridStrip_eq_zero_iff (side : Fin n → Bool)
    (a b c lo hi : ℝ) :
    HStar n (twoBlockAffineGridStrip side a b c lo hi) = 0 ↔
      ∀ x y, twoBlockAffineGridStrip side a b c lo hi x =
        twoBlockAffineGridStrip side a b c lo hi y :=
  HStar_affineSlab_eq_zero_iff c (fun i ↦ if side i then a else b) lo hi

/-- Exact one-head branch for two-block affine grid strips. -/
theorem HStar_twoBlockAffineGridStrip_eq_one_iff (side : Fin n → Bool)
    (a b c lo hi : ℝ) :
    HStar n (twoBlockAffineGridStrip side a b c lo hi) = 1 ↔
      (¬ (∀ x y, twoBlockAffineGridStrip side a b c lo hi x =
          twoBlockAffineGridStrip side a b c lo hi y) ∧
        isLTF (twoBlockAffineGridStrip side a b c lo hi)) :=
  HStar_affineSlab_eq_one_iff c (fun i ↦ if side i then a else b) lo hi

/-- A nonconstant two-block affine grid strip which is not an LTF has exact
head complexity two. -/
theorem HStar_twoBlockAffineGridStrip_eq_two (side : Fin n → Bool)
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi)
    (hnconst : ¬ (∀ x y, twoBlockAffineGridStrip side a b c lo hi x =
      twoBlockAffineGridStrip side a b c lo hi y))
    (hnLTF : ¬ isLTF (twoBlockAffineGridStrip side a b c lo hi)) :
    HStar n (twoBlockAffineGridStrip side a b c lo hi) = 2 :=
  HStar_affineSlab_eq_two c (fun i ↦ if side i then a else b) lo hi
    hlohi hnconst hnLTF

/-- The full exact `0/1/2` classification of two-block affine grid strips. -/
theorem HStar_twoBlockAffineGridStrip_classification (side : Fin n → Bool)
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    (HStar n (twoBlockAffineGridStrip side a b c lo hi) = 0 ↔
      ∀ x y, twoBlockAffineGridStrip side a b c lo hi x =
        twoBlockAffineGridStrip side a b c lo hi y) ∧
    (HStar n (twoBlockAffineGridStrip side a b c lo hi) = 1 ↔
      (¬ (∀ x y, twoBlockAffineGridStrip side a b c lo hi x =
          twoBlockAffineGridStrip side a b c lo hi y) ∧
        isLTF (twoBlockAffineGridStrip side a b c lo hi))) ∧
    (HStar n (twoBlockAffineGridStrip side a b c lo hi) = 2 ↔
      (¬ (∀ x y, twoBlockAffineGridStrip side a b c lo hi x =
          twoBlockAffineGridStrip side a b c lo hi y) ∧
        ¬ isLTF (twoBlockAffineGridStrip side a b c lo hi))) :=
  HStar_affineSlab_classification c
    (fun i ↦ if side i then a else b) lo hi hlohi

/-! ## Independent bivariate grid sign degree -/

private theorem hammingWeight_le_length {m : ℕ} (bits : Fin m → Bool) :
    hammingWeight bits ≤ m := by
  unfold hammingWeight
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun i : Fin m ↦ bits i = true) Finset.univ)

/-- Hamming level of the first block in the canonical `p + q` split. -/
noncomputable def firstBlockLevel {p q : ℕ}
    (bits : Fin (p + q) → Bool) : Fin (p + 1) :=
  ⟨hammingWeight (fun i : Fin p ↦ bits (Fin.castAdd q i)),
    Nat.lt_succ_of_le (hammingWeight_le_length _)⟩

/-- Hamming level of the second block in the canonical `p + q` split. -/
noncomputable def secondBlockLevel {p q : ℕ}
    (bits : Fin (p + q) → Bool) : Fin (q + 1) :=
  ⟨hammingWeight (fun j : Fin q ↦ bits (Fin.natAdd p j)),
    Nat.lt_succ_of_le (hammingWeight_le_length _)⟩

/-- Lift a Boolean function on the two-block Hamming grid to the Boolean
cube with consecutive blocks of sizes `p` and `q`. -/
noncomputable def twoBlockGridLift {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) :
    (Fin (p + q) → Bool) → Bool :=
  fun bits ↦ G (firstBlockLevel bits) (secondBlockLevel bits)

private theorem exists_bits_of_block_levels {p q : ℕ}
    (u : Fin (p + 1)) (v : Fin (q + 1)) :
    ∃ bits : Fin (p + q) → Bool,
      firstBlockLevel bits = u ∧ secondBlockLevel bits = v := by
  obtain ⟨x, hx⟩ := exists_hammingWeight_eq (n := p) (Nat.le_of_lt_succ u.isLt)
  obtain ⟨y, hy⟩ := exists_hammingWeight_eq (n := q) (Nat.le_of_lt_succ v.isLt)
  let bits : Fin (p + q) → Bool := Fin.addCases x y
  refine ⟨bits, ?_, ?_⟩
  · apply Fin.ext
    change hammingWeight (fun i : Fin p ↦ bits (Fin.castAdd q i)) = u
    simpa [bits] using hx
  · apply Fin.ext
    change hammingWeight (fun j : Fin q ↦ bits (Fin.natAdd p j)) = v
    simpa [bits] using hy

theorem twoBlockGridLift_constant_iff {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) :
    (∀ x y, twoBlockGridLift G x = twoBlockGridLift G y) ↔
      ∀ u v u' v', G u v = G u' v' := by
  constructor
  · intro h u v u' v'
    obtain ⟨x, hx, hx'⟩ := exists_bits_of_block_levels u v
    obtain ⟨y, hy, hy'⟩ := exists_bits_of_block_levels u' v'
    simpa [twoBlockGridLift, hx, hx', hy, hy'] using h x y
  · intro h x y
    exact h _ _ _ _

/-- Coefficients which are constant on each side of the canonical two-block
split. -/
def canonicalTwoBlockCoeff {p q : ℕ} (a b : ℝ) : Fin (p + q) → ℝ :=
  Fin.addCases (fun _ ↦ a) (fun _ ↦ b)

theorem affineValue_canonicalTwoBlockCoeff {p q : ℕ}
    (a b c : ℝ) (bits : Fin (p + q) → Bool) :
    affineValue c (canonicalTwoBlockCoeff a b) bits =
      a * (firstBlockLevel bits : ℕ) +
        b * (secondBlockLevel bits : ℕ) + c := by
  unfold affineValue canonicalTwoBlockCoeff
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  have hx := hammingWeight_eq_sum
    (fun i : Fin p ↦ bits (Fin.castAdd q i))
  have hy := hammingWeight_eq_sum
    (fun j : Fin q ↦ bits (Fin.natAdd p j))
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hx, ← hy]
  simp only [firstBlockLevel, secondBlockLevel]
  ring

/-- A permutation acting independently inside the two canonical blocks. -/
noncomputable def twoBlockPerm {p q : ℕ}
    (sigma : Equiv.Perm (Fin p)) (tau : Equiv.Perm (Fin q)) :
    Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.symm.trans ((sigma.sumCongr tau).trans finSumFinEquiv)

@[simp] theorem twoBlockPerm_castAdd {p q : ℕ}
    (sigma : Equiv.Perm (Fin p)) (tau : Equiv.Perm (Fin q)) (i : Fin p) :
    twoBlockPerm sigma tau (Fin.castAdd q i) = Fin.castAdd q (sigma i) := by
  simp [twoBlockPerm]

@[simp] theorem twoBlockPerm_natAdd {p q : ℕ}
    (sigma : Equiv.Perm (Fin p)) (tau : Equiv.Perm (Fin q)) (j : Fin q) :
    twoBlockPerm sigma tau (Fin.natAdd p j) = Fin.natAdd p (tau j) := by
  simp [twoBlockPerm]

@[simp] theorem twoBlockPerm_symm {p q : ℕ}
    (sigma : Equiv.Perm (Fin p)) (tau : Equiv.Perm (Fin q)) :
    (twoBlockPerm sigma tau).symm = twoBlockPerm sigma.symm tau.symm := by
  ext i
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective i
  · simp [twoBlockPerm]
  · simp [twoBlockPerm]

@[simp] theorem firstBlockLevel_comp_twoBlockPerm {p q : ℕ}
    (sigma : Equiv.Perm (Fin p)) (tau : Equiv.Perm (Fin q))
    (bits : Fin (p + q) → Bool) :
    firstBlockLevel (fun i ↦ bits (twoBlockPerm sigma tau i)) =
      firstBlockLevel bits := by
  apply Fin.ext
  change hammingWeight
      (fun i : Fin p ↦ bits (twoBlockPerm sigma tau (Fin.castAdd q i))) =
    hammingWeight (fun i : Fin p ↦ bits (Fin.castAdd q i))
  simp only [twoBlockPerm_castAdd]
  exact hammingWeight_comp_perm (fun i : Fin p ↦ bits (Fin.castAdd q i)) sigma

@[simp] theorem secondBlockLevel_comp_twoBlockPerm {p q : ℕ}
    (sigma : Equiv.Perm (Fin p)) (tau : Equiv.Perm (Fin q))
    (bits : Fin (p + q) → Bool) :
    secondBlockLevel (fun i ↦ bits (twoBlockPerm sigma tau i)) =
      secondBlockLevel bits := by
  apply Fin.ext
  change hammingWeight
      (fun j : Fin q ↦ bits (twoBlockPerm sigma tau (Fin.natAdd p j))) =
    hammingWeight (fun j : Fin q ↦ bits (Fin.natAdd p j))
  simp only [twoBlockPerm_natAdd]
  exact hammingWeight_comp_perm (fun j : Fin q ↦ bits (Fin.natAdd p j)) tau

/-- Coefficients obtained by summing a separator over all permutations inside
the two blocks. -/
noncomputable def blockAverageCoeff {p q : ℕ}
    (cs : Fin (p + q) → ℝ) (i : Fin (p + q)) : ℝ :=
  ∑ sigma : Equiv.Perm (Fin p), ∑ tau : Equiv.Perm (Fin q),
    cs ((twoBlockPerm sigma tau).symm i)

private def rightSwapPerm {p : ℕ} (i k : Fin p) :
    Equiv.Perm (Equiv.Perm (Fin p)) where
  toFun sigma := sigma.trans (Equiv.swap i k)
  invFun sigma := sigma.trans (Equiv.swap i k)
  left_inv sigma := by
    ext j
    simp
  right_inv sigma := by
    ext j
    simp

theorem blockAverageCoeff_castAdd_eq {p q : ℕ}
    (cs : Fin (p + q) → ℝ) (i k : Fin p) :
    blockAverageCoeff cs (Fin.castAdd q i) =
      blockAverageCoeff cs (Fin.castAdd q k) := by
  unfold blockAverageCoeff
  simp only [twoBlockPerm_symm, twoBlockPerm_castAdd]
  simp_rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  have h := Equiv.sum_comp (rightSwapPerm i k)
    (fun sigma : Equiv.Perm (Fin p) ↦
      (Fintype.card (Equiv.Perm (Fin q)) : ℝ) *
        cs (Fin.castAdd q (sigma.symm i)))
  simpa [rightSwapPerm] using h.symm

theorem blockAverageCoeff_natAdd_eq {p q : ℕ}
    (cs : Fin (p + q) → ℝ) (j k : Fin q) :
    blockAverageCoeff cs (Fin.natAdd p j) =
      blockAverageCoeff cs (Fin.natAdd p k) := by
  unfold blockAverageCoeff
  simp only [twoBlockPerm_symm, twoBlockPerm_natAdd]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  have h := Equiv.sum_comp (rightSwapPerm j k)
    (fun tau : Equiv.Perm (Fin q) ↦ cs (Fin.natAdd p (tau.symm j)))
  simpa [rightSwapPerm] using h.symm

noncomputable def blockAverageConstant {p q : ℕ} (c : ℝ) : ℝ :=
  ∑ _sigma : Equiv.Perm (Fin p), ∑ _tau : Equiv.Perm (Fin q), c

theorem affineValue_blockAverage {p q : ℕ} (c : ℝ)
    (cs : Fin (p + q) → ℝ) (bits : Fin (p + q) → Bool) :
    affineValue (blockAverageConstant (p := p) (q := q) c)
        (blockAverageCoeff cs) bits =
      ∑ sigma : Equiv.Perm (Fin p), ∑ tau : Equiv.Perm (Fin q),
        affineValue c cs (fun i ↦ bits (twoBlockPerm sigma tau i)) := by
  unfold affineValue blockAverageConstant blockAverageCoeff
  simp_rw [Finset.sum_add_distrib]
  congr 1
  have hreindex : ∀ (sigma : Equiv.Perm (Fin p))
      (tau : Equiv.Perm (Fin q)),
      (∑ i, cs i * boolToReal (bits (twoBlockPerm sigma tau i))) =
        ∑ i, cs ((twoBlockPerm sigma tau).symm i) * boolToReal (bits i) := by
    intro sigma tau
    simpa only [Equiv.apply_symm_apply] using
      (Equiv.sum_comp (twoBlockPerm sigma tau).symm
        (fun i ↦ cs i * boolToReal (bits (twoBlockPerm sigma tau i)))).symm
  simp_rw [hreindex]
  calc
    (∑ i, (∑ sigma, ∑ tau, cs ((twoBlockPerm sigma tau).symm i)) *
        boolToReal (bits i)) =
        ∑ i, ∑ sigma, ∑ tau,
          cs ((twoBlockPerm sigma tau).symm i) * boolToReal (bits i) := by
            simp_rw [Finset.sum_mul]
    _ = ∑ sigma, ∑ i, ∑ tau,
          cs ((twoBlockPerm sigma tau).symm i) * boolToReal (bits i) := by
            rw [Finset.sum_comm]
    _ = ∑ sigma, ∑ tau, ∑ i,
          cs ((twoBlockPerm sigma tau).symm i) * boolToReal (bits i) := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            rw [Finset.sum_comm]

private theorem exists_strict_affine_separator {m : ℕ}
    {f : (Fin m → Bool) → Bool} (hf : isLTF f) :
    ∃ (c : ℝ) (cs : Fin m → ℝ), ∀ bits,
      (f bits = true → 0 < affineValue c cs bits) ∧
      (f bits = false → affineValue c cs bits < 0) := by
  classical
  obtain ⟨c, cs, hsign⟩ := hf
  let T : Finset (Fin m → Bool) := Finset.univ.filter fun bits ↦ f bits = true
  obtain ⟨eps, heps, hepslt⟩ :
      ∃ eps : ℝ, 0 < eps ∧
        ∀ bits, f bits = true → eps < affineValue c cs bits := by
    by_cases hT : T.Nonempty
    · refine ⟨T.inf' hT (affineValue c cs) / 2, ?_, ?_⟩
      · apply half_pos
        rw [Finset.lt_inf'_iff]
        intro bits hbits
        exact (hsign bits).mpr (Finset.mem_filter.mp hbits).2
      · intro bits hbits
        have hmem : bits ∈ T := by simp [T, hbits]
        have hle := Finset.inf'_le (affineValue c cs) hmem
        have hpos := (hsign bits).mpr hbits
        have hinfpos : 0 < T.inf' hT (affineValue c cs) := by
          rw [Finset.lt_inf'_iff]
          intro y hy
          exact (hsign y).mpr (Finset.mem_filter.mp hy).2
        linarith
    · refine ⟨1, one_pos, ?_⟩
      intro bits hbits
      exact (hT ⟨bits, by simp [T, hbits]⟩).elim
  refine ⟨c - eps, cs, fun bits ↦ ?_⟩
  have hvalue : affineValue (c - eps) cs bits = affineValue c cs bits - eps := by
    unfold affineValue
    ring
  constructor
  · intro htrue
    rw [hvalue]
    linarith [hepslt bits htrue]
  · intro hfalse
    rw [hvalue]
    have hnonpos : affineValue c cs bits ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have := (hsign bits).mp hpos
      simp [hfalse] at this
    linarith

/-- The real point `(u,v)` associated with a two-dimensional finite grid
index. -/
def bivariateGridPoint {p q : ℕ} (u : Fin (p + 1)) (v : Fin (q + 1)) :
    Fin 2 → ℝ :=
  ![(u : ℝ), (v : ℝ)]

/-- Strict sign representation of a Boolean function on a finite rectangular
integer grid. -/
def StrictBivariateGridSignRep {p q : ℕ}
    (P : MvPolynomial (Fin 2) ℝ)
    (G : Fin (p + 1) → Fin (q + 1) → Bool) : Prop :=
  ∀ u v,
    (G u v = true → 0 < eval (bivariateGridPoint u v) P) ∧
    (G u v = false → eval (bivariateGridPoint u v) P < 0)

/-- A rectangular grid function has strict bivariate sign degree at most
`d`. -/
def BivariateGridThresholdDegLE {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) (d : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ,
    P.totalDegree ≤ d ∧ StrictBivariateGridSignRep P G

/-- The least strict bivariate sign degree. The fallback branch is irrelevant
whenever a certificate is supplied, as it is below for affine strips. -/
noncomputable def bivariateGridThresholdDeg {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) : ℕ := by
  classical
  exact if h : ∃ d, BivariateGridThresholdDegLE G d then Nat.find h else 0

theorem bivariateGridThresholdDeg_spec_of_exists {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool)
    (h : ∃ d, BivariateGridThresholdDegLE G d) :
    BivariateGridThresholdDegLE G (bivariateGridThresholdDeg G) := by
  classical
  unfold bivariateGridThresholdDeg
  rw [dif_pos h]
  exact Nat.find_spec h

theorem bivariateGridThresholdDeg_le {p q d : ℕ}
    {G : Fin (p + 1) → Fin (q + 1) → Bool}
    (h : BivariateGridThresholdDegLE G d) :
    bivariateGridThresholdDeg G ≤ d := by
  classical
  have hex : ∃ e, BivariateGridThresholdDegLE G e := ⟨d, h⟩
  unfold bivariateGridThresholdDeg
  rw [dif_pos hex]
  exact Nat.find_min' hex h

/-- The affine-strip predicate on the rectangular integer grid. -/
noncomputable def affineGridStrip {p q : ℕ} (a b c lo hi : ℝ)
    (u : Fin (p + 1)) (v : Fin (q + 1)) : Bool :=
  decide (lo ≤ a * (u : ℝ) + b * (v : ℝ) + c ∧
    a * (u : ℝ) + b * (v : ℝ) + c ≤ hi)

/-- An affine polynomial in the two grid coordinates. -/
noncomputable def bivariateAffinePolynomial (a b c : ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  C c + C a * X 0 + C b * X 1

@[simp] theorem bivariateAffinePolynomial_eval {p q : ℕ}
    (a b c : ℝ) (u : Fin (p + 1)) (v : Fin (q + 1)) :
    eval (bivariateGridPoint u v) (bivariateAffinePolynomial a b c) =
      a * (u : ℝ) + b * (v : ℝ) + c := by
  simp [bivariateAffinePolynomial, bivariateGridPoint]
  ring

theorem bivariateAffinePolynomial_totalDegree_le_one (a b c : ℝ) :
    (bivariateAffinePolynomial a b c).totalDegree ≤ 1 := by
  unfold bivariateAffinePolynomial
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · refine (totalDegree_mul _ _).trans ?_
      simp
  · refine (totalDegree_mul _ _).trans ?_
    simp

private theorem finsupp_fin_two_eq_of_sum_le_one (d : Fin 2 →₀ ℕ)
    (h : ∑ i, d i ≤ 1) :
    d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
  rw [Fin.sum_univ_two] at h
  have hcases :
      (d 0 = 0 ∧ d 1 = 0) ∨
      (d 0 = 1 ∧ d 1 = 0) ∨
      (d 0 = 0 ∧ d 1 = 1) := by omega
  rcases hcases with hzero | hfirst | hsecond
  · left
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [hzero.1]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hzero.2]
  · right; left
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [hfirst.1]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hfirst.2]
  · right; right
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [hsecond.1]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hsecond.2]

/-- Every bivariate polynomial of total degree at most one is affine. -/
theorem eq_bivariateAffinePolynomial_of_totalDegree_le_one
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 1) :
    P = bivariateAffinePolynomial
      (P.coeff (Finsupp.single 0 1))
      (P.coeff (Finsupp.single 1 1)) (P.coeff 0) := by
  have hzero_first : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
    simp at this
  have hzero_second : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) h
    simp at this
  have hfirst_second :
      (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
    simp at this
  ext d
  by_cases hd : d ∈ P.support
  · have hsum : ∑ i, d i ≤ 1 := by
      simpa [Finsupp.sum_fintype] using (le_totalDegree hd).trans hP
    rcases finsupp_fin_two_eq_of_sum_le_one d hsum with rfl | rfl | rfl <;>
      simp [bivariateAffinePolynomial, hzero_first, hzero_second]
  · have hcoeff : P.coeff d = 0 := by
      simpa [mem_support_iff] using hd
    by_cases hzero : d = 0
    · subst d
      simp [bivariateAffinePolynomial, hcoeff]
    · by_cases hfirst : d = Finsupp.single 0 1
      · subst d
        simp [bivariateAffinePolynomial, hcoeff, hzero_first]
      · by_cases hsecond : d = Finsupp.single 1 1
        · subst d
          simp [bivariateAffinePolynomial, hcoeff, hzero_second]
        · have hsum : 2 ≤ ∑ i, d i := by
            by_contra hnot
            push Not at hnot
            have := finsupp_fin_two_eq_of_sum_le_one d (by omega)
            rcases this with h | h | h <;> contradiction
          have hXzero :
              (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ).coeff d = 0 := by
            rw [coeff_X]
            simp [Ne.symm hfirst]
          have hXone :
              (X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).coeff d = 0 := by
            rw [coeff_X]
            simp [Ne.symm hsecond]
          simp [bivariateAffinePolynomial, hcoeff, hXzero, hXone,
            Ne.symm hzero]

/-- A strict affine separator on the finite grid. -/
def IsBivariateGridLTF {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) : Prop :=
  ∃ a b c : ℝ, ∀ u v,
    (G u v = true → 0 < a * (u : ℝ) + b * (v : ℝ) + c) ∧
    (G u v = false → a * (u : ℝ) + b * (v : ℝ) + c < 0)

/-- A strict affine separator on the block-weight grid lifts to an LTF on the
Boolean cube. -/
theorem IsBivariateGridLTF.isLTF_twoBlockGridLift {p q : ℕ}
    {G : Fin (p + 1) → Fin (q + 1) → Bool}
    (h : IsBivariateGridLTF G) : isLTF (twoBlockGridLift G) := by
  obtain ⟨a, b, c, hsep⟩ := h
  refine ⟨c, canonicalTwoBlockCoeff a b, fun bits ↦ ?_⟩
  change 0 < affineValue c (canonicalTwoBlockCoeff a b) bits ↔
    twoBlockGridLift G bits = true
  rw [affineValue_canonicalTwoBlockCoeff]
  change 0 < a * (firstBlockLevel bits : ℕ) +
      b * (secondBlockLevel bits : ℕ) + c ↔
    G (firstBlockLevel bits) (secondBlockLevel bits) = true
  cases hG : G (firstBlockLevel bits) (secondBlockLevel bits)
  · simp only [Bool.false_eq_true, iff_false]
    exact not_lt_of_ge (le_of_lt ((hsep _ _).2 hG))
  · simp only [iff_true]
    exact (hsep _ _).1 hG

/-- Conversely, for nonempty blocks, averaging a strict cube separator over
all within-block permutations produces a strict affine separator on the
block-weight grid. -/
theorem isBivariateGridLTF_of_isLTF_twoBlockGridLift {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    {G : Fin (p + 1) → Fin (q + 1) → Bool}
    (h : isLTF (twoBlockGridLift G)) : IsBivariateGridLTF G := by
  obtain ⟨c, cs, hstrict⟩ := exists_strict_affine_separator h
  let i₀ : Fin p := ⟨0, hp⟩
  let j₀ : Fin q := ⟨0, hq⟩
  let cbar : ℝ := blockAverageConstant (p := p) (q := q) c
  let csbar : Fin (p + q) → ℝ := blockAverageCoeff cs
  let a : ℝ := csbar (Fin.castAdd q i₀)
  let b : ℝ := csbar (Fin.natAdd p j₀)
  have hcsbar : csbar = canonicalTwoBlockCoeff a b := by
    funext k
    induction k using Fin.addCases with
    | left i =>
        dsimp [csbar, a, canonicalTwoBlockCoeff]
        simpa only [Fin.addCases_left] using
          blockAverageCoeff_castAdd_eq cs i i₀
    | right j =>
        dsimp [csbar, b, canonicalTwoBlockCoeff]
        simpa only [Fin.addCases_right] using
          blockAverageCoeff_natAdd_eq cs j j₀
  refine ⟨a, b, cbar, fun u v ↦ ?_⟩
  obtain ⟨bits, hu, hv⟩ := exists_bits_of_block_levels u v
  have havgform : affineValue cbar csbar bits =
      a * (u : ℝ) + b * (v : ℝ) + cbar := by
    rw [hcsbar, affineValue_canonicalTwoBlockCoeff, hu, hv]
  constructor
  · intro htrue
    rw [← havgform, affineValue_blockAverage]
    refine Finset.sum_pos (fun sigma _ ↦ ?_) Finset.univ_nonempty
    refine Finset.sum_pos (fun tau _ ↦ ?_) Finset.univ_nonempty
    apply (hstrict (fun i ↦ bits (twoBlockPerm sigma tau i))).1
    change G
      (firstBlockLevel (fun i ↦ bits (twoBlockPerm sigma tau i)))
      (secondBlockLevel (fun i ↦ bits (twoBlockPerm sigma tau i))) = true
    simpa [hu, hv] using htrue
  · intro hfalse
    rw [← havgform, affineValue_blockAverage]
    refine Finset.sum_neg (fun sigma _ ↦ ?_) Finset.univ_nonempty
    refine Finset.sum_neg (fun tau _ ↦ ?_) Finset.univ_nonempty
    apply (hstrict (fun i ↦ bits (twoBlockPerm sigma tau i))).2
    change G
      (firstBlockLevel (fun i ↦ bits (twoBlockPerm sigma tau i)))
      (secondBlockLevel (fun i ↦ bits (twoBlockPerm sigma tau i))) = false
    simpa [hu, hv] using hfalse

/-- The canonical cube lift of an affine grid strip is exactly an affine slab
whose coefficients are constant on the two blocks. -/
theorem twoBlockGridLift_affineGridStrip {p q : ℕ}
    (a b c lo hi : ℝ) :
    twoBlockGridLift (affineGridStrip (p := p) (q := q) a b c lo hi) =
      affineSlab c (canonicalTwoBlockCoeff a b) lo hi := by
  funext bits
  simp only [twoBlockGridLift, affineGridStrip, affineSlab,
    decide_eq_decide]
  rw [affineValue_canonicalTwoBlockCoeff]

theorem bivariateGridThresholdDegLE_one_iff {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) :
    BivariateGridThresholdDegLE G 1 ↔ IsBivariateGridLTF G := by
  constructor
  · rintro ⟨P, hP, hsign⟩
    let a := P.coeff (Finsupp.single 0 1)
    let b := P.coeff (Finsupp.single 1 1)
    let c := P.coeff 0
    refine ⟨a, b, c, fun u v ↦ ?_⟩
    have heq := eq_bivariateAffinePolynomial_of_totalDegree_le_one P hP
    have heval : eval (bivariateGridPoint u v) P =
        a * (u : ℝ) + b * (v : ℝ) + c := by
      rw [heq]
      exact bivariateAffinePolynomial_eval a b c u v
    exact ⟨fun h ↦ heval ▸ (hsign u v).1 h,
      fun h ↦ heval ▸ (hsign u v).2 h⟩
  · rintro ⟨a, b, c, hsep⟩
    refine ⟨bivariateAffinePolynomial a b c,
      bivariateAffinePolynomial_totalDegree_le_one a b c, ?_⟩
    intro u v
    simpa using hsep u v

theorem bivariateGridThresholdDegLE_zero_iff {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool) :
    BivariateGridThresholdDegLE G 0 ↔
      ∀ u v u' v', G u v = G u' v' := by
  constructor
  · rintro ⟨P, hP, hsign⟩
    have hdegree : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hP
    have hPeq : P = C (P.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp hdegree
    intro u v u' v'
    have huv : eval (bivariateGridPoint u v) P = P.coeff 0 := by
      rw [hPeq]
      simp
    have huv' : eval (bivariateGridPoint u' v') P = P.coeff 0 := by
      rw [hPeq]
      simp
    cases hu : G u v <;> cases hu' : G u' v'
    · rfl
    · exfalso
      have hneg := (hsign u v).2 hu
      have hpos := (hsign u' v').1 hu'
      rw [huv] at hneg
      rw [huv'] at hpos
      linarith
    · exfalso
      have hpos := (hsign u v).1 hu
      have hneg := (hsign u' v').2 hu'
      rw [huv] at hpos
      rw [huv'] at hneg
      linarith
    · rfl
  · intro hconst
    let z : ℝ := if G 0 0 then 1 else -1
    refine ⟨C z, by simp, ?_⟩
    intro u v
    have hval : G u v = G 0 0 := hconst u v 0 0
    cases hbase : G 0 0 <;> simp [z, hval, hbase]

theorem bivariateGridThresholdDeg_eq_zero_iff_of_exists {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool)
    (hex : ∃ d, BivariateGridThresholdDegLE G d) :
    bivariateGridThresholdDeg G = 0 ↔
      ∀ u v u' v', G u v = G u' v' := by
  constructor
  · intro hzero
    apply (bivariateGridThresholdDegLE_zero_iff G).mp
    simpa [hzero] using bivariateGridThresholdDeg_spec_of_exists G hex
  · intro hconst
    apply Nat.eq_zero_of_le_zero
    apply bivariateGridThresholdDeg_le
    exact (bivariateGridThresholdDegLE_zero_iff G).mpr hconst

theorem bivariateGridThresholdDeg_eq_one_of_nonconstant_ltf {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool)
    (hnconst : ¬ (∀ u v u' v', G u v = G u' v'))
    (hltf : IsBivariateGridLTF G) :
    bivariateGridThresholdDeg G = 1 := by
  have hone : BivariateGridThresholdDegLE G 1 :=
    (bivariateGridThresholdDegLE_one_iff G).mpr hltf
  have hle := bivariateGridThresholdDeg_le hone
  have hne : bivariateGridThresholdDeg G ≠ 0 := by
    intro hzero
    exact hnconst ((bivariateGridThresholdDeg_eq_zero_iff_of_exists G
      ⟨1, hone⟩).mp hzero)
  omega

theorem bivariateGridThresholdDeg_eq_two_of_not_ltf {p q : ℕ}
    (G : Fin (p + 1) → Fin (q + 1) → Bool)
    (htwo : BivariateGridThresholdDegLE G 2)
    (hnconst : ¬ (∀ u v u' v', G u v = G u' v'))
    (hnltf : ¬ IsBivariateGridLTF G) :
    bivariateGridThresholdDeg G = 2 := by
  have hle := bivariateGridThresholdDeg_le htwo
  have hspec := bivariateGridThresholdDeg_spec_of_exists G ⟨2, htwo⟩
  have hnezero : bivariateGridThresholdDeg G ≠ 0 := by
    intro hzero
    exact hnconst ((bivariateGridThresholdDeg_eq_zero_iff_of_exists G
      ⟨2, htwo⟩).mp hzero)
  have hneone : bivariateGridThresholdDeg G ≠ 1 := by
    intro hone
    apply hnltf
    apply (bivariateGridThresholdDegLE_one_iff G).mp
    simpa [hone] using hspec
  omega

private theorem interval_iff_abs_sub_midpoint_le {lo hi t : ℝ} :
    (lo ≤ t ∧ t ≤ hi) ↔
      |t - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem exists_strict_grid_radius {p q : ℕ}
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : Fin (p + 1), ∀ v : Fin (q + 1),
      (affineGridStrip a b c lo hi u v = true →
        |a * (u : ℝ) + b * (v : ℝ) + c - (lo + hi) / 2| < r) ∧
      (affineGridStrip a b c lo hi u v = false →
        r < |a * (u : ℝ) + b * (v : ℝ) + c - (lo + hi) / 2|) := by
  classical
  let w : Fin (p + 1) × Fin (q + 1) → ℝ := fun z ↦
    |a * (z.1 : ℝ) + b * (z.2 : ℝ) + c - (lo + hi) / 2|
  let outside : Finset (Fin (p + 1) × Fin (q + 1)) :=
    Finset.univ.filter fun z ↦ affineGridStrip a b c lo hi z.1 z.2 = false
  by_cases hout : outside.Nonempty
  · obtain ⟨nearest, hnearest, hmin⟩ := outside.exists_min_image w hout
    have hnearest_false :
        affineGridStrip a b c lo hi nearest.1 nearest.2 = false :=
      (Finset.mem_filter.mp hnearest).2
    have hradius_nonneg : 0 ≤ (hi - lo) / 2 := by linarith
    have hradius_lt : (hi - lo) / 2 < w nearest := by
      apply lt_of_not_ge
      intro hle
      have htrue : affineGridStrip a b c lo hi nearest.1 nearest.2 = true := by
        simp only [affineGridStrip, decide_eq_true_eq]
        exact interval_iff_abs_sub_midpoint_le.mpr hle
      simp [hnearest_false] at htrue
    let r : ℝ := ((hi - lo) / 2 + w nearest) / 2
    have hradius_r : (hi - lo) / 2 < r := by dsimp [r]; linarith
    have hr_nearest : r < w nearest := by dsimp [r]; linarith
    refine ⟨r, hradius_nonneg.trans_lt hradius_r, ?_⟩
    intro u v
    constructor
    · intro htrue
      have hle :
          |a * (u : ℝ) + b * (v : ℝ) + c - (lo + hi) / 2| ≤
            (hi - lo) / 2 := by
        apply interval_iff_abs_sub_midpoint_le.mp
        simpa [affineGridStrip] using htrue
      exact hle.trans_lt hradius_r
    · intro hfalse
      have hmem : (u, v) ∈ outside := by simp [outside, hfalse]
      exact hr_nearest.trans_le (hmin (u, v) hmem)
  · have hall : ∀ u : Fin (p + 1), ∀ v : Fin (q + 1),
        affineGridStrip a b c lo hi u v = true := by
      intro u v
      cases hval : affineGridStrip a b c lo hi u v with
      | false =>
          exact (hout ⟨(u, v), by simp [outside, hval]⟩).elim
      | true => rfl
    let r : ℝ := 1 + ∑ z : Fin (p + 1) × Fin (q + 1), w z
    have hr : 0 < r := by
      dsimp [r]
      have : 0 ≤ ∑ z : Fin (p + 1) × Fin (q + 1), w z := by positivity
      linarith
    refine ⟨r, hr, ?_⟩
    intro u v
    constructor
    · intro _
      have hnonneg : ∀ z ∈ (Finset.univ :
          Finset (Fin (p + 1) × Fin (q + 1))), 0 ≤ w z := by
        intro z hz
        exact abs_nonneg _
      have hle : w (u, v) ≤ ∑ z : Fin (p + 1) × Fin (q + 1), w z :=
        Finset.single_le_sum hnonneg (Finset.mem_univ (u, v))
      dsimp [r]
      dsimp [w] at hle ⊢
      linarith
    · intro hfalse
      exact (Bool.false_ne_true (hfalse.symm.trans (hall u v))).elim

/-- Every affine strip on a finite rectangular grid has a strict quadratic
sign representation. -/
theorem affineGridStrip_thresholdDegLE_two {p q : ℕ}
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    BivariateGridThresholdDegLE (affineGridStrip (p := p) (q := q)
      a b c lo hi) 2 := by
  obtain ⟨r, hr, hsep⟩ :=
    exists_strict_grid_radius (p := p) (q := q) a b c lo hi hlohi
  let W := bivariateAffinePolynomial a b (c - (lo + hi) / 2)
  let P : MvPolynomial (Fin 2) ℝ := C (r ^ 2) - W ^ 2
  refine ⟨P, ?_, ?_⟩
  · dsimp [P]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_C]
      omega
    · refine (totalDegree_pow _ _).trans ?_
      simpa [W] using Nat.mul_le_mul_left 2
        (bivariateAffinePolynomial_totalDegree_le_one a b
          (c - (lo + hi) / 2))
  · intro u v
    have hW : eval (bivariateGridPoint u v) W =
        a * (u : ℝ) + b * (v : ℝ) + c - (lo + hi) / 2 := by
      simp [W]
      ring
    have hP : eval (bivariateGridPoint u v) P =
        r ^ 2 - (a * (u : ℝ) + b * (v : ℝ) + c -
          (lo + hi) / 2) ^ 2 := by
      simp [P, hW]
    constructor
    · intro htrue
      rw [hP]
      have habs := (hsep u v).1 htrue
      have hsquare :
          (a * (u : ℝ) + b * (v : ℝ) + c - (lo + hi) / 2) ^ 2 <
            r ^ 2 := by
        apply sq_lt_sq.mpr
        rwa [abs_of_pos hr]
      linarith
    · intro hfalse
      rw [hP]
      have hout := (hsep u v).2 hfalse
      have hsquare : r ^ 2 <
          (a * (u : ℝ) + b * (v : ℝ) + c - (lo + hi) / 2) ^ 2 := by
        apply sq_lt_sq.mpr
        simpa [abs_of_pos hr] using hout
      linarith

/-- The strict bivariate grid sign degree of an affine strip is at most two. -/
theorem bivariateGridThresholdDeg_affineGridStrip_le_two {p q : ℕ}
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    bivariateGridThresholdDeg (affineGridStrip (p := p) (q := q)
      a b c lo hi) ≤ 2 :=
  bivariateGridThresholdDeg_le
    (affineGridStrip_thresholdDegLE_two a b c lo hi hlohi)

/-- Whenever a two-block grid lift has the independent two-head upper bound,
its head complexity is at most the strict bivariate grid sign degree. -/
theorem HStar_twoBlockGridLift_le_bivariateGridThresholdDeg_of_le_two
    {p q : ℕ} (G : Fin (p + 1) → Fin (q + 1) → Bool)
    (hgridTwo : BivariateGridThresholdDegLE G 2)
    (hheadTwo : HStar (p + q) (twoBlockGridLift G) ≤ 2) :
    HStar (p + q) (twoBlockGridLift G) ≤ bivariateGridThresholdDeg G := by
  have hdle := bivariateGridThresholdDeg_le hgridTwo
  have hspec := bivariateGridThresholdDeg_spec_of_exists G ⟨2, hgridTwo⟩
  have hcases : bivariateGridThresholdDeg G = 0 ∨
      bivariateGridThresholdDeg G = 1 ∨
      bivariateGridThresholdDeg G = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hconstG : ∀ u v u' v', G u v = G u' v' :=
      (bivariateGridThresholdDegLE_zero_iff G).mp (by simpa [hzero] using hspec)
    have hconstLift := (twoBlockGridLift_constant_iff G).mpr hconstG
    rw [(HStar_eq_zero_iff _).mpr hconstLift, hzero]
  · have hgridLTF : IsBivariateGridLTF G :=
      (bivariateGridThresholdDegLE_one_iff G).mp (by simpa [hone] using hspec)
    have hliftLTF := hgridLTF.isLTF_twoBlockGridLift
    by_cases hconst : ∀ x y, twoBlockGridLift G x = twoBlockGridLift G y
    · rw [(HStar_eq_zero_iff _).mpr hconst, hone]
      omega
    · rw [(HStar_eq_one_iff _).mpr ⟨hconst, hliftLTF⟩, hone]
  · rwa [htwo]

/-- For affine grid strips, the independent grid sign degree always gives an
upper bound on the exact head complexity of the cube lift. -/
theorem HStar_affineGridStrip_le_bivariateGridThresholdDeg {p q : ℕ}
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    HStar (p + q)
        (twoBlockGridLift (affineGridStrip (p := p) (q := q) a b c lo hi)) ≤
      bivariateGridThresholdDeg
        (affineGridStrip (p := p) (q := q) a b c lo hi) := by
  apply HStar_twoBlockGridLift_le_bivariateGridThresholdDeg_of_le_two
  · exact affineGridStrip_thresholdDegLE_two a b c lo hi hlohi
  · rw [twoBlockGridLift_affineGridStrip]
    exact HStar_affineSlab_le_two c (canonicalTwoBlockCoeff a b) lo hi hlohi

/-- The only remaining ingredient for the full grid-degree equality is the
reverse LTF transport, obtained mathematically by averaging a cube separator
over permutations within the two blocks. -/
theorem HStar_affineGridStrip_eq_bivariateGridThresholdDeg_of_ltf_reverse
    {p q : ℕ} (a b c lo hi : ℝ) (hlohi : lo ≤ hi)
    (hltfReverse :
      isLTF (twoBlockGridLift
        (affineGridStrip (p := p) (q := q) a b c lo hi)) →
      IsBivariateGridLTF (affineGridStrip (p := p) (q := q)
        a b c lo hi)) :
    HStar (p + q)
        (twoBlockGridLift (affineGridStrip (p := p) (q := q) a b c lo hi)) =
      bivariateGridThresholdDeg
        (affineGridStrip (p := p) (q := q) a b c lo hi) := by
  let G := affineGridStrip (p := p) (q := q) a b c lo hi
  let F := twoBlockGridLift G
  have htwoGrid : BivariateGridThresholdDegLE G 2 :=
    affineGridStrip_thresholdDegLE_two a b c lo hi hlohi
  have htwoHead : HStar (p + q) F ≤ 2 := by
    dsimp [F, G]
    rw [twoBlockGridLift_affineGridStrip]
    exact HStar_affineSlab_le_two c (canonicalTwoBlockCoeff a b) lo hi hlohi
  by_cases hconst : ∀ x y, F x = F y
  · have hgridconst : ∀ u v u' v', G u v = G u' v' :=
      (twoBlockGridLift_constant_iff G).mp hconst
    rw [(HStar_eq_zero_iff F).mpr hconst]
    exact (bivariateGridThresholdDeg_eq_zero_iff_of_exists G
      ⟨2, htwoGrid⟩).mpr hgridconst |>.symm
  · by_cases hltf : isLTF F
    · have hgridltf : IsBivariateGridLTF G := by
        apply hltfReverse
        exact hltf
      rw [(HStar_eq_one_iff F).mpr ⟨hconst, hltf⟩]
      exact (bivariateGridThresholdDeg_eq_one_of_nonconstant_ltf G
        (fun hg ↦ hconst ((twoBlockGridLift_constant_iff G).mpr hg))
        hgridltf).symm
    · have hgridnltf : ¬ IsBivariateGridLTF G :=
        fun hg ↦ hltf hg.isLTF_twoBlockGridLift
      have hhead : HStar (p + q) F = 2 := by
        have hnezero : HStar (p + q) F ≠ 0 :=
          fun hz ↦ hconst ((HStar_eq_zero_iff F).mp hz)
        have hneone : HStar (p + q) F ≠ 1 :=
          fun ho ↦ hltf ((HStar_eq_one_iff F).mp ho).2
        omega
      rw [hhead]
      exact (bivariateGridThresholdDeg_eq_two_of_not_ltf G htwoGrid
        (fun hg ↦ hconst ((twoBlockGridLift_constant_iff G).mpr hg))
        hgridnltf).symm

/-- **Two-block affine grid-strip exactness.** For two nonempty blocks, head
complexity of the lifted affine strip equals its least strict bivariate grid
sign degree. -/
theorem HStar_affineGridStrip_eq_bivariateGridThresholdDeg
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (a b c lo hi : ℝ) (hlohi : lo ≤ hi) :
    HStar (p + q)
        (twoBlockGridLift (affineGridStrip (p := p) (q := q) a b c lo hi)) =
      bivariateGridThresholdDeg
        (affineGridStrip (p := p) (q := q) a b c lo hi) := by
  apply HStar_affineGridStrip_eq_bivariateGridThresholdDeg_of_ltf_reverse
    a b c lo hi hlohi
  exact isBivariateGridLTF_of_isLTF_twoBlockGridLift hp hq

end HeadComplexity
