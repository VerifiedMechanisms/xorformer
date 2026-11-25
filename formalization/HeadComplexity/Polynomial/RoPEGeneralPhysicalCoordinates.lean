import HeadComplexity.Polynomial.AffineCoordinateEquivalence
import HeadComplexity.Polynomial.RoPEGeneralLocalDivisibility
import HeadComplexity.Atoms.RoPEGeneralCoordinates
import HeadComplexity.Results.PureGeneralReplicatedGrid

set_option linter.style.header false

/-! # Independent physical coordinates for the general-head source -/

namespace HeadComplexity.RoPEGeneralPhysicalCoordinates

open scoped BigOperators
open MvPolynomial PureGeneralReplicatedGrid

abbrev Input (h : ℕ) := Fin (groupCount (h + 1))
abbrev Extra (h : ℕ) := Fin (h * (2 * (h + 1)))
abbrev Output (h : ℕ) := RoPEGeneralPolynomial.Var (h + 1) (h * (2 * (h + 1)))

noncomputable def denominatorDirection {H : ℕ} (q : Fin (groupCount H) → ℝ) (i : Fin H) : ℝ :=
  ∑ g, d i g * q g

theorem denominatorDirection_blocks {H : ℕ} (q : Fin (groupCount H) → ℝ) (i : Fin H) :
    denominatorDirection q i = ∑ b : Fin H,
      (q (finProdFinEquiv (b, leftIndex i)) - q (finProdFinEquiv (b, rightIndex i))) := by
  rw [denominatorDirection, ← (finProdFinEquiv (m := H) (n := 2 * H)).sum_comp]
  simp only [d, localIndex, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  simp

theorem numerator_blocks {H : ℕ} (q : Fin (groupCount H) → ℝ) (i : Fin H) :
    numerator i q = 2 * ((∑ b : Fin H, ∑ j : Fin (2 * H), q (finProdFinEquiv (b, j))) +
      ∑ b : Fin H, q (finProdFinEquiv (b, leftIndex i))) := by
  rw [numerator, ← (finProdFinEquiv (m := H) (n := 2 * H)).sum_comp]
  simp only [u, localIndex, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    add_mul, mul_assoc, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp
  ring

/-- The first-block left/right coordinates partition all of its coordinates. -/
theorem sum_local {H : ℕ} (x : Fin (2 * H) → ℝ) :
    (∑ j, x j) = (∑ i : Fin H, x (leftIndex i)) + ∑ i : Fin H, x (rightIndex i) := by
  have hn : 2 * H = H + H := by omega
  rw [← (finCongr hn.symm).sum_comp, Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [rightIndex, Nat.add_comm]

noncomputable def firstBlock {h : ℕ} (q : Input h → ℝ) : RoPEGeneralCoordinates.Space (h + 1) :=
  (fun i ↦ q (finProdFinEquiv (0, leftIndex i)),
    fun i ↦ q (finProdFinEquiv (0, rightIndex i)))

def extraIndex {h : ℕ} (j : Extra h) : Input h :=
  let p := (finProdFinEquiv (m := h) (n := 2 * (h + 1))).symm j
  finProdFinEquiv (p.1.succ, p.2)

noncomputable def coordinateMap (h : ℕ) : (Input h → ℝ) →ₗ[ℝ] (Output h → ℝ) where
  toFun q := Sum.elim (denominatorDirection q)
    (Sum.elim (fun i ↦ numerator i q) (fun j ↦ q (extraIndex j)))
  map_add' q r := by
    funext v
    rcases v with i | i
    · simp [denominatorDirection, mul_add, Finset.sum_add_distrib]
    · rcases i with i | j
      · simp [numerator, mul_add, Finset.sum_add_distrib]
      · rfl
  map_smul' c q := by
    funext v
    rcases v with i | i
    · simp [denominatorDirection, ← Finset.mul_sum, mul_left_comm]
    · rcases i with i | j
      · simp [numerator, ← Finset.mul_sum, mul_left_comm]
      · rfl

theorem coordinateMap_injective (h : ℕ) : Function.Injective (coordinateMap h) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro q hq
  have hzero : coordinateMap h q = 0 := hq
  have htail (b : Fin h) (j : Fin (2 * (h + 1))) :
      q (finProdFinEquiv (b.succ, j)) = 0 := by
    have he := congrFun hzero (Sum.inr (Sum.inr (finProdFinEquiv (b, j))))
    simpa [coordinateMap, extraIndex] using he
  have hd (i : Fin (h + 1)) : RoPEGeneralCoordinates.denominator (firstBlock q) i = 0 := by
    have he := congrFun hzero (Sum.inl i)
    change denominatorDirection q i = 0 at he
    rw [denominatorDirection_blocks, Fin.sum_univ_succ] at he
    simpa [htail, firstBlock, RoPEGeneralCoordinates.denominator] using he
  have hn (i : Fin (h + 1)) : RoPEGeneralCoordinates.numerator (firstBlock q) i = 0 := by
    have he := congrFun hzero (Sum.inr (Sum.inl i))
    change numerator i q = 0 at he
    rw [numerator_blocks, Fin.sum_univ_succ, Fin.sum_univ_succ] at he
    simp only [htail, Finset.sum_const_zero, add_zero] at he
    rw [sum_local] at he
    simpa [firstBlock, RoPEGeneralCoordinates.numerator, RoPEGeneralCoordinates.total] using he
  have hf : firstBlock q = 0 := by
    apply (RoPEGeneralCoordinates.coordinateEquiv (h + 1)).injective
    change (RoPEGeneralCoordinates.denominator (firstBlock q),
      RoPEGeneralCoordinates.numerator (firstBlock q)) = _
    rw [map_zero]
    exact Prod.ext (funext hd) (funext hn)
  change q = 0
  funext g
  obtain ⟨⟨b, j⟩, rfl⟩ := (finProdFinEquiv (m := h + 1) (n := 2 * (h + 1))).surjective g
  refine Fin.cases ?_ (fun b ↦ htail b j) b
  have hleft (i : Fin (h + 1)) : q (finProdFinEquiv (0, leftIndex i)) = 0 :=
    congrFun (congrArg Prod.fst hf) i
  have hright (i : Fin (h + 1)) : q (finProdFinEquiv (0, rightIndex i)) = 0 :=
    congrFun (congrArg Prod.snd hf) i
  by_cases hj : j.val < h + 1
  · have hjEq : j = leftIndex ⟨j.val, hj⟩ := Fin.ext rfl
    rw [hjEq]
    exact hleft _
  · have hj' : j.val - (h + 1) < h + 1 := by omega
    have hjEq : j = rightIndex ⟨j.val - (h + 1), hj'⟩ := by
      apply Fin.ext
      simp only [rightIndex]
      omega
    rw [hjEq]
    exact hright _

noncomputable def coordinateEquiv (h : ℕ) : (Input h → ℝ) ≃ₗ[ℝ] (Output h → ℝ) :=
  LinearMap.linearEquivOfInjective (coordinateMap h) (coordinateMap_injective h)
    (by simp [Input, Output, RoPEGeneralPolynomial.Var, groupCount]; ring)


noncomputable def shift (h : ℕ) : Output h → ℝ :=
  Sum.elim (fun _ ↦ base (h + 1)) (fun _ ↦ 0)

noncomputable def substitutionEquiv (h : ℕ) :=
  AffineCoordinateEquivalence.substitutionEquiv (coordinateEquiv h) (shift h)

noncomputable def coordinateHomeomorph (h : ℕ) :=
  AffineCoordinateEquivalence.coordinateHomeomorph (coordinateEquiv h) (shift h)

noncomputable def physical (h : ℕ) : MvPolynomial (Input h) ℝ :=
  substitutionEquiv h (RoPEGeneralPolynomial.core (h + 1) (h * (2 * (h + 1))))

theorem eval_substitutionEquiv (h : ℕ)
    (P : MvPolynomial (Output h) ℝ) (q : Input h → ℝ) :
    eval q (substitutionEquiv h P) = eval (coordinateEquiv h q + shift h) P :=
  AffineCoordinateEquivalence.eval_substitutionEquiv _ _ _ _

theorem eval_substitutionEquiv_symm (h : ℕ)
    (P : MvPolynomial (Input h) ℝ) (q : Output h → ℝ) :
    eval q ((substitutionEquiv h).symm P) =
      eval ((coordinateEquiv h).symm (q - shift h)) P :=
  AffineCoordinateEquivalence.eval_substitutionEquiv_symm _ _ _ _

theorem eval_physical (h : ℕ) (q : Input h → ℝ) :
    eval q (physical h) = ∑ i : Fin (h + 1), numerator i q *
      ∏ j ∈ Finset.univ.erase i, denominator j q := by
  rw [physical, eval_substitutionEquiv, RoPEGeneralPolynomial.eval_core]
  simp [coordinateEquiv, LinearMap.linearEquivOfInjective_apply, coordinateMap,
    shift, RoPEGeneralPolynomial.numeratorIndex, RoPEGeneralPolynomial.denominatorIndex,
    denominator, denominatorDirection, add_comm]

theorem physical_totalDegree (h : ℕ) : (physical h).totalDegree = h + 1 := by
  rw [physical, substitutionEquiv, AffineCoordinateEquivalence.substitutionEquiv_totalDegree,
    RoPEGeneralPolynomial.core_totalDegree _ _ (by omega)]

theorem physical_irreducible (h : ℕ) : Irreducible (physical h) :=
  (MulEquiv.irreducible_iff (substitutionEquiv h)).mpr
    (RoPEGeneralPolynomial.core_irreducible _ _ (by omega))

theorem physical_dvd_of_weak_sign_on_open (h : ℕ) (Q : MvPolynomial (Input h) ℝ)
    (U : Set (Input h → ℝ)) (hU : IsOpen U) (hzero : (0 : Input h → ℝ) ∈ U)
    (hpos : ∀ q ∈ U, 0 < eval q (physical h) → 0 ≤ eval q Q)
    (hneg : ∀ q ∈ U, eval q (physical h) < 0 → eval q Q ≤ 0) : physical h ∣ Q := by
  let Ω : Set (Output h → ℝ) := coordinateHomeomorph h '' U
  have hΩ : IsOpen Ω := (coordinateHomeomorph h).isOpenMap U hU
  have hx : coordinateHomeomorph h 0 ∈ Ω := ⟨0, hzero, rfl⟩
  have hp : ∀ y ∈ Ω, 0 < eval y (RoPEGeneralPolynomial.core _ _) →
      0 ≤ eval y ((substitutionEquiv h).symm Q) := by
    rintro y ⟨q, hq, rfl⟩ hy
    rw [eval_substitutionEquiv_symm]
    change 0 ≤ eval ((coordinateEquiv h).symm (coordinateEquiv h q + shift h - shift h)) Q
    simp only [add_sub_cancel_right, LinearEquiv.symm_apply_apply]
    apply hpos q hq
    rwa [physical, eval_substitutionEquiv]
  have hn : ∀ y ∈ Ω, eval y (RoPEGeneralPolynomial.core _ _) < 0 →
      eval y ((substitutionEquiv h).symm Q) ≤ 0 := by
    rintro y ⟨q, hq, rfl⟩ hy
    rw [eval_substitutionEquiv_symm]
    change eval ((coordinateEquiv h).symm (coordinateEquiv h q + shift h - shift h)) Q ≤ 0
    simp only [add_sub_cancel_right, LinearEquiv.symm_apply_apply]
    apply hneg q hq
    rwa [physical, eval_substitutionEquiv]
  have hcorezero : eval (coordinateHomeomorph h 0) (RoPEGeneralPolynomial.core _ _) = 0 := by
    change eval (coordinateEquiv h 0 + shift h) (RoPEGeneralPolynomial.core _ _) = 0
    rw [← eval_substitutionEquiv]
    change eval 0 (physical h) = 0
    rw [eval_physical]
    simp [numerator]
  have hslope : eval (coordinateHomeomorph h 0)
      (RoPEGeneralPolynomial.omittedProduct (h + 1) (h * (2 * (h + 1))) 0) ≠ 0 := by
    simp only [RoPEGeneralPolynomial.omittedProduct, map_prod, eval_X]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    change (coordinateEquiv h 0 + shift h) (RoPEGeneralPolynomial.denominatorIndex i) ≠ 0
    simp only [map_zero, zero_add, shift, RoPEGeneralPolynomial.denominatorIndex, Sum.elim_inl]
    dsimp [base]
    positivity
  have hd := RoPEGeneralPolynomial.core_dvd_of_weak_sign_on_open
    (by omega : 0 < h + 1) 0 ((substitutionEquiv h).symm Q)
    Ω hΩ hp hn (coordinateHomeomorph h 0) hx hcorezero hslope
  have hm := map_dvd (substitutionEquiv h).toRingHom hd
  change substitutionEquiv h (RoPEGeneralPolynomial.core _ _) ∣
    substitutionEquiv h ((substitutionEquiv h).symm Q) at hm
  simpa only [AlgEquiv.apply_symm_apply, physical] using hm

def openCube (h : ℕ) : Set (Input h → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Ioo (-1 : ℝ) 1)

theorem isOpen_openCube (h : ℕ) : IsOpen (openCube h) :=
  isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)

theorem zero_mem_openCube (h : ℕ) : (0 : Input h → ℝ) ∈ openCube h := by
  intro i _
  norm_num

/-- Full-degree weak sign limits are nonzero scalar multiples of the actual source. -/
theorem scalar_multiple_of_weak_sign_cube (h : ℕ) (Q : MvPolynomial (Input h) ℝ)
    (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ h + 1)
    (hweak : ∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
      (0 < eval q (physical h) → 0 ≤ eval q Q) ∧
      (eval q (physical h) < 0 → eval q Q ≤ 0)) :
    ∃ a : ℝ, a ≠ 0 ∧ Q = C a * physical h := by
  apply SignLimitProportionality.scalar_multiple_of_dvd_of_totalDegree_le
    (physical h) Q (physical_irreducible h).ne_zero hQ
  · simpa only [physical_totalDegree] using hdeg
  · exact physical_dvd_of_weak_sign_on_open h Q (openCube h)
      (isOpen_openCube h) (zero_mem_openCube h)
      (fun q hq ↦ (hweak q (fun i ↦ ⟨(hq i trivial).1.le, (hq i trivial).2.le⟩)).1)
      (fun q hq ↦ (hweak q (fun i ↦ ⟨(hq i trivial).1.le, (hq i trivial).2.le⟩)).2)

/-- The actual physical source has no nonzero lower-degree weak sign polynomial. -/
theorem no_lower_degree_weak_sign_cube (h : ℕ) (Q : MvPolynomial (Input h) ℝ)
    (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ h)
    (hweak : ∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
      (0 < eval q (physical h) → 0 ≤ eval q Q) ∧
      (eval q (physical h) < 0 → eval q Q ≤ 0)) : False := by
  have hd := physical_dvd_of_weak_sign_on_open h Q (openCube h)
    (isOpen_openCube h) (zero_mem_openCube h)
    (fun q hq ↦ (hweak q (fun i ↦ ⟨(hq i trivial).1.le, (hq i trivial).2.le⟩)).1)
    (fun q hq ↦ (hweak q (fun i ↦ ⟨(hq i trivial).1.le, (hq i trivial).2.le⟩)).2)
  obtain ⟨R, hR⟩ := hd
  have hRne : R ≠ 0 := by intro he; rw [he, mul_zero] at hR; exact hQ hR
  rw [hR, totalDegree_mul_of_isDomain (physical_irreducible h).ne_zero hRne,
    physical_totalDegree] at hdeg
  omega

end HeadComplexity.RoPEGeneralPhysicalCoordinates
