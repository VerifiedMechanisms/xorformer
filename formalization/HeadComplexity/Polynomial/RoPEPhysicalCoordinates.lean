import HeadComplexity.Polynomial.RoPECubicIrreducible
import HeadComplexity.Polynomial.RoPECubicLocalDivisibility
import HeadComplexity.Atoms.RoPEThreeTensor
import HeadComplexity.Results.PureThreeReplicatedGrid
import Mathlib.Topology.Algebra.MvPolynomial

set_option linter.style.header false

/-!
# Physical coordinates for the replicated-grid cubic

The first six new coordinates are the three denominators and numerators.
The remaining twelve coordinates are retained. The first source block is
invertible, giving both a homeomorphism and a polynomial substitution equivalence.
-/

namespace HeadComplexity.RoPEPhysicalCoordinates

open scoped BigOperators
open MvPolynomial

abbrev Vec := Fin 18 → ℝ
abbrev Poly := MvPolynomial (Fin 18) ℝ

def first {R : Type*} (x : Fin 18 → R) : Fin 6 → R := fun i ↦ x (Fin.castAdd 12 i)
def tail {R : Type*} (x : Fin 18 → R) : Fin 12 → R := fun i ↦ x (Fin.natAdd 6 i)
def join {R : Type*} (a : Fin 6 → R) (b : Fin 12 → R) : Fin 18 → R :=
  fun i ↦ Fin.addCases (m := 6) (n := 12) a b i

@[simp] theorem first_join {R : Type*} (a : Fin 6 → R) (b : Fin 12 → R) :
    first (join a b) = a := by funext i; simp [first, join]

@[simp] theorem tail_join {R : Type*} (a : Fin 6 → R) (b : Fin 12 → R) :
    tail (join a b) = b := by funext i; simp [tail, join]

@[simp] theorem join_first_tail {R : Type*} (x : Fin 18 → R) :
    join (first x) (tail x) = x := by
  funext i
  refine Fin.addCases (m := 6) (n := 12) ?_ ?_ i
  · intro j
    simp [join, first]
  · intro j
    simp [join, tail]

def tailSum {R : Type*} [Add R] (x : Fin 12 → R) : Fin 6 → R :=
  fun i ↦ x (Fin.castAdd 6 i) + x (Fin.natAdd 6 i)

noncomputable def B : Matrix (Fin 6) (Fin 6) ℝ := RoPEThreeTensor.blockMatrix 1 2
noncomputable def shift : Fin 6 → ℝ := ![200, 200, 200, 0, 0, 0]

noncomputable def forward (x : Vec) : Vec :=
  join (B.mulVec (first x + tailSum (tail x)) + shift) (tail x)

noncomputable def backward (y : Vec) : Vec :=
  join ((B⁻¹).mulVec (first y - shift) - tailSum (tail y)) (tail y)

theorem B_isUnit : IsUnit B := RoPEThreeTensor.blockMatrix_isUnit 1 2 (by norm_num) (by norm_num)

theorem backward_forward (x : Vec) : backward (forward x) = x := by
  have hB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp B_isUnit)
  simp only [backward, forward, first_join, tail_join, add_sub_cancel_right,
    Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  exact join_first_tail x

theorem forward_backward (y : Vec) : forward (backward y) = y := by
  have hB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp B_isUnit)
  simp only [backward, forward, first_join, tail_join, sub_add_cancel,
    Matrix.mulVec_mulVec, hB, Matrix.one_mulVec, join_first_tail]

@[fun_prop] theorem continuous_first : Continuous (first : Vec → Fin 6 → ℝ) := by
  unfold first
  fun_prop

@[fun_prop] theorem continuous_tail : Continuous (tail : Vec → Fin 12 → ℝ) := by
  unfold tail
  fun_prop

theorem continuous_join : Continuous (fun p : (Fin 6 → ℝ) × (Fin 12 → ℝ) ↦ join p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.addCases (m := 6) (n := 12) ?_ ?_ i
  · intro j
    simpa [join, Function.comp_def] using (continuous_apply j).comp continuous_fst
  · intro j
    simpa [join, Function.comp_def] using (continuous_apply j).comp continuous_snd

@[fun_prop] theorem continuous_tailSum : Continuous (tailSum : (Fin 12 → ℝ) → Fin 6 → ℝ) := by
  unfold tailSum
  fun_prop

theorem continuous_forward : Continuous forward := by
  unfold forward
  exact continuous_join.comp (show Continuous (fun x : Vec ↦
    (B.mulVec (first x + tailSum (tail x)) + shift, tail x)) by fun_prop)

theorem continuous_backward : Continuous backward := by
  unfold backward
  exact continuous_join.comp (show Continuous (fun y : Vec ↦
    ((B⁻¹).mulVec (first y - shift) - tailSum (tail y), tail y)) by fun_prop)

noncomputable def coordinateHomeomorph : Vec ≃ₜ Vec where
  toFun := forward
  invFun := backward
  left_inv := backward_forward
  right_inv := forward_backward
  continuous_toFun := continuous_forward
  continuous_invFun := continuous_backward

noncomputable def forwardPolynomial : Fin 18 → Poly :=
  join (fun j ↦ (∑ k, C (B j k) * (first X k + tailSum (tail X) k)) + C (shift j)) (tail X)

noncomputable def backwardPolynomial : Fin 18 → Poly :=
  join (fun j ↦ (∑ k, C (B⁻¹ j k) * (first X k - C (shift k))) - tailSum (tail X) j) (tail X)

theorem eval_forwardPolynomial (x : Vec) :
    (fun i ↦ eval x (forwardPolynomial i)) = forward x := by
  funext i
  refine Fin.addCases (m := 6) (n := 12) ?_ ?_ i
  · intro j
    simp [forwardPolynomial, forward, join, first, tail, tailSum, Matrix.mulVec, dotProduct]
  · intro j
    simp [forwardPolynomial, forward, join, tail]

theorem eval_backwardPolynomial (x : Vec) :
    (fun i ↦ eval x (backwardPolynomial i)) = backward x := by
  funext i
  refine Fin.addCases (m := 6) (n := 12) ?_ ?_ i
  · intro j
    simp [backwardPolynomial, backward, join, first, tail, tailSum, Matrix.mulVec, dotProduct]
  · intro j
    simp [backwardPolynomial, backward, join, tail]

theorem eval_substitute (p : Poly) (q : Fin 18 → Poly) (x : Vec) :
    eval x (aeval q p) = eval (fun i ↦ eval x (q i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp]

noncomputable def substitutionEquiv : Poly ≃ₐ[ℝ] Poly where
  toFun := aeval forwardPolynomial
  invFun := aeval backwardPolynomial
  left_inv p := by
    apply MvPolynomial.funext
    intro x
    rw [eval_substitute, eval_backwardPolynomial, eval_substitute,
      eval_forwardPolynomial, forward_backward]
  right_inv p := by
    apply MvPolynomial.funext
    intro x
    rw [eval_substitute, eval_forwardPolynomial, eval_substitute,
      eval_backwardPolynomial, backward_forward]
  map_mul' := (aeval forwardPolynomial).map_mul
  map_add' := (aeval forwardPolynomial).map_add
  commutes' := (aeval forwardPolynomial).commutes

theorem eval_substitutionEquiv (p : Poly) (x : Vec) :
    eval x (substitutionEquiv p) = eval (forward x) p := by
  change eval x (aeval forwardPolynomial p) = _
  rw [eval_substitute, eval_forwardPolynomial]

theorem eval_substitutionEquiv_symm (p : Poly) (x : Vec) :
    eval x (substitutionEquiv.symm p) = eval (backward x) p := by
  change eval x (aeval backwardPolynomial p) = _
  rw [eval_substitute, eval_backwardPolynomial]

noncomputable def physical : Poly := substitutionEquiv RoPECubic.core

/-- Substitution of affine polynomials cannot increase total degree. -/
theorem totalDegree_substitute_le (p : Poly) (q : Fin 18 → Poly)
    (hq : ∀ i, (q i).totalDegree ≤ 1) : (aeval q p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial]
  calc
    _ ≤ (d.prod fun i k ↦ q i ^ k).totalDegree := by
      simpa using totalDegree_mul (C (p.coeff d)) (d.prod fun i k ↦ q i ^ k)
    _ ≤ ∑ i ∈ d.support, (q i ^ d i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hq i))
    _ ≤ p.totalDegree := le_totalDegree hd

theorem totalDegree_add_le_one (p q : Poly)
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) : (p + q).totalDegree ≤ 1 :=
  (totalDegree_add p q).trans (max_le hp hq)

theorem totalDegree_sub_le_one (p q : Poly)
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) : (p - q).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg]
  exact totalDegree_add_le_one _ _ hp (by simpa using hq)

theorem forwardPolynomial_totalDegree (i : Fin 18) : (forwardPolynomial i).totalDegree ≤ 1 := by
  refine Fin.addCases (m := 6) (n := 12) ?_ ?_ i
  · intro j
    simp only [forwardPolynomial, join, Fin.addCases_left]
    apply totalDegree_add_le_one
    · apply totalDegree_finsetSum_le
      intro k _
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      apply totalDegree_add_le_one
      · simp [first]
      · apply totalDegree_add_le_one <;> simp [tail]
    · simp
  · intro j
    simp [forwardPolynomial, join, tail]

theorem backwardPolynomial_totalDegree (i : Fin 18) : (backwardPolynomial i).totalDegree ≤ 1 := by
  refine Fin.addCases (m := 6) (n := 12) ?_ ?_ i
  · intro j
    simp only [backwardPolynomial, join, Fin.addCases_left]
    apply totalDegree_sub_le_one
    · apply totalDegree_finsetSum_le
      intro k _
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      apply totalDegree_sub_le_one <;> simp [first]
    · apply totalDegree_add_le_one <;> simp [tail]
  · intro j
    simp [backwardPolynomial, join, tail]

theorem substitutionEquiv_totalDegree (p : Poly) :
    (substitutionEquiv p).totalDegree = p.totalDegree := by
  have hf : (substitutionEquiv p).totalDegree ≤ p.totalDegree :=
    totalDegree_substitute_le p _ forwardPolynomial_totalDegree
  have h := totalDegree_substitute_le (substitutionEquiv p) _ backwardPolynomial_totalDegree
  change (substitutionEquiv.symm (substitutionEquiv p)).totalDegree ≤ _ at h
  have hb : p.totalDegree ≤ (substitutionEquiv p).totalDegree := by
    simpa only [AlgEquiv.symm_apply_apply] using h
  exact Nat.le_antisymm hf hb

theorem physical_totalDegree : physical.totalDegree = 3 := by
  rw [physical, substitutionEquiv_totalDegree, RoPECubic.core_totalDegree]

set_option maxHeartbeats 800000 in
-- Checking the six actual rows expands the eighteen source group coordinates.
theorem first_forward (x : Vec) :
    first (forward x) =
      ![PureThreeReplicatedGrid.denominator 0 x, PureThreeReplicatedGrid.denominator 1 x,
        PureThreeReplicatedGrid.denominator 2 x, PureThreeReplicatedGrid.numerator 0 x,
        PureThreeReplicatedGrid.numerator 1 x, PureThreeReplicatedGrid.numerator 2 x] := by
  simp only [forward, first_join]
  ext i
  fin_cases i <;>
    norm_num [B, RoPEThreeTensor.blockMatrix, Matrix.mulVec, dotProduct, first, tail,
      tailSum, shift, PureThreeReplicatedGrid.denominator, PureThreeReplicatedGrid.numerator,
      PureThreeReplicatedGrid.d, PureThreeReplicatedGrid.u, Fin.sum_univ_succ,
      Fin.castAdd, Fin.natAdd, Fin.addNat, Fin.succ] <;> ring

theorem eval_physical (x : Vec) : eval x physical = PureThreeReplicatedGrid.clearedScore x := by
  rw [physical, eval_substitutionEquiv]
  have h := first_forward x
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  change forward x 0 = PureThreeReplicatedGrid.denominator 0 x at h0
  change forward x 1 = PureThreeReplicatedGrid.denominator 1 x at h1
  change forward x 2 = PureThreeReplicatedGrid.denominator 2 x at h2
  change forward x 3 = PureThreeReplicatedGrid.numerator 0 x at h3
  change forward x 4 = PureThreeReplicatedGrid.numerator 1 x at h4
  change forward x 5 = PureThreeReplicatedGrid.numerator 2 x at h5
  simp only [RoPECubic.core, map_add, map_mul, eval_X, h0, h1, h2, h3, h4, h5,
    PureThreeReplicatedGrid.clearedScore]

theorem physical_irreducible : Irreducible physical :=
  (MulEquiv.irreducible_iff substitutionEquiv).mpr RoPECubic.core_irreducible

noncomputable def denominatorPolynomial (h : Fin 3) : Poly :=
  C 200 + ∑ g, C (PureThreeReplicatedGrid.d h g) * X g

noncomputable def numeratorPolynomial (h : Fin 3) : Poly :=
  ∑ g, C (PureThreeReplicatedGrid.u h g) * X g

theorem eval_denominatorPolynomial (h : Fin 3) (x : Vec) :
    eval x (denominatorPolynomial h) = PureThreeReplicatedGrid.denominator h x := by
  simp [denominatorPolynomial, PureThreeReplicatedGrid.denominator]

theorem eval_numeratorPolynomial (h : Fin 3) (x : Vec) :
    eval x (numeratorPolynomial h) = PureThreeReplicatedGrid.numerator h x := by
  simp [numeratorPolynomial, PureThreeReplicatedGrid.numerator]

theorem physical_explicit : physical =
    numeratorPolynomial 0 * denominatorPolynomial 1 * denominatorPolynomial 2 +
      numeratorPolynomial 1 * denominatorPolynomial 0 * denominatorPolynomial 2 +
      numeratorPolynomial 2 * denominatorPolynomial 0 * denominatorPolynomial 1 := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_physical, map_add, map_mul, eval_denominatorPolynomial,
    eval_numeratorPolynomial, PureThreeReplicatedGrid.clearedScore]

/-- Weak sign agreement on any open physical neighborhood of the origin implies
divisibility by the physical cleared cubic. -/
theorem physical_dvd_of_weak_sign_on_open (Q : Poly)
    (U : Set Vec) (hU : IsOpen U) (hzero : (0 : Vec) ∈ U)
    (hpos : ∀ x ∈ U, 0 < eval x physical → 0 ≤ eval x Q)
    (hneg : ∀ x ∈ U, eval x physical < 0 → eval x Q ≤ 0) : physical ∣ Q := by
  let Ω : Set Vec := coordinateHomeomorph '' U
  have hΩ : IsOpen Ω := coordinateHomeomorph.isOpenMap U hU
  have hx : forward 0 ∈ Ω := ⟨0, hzero, rfl⟩
  have hp : ∀ y ∈ Ω, 0 < eval y RoPECubic.core →
      0 ≤ eval y (substitutionEquiv.symm Q) := by
    rintro y ⟨x, hx, rfl⟩ hy
    rw [eval_substitutionEquiv_symm]
    change 0 ≤ eval (backward (forward x)) Q
    rw [backward_forward]
    apply hpos x hx
    rwa [physical, eval_substitutionEquiv]
  have hn : ∀ y ∈ Ω, eval y RoPECubic.core < 0 →
      eval y (substitutionEquiv.symm Q) ≤ 0 := by
    rintro y ⟨x, hx, rfl⟩ hy
    rw [eval_substitutionEquiv_symm]
    change eval (backward (forward x)) Q ≤ 0
    rw [backward_forward]
    apply hneg x hx
    rwa [physical, eval_substitutionEquiv]
  have hcorezero : eval (forward 0) RoPECubic.core = 0 := by
    rw [← eval_substitutionEquiv, ← physical, eval_physical]
    simp [PureThreeReplicatedGrid.clearedScore, PureThreeReplicatedGrid.numerator]
  have hslope : eval (forward 0) RoPECubic.slope ≠ 0 := by
    have h := first_forward 0
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change forward 0 0 = PureThreeReplicatedGrid.denominator 0 0 at h0
    change forward 0 1 = PureThreeReplicatedGrid.denominator 1 0 at h1
    simp only [RoPECubic.slope, map_mul, eval_X, h0, h1]
    norm_num [PureThreeReplicatedGrid.denominator]
  have hd := RoPECubic.core_dvd_of_weak_sign_on_open
    (substitutionEquiv.symm Q) Ω hΩ hp hn (forward 0) hx hcorezero hslope
  have hm := map_dvd substitutionEquiv.toRingHom hd
  change substitutionEquiv RoPECubic.core ∣ substitutionEquiv (substitutionEquiv.symm Q) at hm
  simpa only [AlgEquiv.apply_symm_apply, physical] using hm

def openCube : Set Vec := Set.pi Set.univ (fun _ ↦ Set.Ioo (-1 : ℝ) 1)

theorem isOpen_openCube : IsOpen openCube :=
  isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)

theorem zero_mem_openCube : (0 : Vec) ∈ openCube := by
  intro i _
  norm_num

theorem half_mem_openCube : (fun _ : Fin 18 ↦ (1 / 2 : ℝ)) ∈ openCube := by
  intro i _
  norm_num

theorem eval_physical_half_pos : 0 < eval (fun _ : Fin 18 ↦ (1 / 2 : ℝ)) physical := by
  rw [eval_physical]
  have hd (h : Fin 3) : PureThreeReplicatedGrid.denominator h (fun _ ↦ (1 / 2 : ℝ)) = 200 := by
    simp only [PureThreeReplicatedGrid.denominator, ← Finset.sum_mul,
      PureThreeReplicatedGrid.sum_d, zero_mul, add_zero]
  have hn (h : Fin 3) : PureThreeReplicatedGrid.numerator h (fun _ ↦ (1 / 2 : ℝ)) = 21 := by
    simp only [PureThreeReplicatedGrid.numerator, ← Finset.sum_mul,
      PureThreeReplicatedGrid.sum_u]
    norm_num
  norm_num [PureThreeReplicatedGrid.clearedScore, hd, hn]

/-- The analytic rigidity conclusion used after coefficient compactness:
a nonzero degree-three weak sign limit is a positive scalar source multiple. -/
theorem positive_scalar_multiple_of_weak_sign_cube (Q : Poly) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ 3)
    (hpos : ∀ x ∈ openCube, 0 < eval x physical → 0 ≤ eval x Q)
    (hneg : ∀ x ∈ openCube, eval x physical < 0 → eval x Q ≤ 0) :
    ∃ a : ℝ, 0 < a ∧ Q = C a * physical := by
  apply SignLimitProportionality.positive_scalar_multiple_of_dvd_of_totalDegree_le
    physical Q physical_irreducible.ne_zero hQ
  · simpa only [physical_totalDegree] using hdeg
  · exact physical_dvd_of_weak_sign_on_open Q openCube isOpen_openCube zero_mem_openCube hpos hneg
  · exact eval_physical_half_pos
  · exact hpos _ half_mem_openCube eval_physical_half_pos

end HeadComplexity.RoPEPhysicalCoordinates
