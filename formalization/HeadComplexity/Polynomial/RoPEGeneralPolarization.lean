import HeadComplexity.Polynomial.RoPEGeneralDerivative
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Diagonal contraction of the mixed source polynomial

There are two distinguished blocks and a finite list of remaining blocks.
After contracting the first two blocks, each remaining block is scaled by its
own parameter and evaluated at the same vector. The squarefree parameter
coefficient recovers a factorial times the genuine second directional derivative.
-/

noncomputable section

namespace HeadComplexity.RoPEGeneralPolarization

open MvPolynomial RoPEGeneralDerivative
open scoped BigOperators

variable {σ τ : Type*}

theorem directional_eval₂ (v : σ → ℝ) (w : τ → ℝ)
    (g : σ → MvPolynomial τ ℝ)
    (h : ∀ i, directional w (g i) = C (v i))
    (P : MvPolynomial σ ℝ) :
    directional w (eval₂ C g P) = eval₂ C g (directional v P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp [Derivation.leibniz, smul_eq_mul, hp, h]

theorem homogeneous_eval₂_scale {A : Type*} [CommRing A]
    (f : ℝ →+* A) (g : σ → A) (t : A)
    {P : MvPolynomial σ ℝ} {m : ℕ} (hP : P.IsHomogeneous m) :
    eval₂ f (fun i => t * g i) P = t ^ m * eval₂ f g P := by
  classical
  rw [← P.support_sum_monomial_coeff]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hedegree := hP.degree_eq_sum_deg_support he
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hedegree]
  ring

def allOnes (m : ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem allOnes_apply (m : ℕ) (i : Fin m) : allOnes m i = 1 := by
  simp [allOnes]

theorem coeff_allOnes_sum_pow {R : Type*} [CommSemiring R] (m : ℕ) :
    ((∑ i : Fin m, X i : MvPolynomial (Fin m) R) ^ m).coeff (allOnes m) =
      (m.factorial : R) := by
  rw [coeff_sum_X_pow_of_fintype]
  have hsupport : (allOnes m).support = Finset.univ := by
    ext i
    simp
  simp [Finsupp.sum, Finsupp.prod, Finsupp.multinomial, hsupport]

abbrev Block (m : ℕ) := Option (Option (Fin m))
abbrev BlockPoly (m : ℕ) (σ : Type*) := MvPolynomial (Block m × σ) ℝ
abbrev ParameterPoly (m : ℕ) (σ : Type*) := MvPolynomial (Fin m) (MvPolynomial σ ℝ)

def blockSum (m : ℕ) (i : σ) : BlockPoly m σ :=
  ∑ b : Block m, X (b, i)

def blockLift (m : ℕ) : MvPolynomial σ ℝ →ₐ[ℝ] BlockPoly m σ :=
  aeval (blockSum m)

@[simp] theorem blockLift_X (m : ℕ) (i : σ) :
    blockLift m (X i) = blockSum m i := by
  simp [blockLift]

def blockDirection (m : ℕ) (b : Block m) (v : σ → ℝ) :
    Block m × σ → ℝ := fun p => if p.1 = b then v p.2 else 0

theorem directional_blockSum (m : ℕ) (b : Block m) (v : σ → ℝ) (i : σ) :
    directional (blockDirection m b v) (blockSum m i) = C (v i) := by
  classical
  unfold blockSum
  rw [map_sum]
  calc
    _ = directional (blockDirection m b v) (X (b, i)) := by
      apply Finset.sum_eq_single b
      · intro c hc hcb
        simp [blockDirection, hcb]
      · intro hb
        exact (hb (Finset.mem_univ b)).elim
    _ = _ := by simp [blockDirection]

theorem directional_blockLift (m : ℕ) (b : Block m) (v : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    directional (blockDirection m b v) (blockLift m P) =
      blockLift m (directional v P) := by
  exact directional_eval₂ v (blockDirection m b v) (blockSum m)
    (directional_blockSum m b v) P

def collapseVariable (m : ℕ) : Block m × σ → ParameterPoly m σ
  | (none, _) => 0
  | (some none, _) => 0
  | (some (some b), i) => X b * C (X i)

def collapse (m : ℕ) : BlockPoly m σ →+* ParameterPoly m σ :=
  eval₂Hom (C.comp C) (collapseVariable m)

theorem collapse_blockSum (m : ℕ) (i : σ) :
    collapse m (blockSum m i) =
      (∑ b : Fin m, X b : ParameterPoly m σ) * C (X i) := by
  simp [collapse, blockSum, collapseVariable, Fintype.sum_option, Finset.sum_mul]

theorem collapse_blockLift (m : ℕ) (P : MvPolynomial σ ℝ) :
    collapse m (blockLift m P) =
      eval₂ (C.comp C) (fun i =>
        (∑ b : Fin m, X b : ParameterPoly m σ) * C (X i)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [blockLift, collapse]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp only [map_mul, eval₂_mul, blockLift_X,
      collapse_blockSum, eval₂_X, hp]

def contractDiagonal (m : ℕ) (P : BlockPoly m σ) (v w : σ → ℝ) :
    MvPolynomial σ ℝ :=
  (collapse m
    (directional (blockDirection m (some none) w)
      (directional (blockDirection m none v) P))).coeff (allOnes m)

def projection (m : ℕ) : BlockPoly m σ →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun P := (collapse m P).coeff (allOnes m)
  map_add' := by intros; simp
  map_smul' := by
    intro c P
    simp [smul_eq_C_mul, collapse, coeff_C_mul]

theorem contractDiagonal_eq_projection (m : ℕ) (P : BlockPoly m σ)
    (v w : σ → ℝ) :
    contractDiagonal m P v w =
      projection m (directional (blockDirection m (some none) w)
        (directional (blockDirection m none v) P)) := rfl

def blockDirectionLinear (m : ℕ) (b : Block m) :
    (σ → ℝ) →ₗ[ℝ] (Block m × σ → ℝ) where
  toFun v := blockDirection m b v
  map_add' := by
    intro v w
    funext p
    simp [blockDirection]
    split_ifs <;> simp
  map_smul' := by
    intro c v
    funext p
    simp [blockDirection]

def contractMap (m : ℕ) (P : BlockPoly m σ) (v : σ → ℝ) :
    (σ → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun w := contractDiagonal m P v w
  map_add' := by
    intro w z
    simp only [contractDiagonal_eq_projection]
    change projection m (directional (blockDirectionLinear m (some none) (w + z)) _) = _
    rw [map_add, directional_add]
    simp [blockDirectionLinear]
  map_smul' := by
    intro c w
    simp only [contractDiagonal_eq_projection]
    change projection m (directional (blockDirectionLinear m (some none) (c • w)) _) = _
    rw [map_smul, directional_smul]
    simp [blockDirectionLinear]

theorem contractDiagonal_blockLift (m : ℕ) (P : MvPolynomial σ ℝ)
    (v w : σ → ℝ)
    (hhom : (directional w (directional v P)).IsHomogeneous m) :
    contractDiagonal m (blockLift m P) v w =
      (m.factorial : ℝ) • directional w (directional v P) := by
  unfold contractDiagonal
  rw [directional_blockLift, directional_blockLift, collapse_blockLift,
    homogeneous_eval₂_scale _ _ _ hhom]
  have hbase : eval₂ (C.comp C) (fun i => C (X i))
      (directional w (directional v P)) =
      (C (directional w (directional v P)) : ParameterPoly m σ) := by
    generalize directional w (directional v P) = Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  rw [hbase, mul_comm, coeff_C_mul, coeff_allOnes_sum_pow]
  simp [Algebra.smul_def, mul_comm]

theorem derivation_sum_apply {ι : Type*} (s : Finset ι)
    (δ : ι → Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    (P : MvPolynomial σ ℝ) :
    (∑ i ∈ s, δ i) P = ∑ i ∈ s, δ i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, Derivation.add_apply]

theorem directional_eq_sum_pderiv [Fintype σ] (v : σ → ℝ) :
    directional v = ∑ i, v i • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  rw [derivation_sum_apply]
  simp [Pi.single_apply, smul_eq_C_mul]

theorem directional_isHomogeneous [Finite σ] (v : σ → ℝ)
    {P : MvPolynomial σ ℝ} {m : ℕ} (hP : P.IsHomogeneous m) :
    (directional v P).IsHomogeneous (m - 1) := by
  letI : Fintype σ := Fintype.ofFinite σ
  rw [directional_eq_sum_pderiv]
  simp only [derivation_sum_apply, Derivation.smul_apply]
  apply IsHomogeneous.sum
  intro i hi
  simpa [MvPolynomial.C_mul'] using hP.pderiv.C_mul (v i)

theorem denomProduct_isHomogeneous {H : ℕ} (s : Finset (Fin H)) :
    (denomProduct s).IsHomogeneous s.card := by
  unfold denomProduct
  simpa using IsHomogeneous.prod s (fun i => X (D i)) (fun _ => 1)
    (fun i hi => isHomogeneous_X ℝ (D i))

theorem source_isHomogeneous (H : ℕ) : (source H).IsHomogeneous H := by
  unfold source
  apply IsHomogeneous.sum
  intro i hi
  have h := (isHomogeneous_X ℝ (N i)).mul
    (denomProduct_isHomogeneous (Finset.univ.erase i))
  have hc : 1 + (Finset.univ.erase i).card = H := by
    have hiH := i.isLt
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  simpa only [hc] using h

theorem contractDiagonal_source (m : ℕ)
    (d a e b : Fin (m + 2) → ℝ) :
    contractDiagonal m (blockLift m (source (m + 2)))
      (direction d a) (direction e b) =
      (m.factorial : ℝ) • secondMap d a (e, b) := by
  apply contractDiagonal_blockLift
  have h := directional_isHomogeneous (direction e b)
    (directional_isHomogeneous (direction d a) (source_isHomogeneous (m + 2)))
  simpa using h

theorem collapse_coeff_isHomogeneous (m : ℕ) (P : BlockPoly m σ)
    (e : Fin m →₀ ℕ) : ((collapse m P).coeff e).IsHomogeneous e.degree := by
  classical
  induction P using MvPolynomial.induction_on generalizing e with
  | C c =>
      by_cases he : e = 0
      · subst e
        simpa [collapse] using (isHomogeneous_C (σ := σ) c)
      · simp [collapse, coeff_C, Ne.symm he, isHomogeneous_zero]
  | add p q hp hq => simpa using (hp e).add (hq e)
  | mul_X p i hp =>
      rcases i with ⟨(_ | (_ | b)), i⟩
      · simp [collapse, collapseVariable, isHomogeneous_zero]
      · simp [collapse, collapseVariable, isHomogeneous_zero]
      · have hcollapse : collapse m (p * X (some (some b), i)) =
            (collapse m p * X b) * C (X i) := by
          simp [collapse, collapseVariable, mul_assoc]
        rw [hcollapse, mul_comm _ (C (X i)), coeff_C_mul, coeff_mul_X']
        by_cases hb : b ∈ e.support
        · rw [if_pos hb]
          have hdegree : (e - Finsupp.single b 1).degree + 1 = e.degree := by
            have he := Finsupp.sub_add_single_one_cancel
              (Finsupp.mem_support_iff.mp hb)
            have hd := congrArg Finsupp.degree he
            simpa using hd
          rw [← hdegree]
          simpa only [mul_comm] using (hp (e - Finsupp.single b 1)).mul
            (isHomogeneous_X ℝ i)
        · simp [hb, isHomogeneous_zero]

@[simp] theorem allOnes_degree (m : ℕ) : (allOnes m).degree = m := by
  classical
  have hs : (allOnes m).support = Finset.univ := by ext i; simp
  simp [Finsupp.degree_apply, hs]

theorem projection_isHomogeneous (m : ℕ) (P : BlockPoly m σ) :
    (projection m P).IsHomogeneous m := by
  simpa only [projection, LinearMap.coe_mk, AddHom.coe_mk, allOnes_degree] using
    collapse_coeff_isHomogeneous m P (allOnes m)

theorem contractDiagonal_isHomogeneous (m : ℕ) (P : BlockPoly m σ)
    (v w : σ → ℝ) : (contractDiagonal m P v w).IsHomogeneous m :=
  projection_isHomogeneous m _

theorem contractDiagonal_totalDegree_le (m : ℕ) (P : BlockPoly m σ)
    (v w : σ → ℝ) : (contractDiagonal m P v w).totalDegree ≤ m :=
  (contractDiagonal_isHomogeneous m P v w).totalDegree_le

end HeadComplexity.RoPEGeneralPolarization
