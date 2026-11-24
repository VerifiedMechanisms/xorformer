import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-! Exact finite-dimensional matrix identities for the row-scaling quotient.
No assertion about asymptotic head complexity is made in this module. -/

namespace HeadComplexity.RowScalingGeometry
open Finset Matrix
noncomputable section

variable {ι : Type*} [Fintype ι]

def pairing (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def energy (A : Matrix ι ι ℝ) : ℝ := pairing A A

theorem pairing_trace (A B : Matrix ι ι ℝ) : pairing A B = trace (Aᵀ * B) := by
  unfold pairing Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_comm]

theorem pairing_comm (A B : Matrix ι ι ℝ) : pairing A B = pairing B A := by
  simp only [pairing, mul_comm]

theorem pairing_add_left (A B C : Matrix ι ι ℝ) :
    pairing (A + B) C = pairing A C + pairing B C := by
  simp [pairing, add_mul, sum_add_distrib]

theorem pairing_add_right (A B C : Matrix ι ι ℝ) :
    pairing A (B + C) = pairing A B + pairing A C := by
  simp [pairing, mul_add, sum_add_distrib]

theorem energy_nonneg (A : Matrix ι ι ℝ) : 0 ≤ energy A := by
  unfold energy pairing
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => mul_self_nonneg (A i j)

theorem energy_add (A B : Matrix ι ι ℝ) :
    energy (A + B) = energy A + 2 * pairing A B + energy B := by
  simp only [energy, pairing_add_left, pairing_add_right]
  rw [pairing_comm B A]
  ring

variable [DecidableEq ι]

def rowVariation (P : Matrix ι ι ℝ) (t : ι → ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (diagonal t * P + P * diagonal t) - P * diagonal t * P

def laplacian (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => P i i) - Matrix.of (fun i j => (P i j) ^ 2)

theorem variation_symmetric (P : Matrix ι ι ℝ) (t : ι → ℝ) (hp : Pᵀ = P) :
    (rowVariation P t)ᵀ = rowVariation P t := by
  simp only [rowVariation, transpose_sub, transpose_smul, transpose_add,
    transpose_mul, diagonal_transpose, hp]
  rw [Matrix.mul_assoc]
  abel_nf

theorem variation_tangent (P : Matrix ι ι ℝ) (t : ι → ℝ) (hp : P * P = P) :
    P * rowVariation P t + rowVariation P t * P = rowVariation P t := by
  unfold rowVariation
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hleft (Z : Matrix ι ι ℝ) : P * (P * Z) = P * Z := by
    rw [← Matrix.mul_assoc, hp]
  simp only [Matrix.mul_assoc, hp, hleft]
  module

theorem variation_middle_zero (P : Matrix ι ι ℝ) (t : ι → ℝ)
    (hp : P * P = P) : P * rowVariation P t * P = 0 := by
  unfold rowVariation
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [← Matrix.mul_assoc, hp]
  have h : P * diagonal t * P * P = P * diagonal t * P := by
    rw [Matrix.mul_assoc, hp]
  rw [h]
  module

theorem variation_pairing (P X : Matrix ι ι ℝ) (t : ι → ℝ)
    (hx : Xᵀ = X) (ht : P * X + X * P = X) (hm : P * X * P = 0) :
    pairing X (rowVariation P t) = (1 / 2 : ℝ) * ∑ i, t i * X i i := by
  rw [pairing_trace, hx]
  unfold rowVariation
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add,
    trace_sub, trace_smul, trace_add, smul_eq_mul]
  have h₁ : trace (X * (diagonal t * P)) = trace (P * X * diagonal t) := by
    rw [← Matrix.mul_assoc, trace_mul_cycle]
  have h₂ : trace (X * (P * diagonal t)) = trace (X * P * diagonal t) := by
    rw [Matrix.mul_assoc]
  have h₃ : trace (X * (P * diagonal t * P)) = 0 := by
    rw [← Matrix.mul_assoc, trace_mul_cycle, Matrix.mul_assoc P X,
      ← Matrix.mul_assoc X P, ← Matrix.mul_assoc P (X * P),
      ← Matrix.mul_assoc P X, hm, Matrix.zero_mul, trace_zero]
  rw [h₁, h₂, h₃, sub_zero, ← trace_add, ← Matrix.add_mul, ht]
  congr 1
  simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, mul_comm]

theorem variation_diagonal (P : Matrix ι ι ℝ) (t : ι → ℝ)
    (hp : Pᵀ = P) (i : ι) :
    rowVariation P t i i = (laplacian P).mulVec t i := by
  have hs (j : ι) : P j i = P i j := congrFun (congrFun hp i) j
  have h₁ : (diagonal t * P) i i = t i * P i i := diagonal_mul t P i i
  have h₂ : (P * diagonal t) i i = P i i * t i := mul_diagonal t P i i
  have h₃ : (P * diagonal t * P) i i = ∑ j, (P i j) ^ 2 * t j := by
    rw [Matrix.mul_apply]
    apply sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, hs]
    ring
  have h₄ : (laplacian P).mulVec t i =
      P i i * t i - ∑ j, (P i j) ^ 2 * t j := by
    simp [laplacian, Matrix.mulVec, dotProduct, sub_mul, sum_sub_distrib,
      Matrix.diagonal_apply]
  rw [h₄]
  simp only [rowVariation, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, h₁, h₂, h₃]
  ring

theorem variation_energy (P : Matrix ι ι ℝ) (t : ι → ℝ)
    (hs : Pᵀ = P) (hi : P * P = P) :
    energy (rowVariation P t) =
      (1 / 2 : ℝ) * ∑ i, t i * (laplacian P).mulVec t i := by
  unfold energy
  rw [variation_pairing P _ t (variation_symmetric P t hs)
    (variation_tangent P t hi) (variation_middle_zero P t hi)]
  simp_rw [variation_diagonal P t hs]

theorem zero_diagonal_orthogonal (P Y : Matrix ι ι ℝ)
    (hs : Yᵀ = Y) (ht : P * Y + Y * P = Y) (hm : P * Y * P = 0)
    (hd : ∀ i, Y i i = 0) (a : ι → ℝ) :
    pairing Y (rowVariation P a) = 0 := by
  rw [variation_pairing P Y a hs ht hm]
  simp [hd]

theorem zero_diagonal_minimal (P Y : Matrix ι ι ℝ)
    (hs : Yᵀ = Y) (ht : P * Y + Y * P = Y) (hm : P * Y * P = 0)
    (hd : ∀ i, Y i i = 0) (a : ι → ℝ) :
    energy Y ≤ energy (Y + rowVariation P a) := by
  rw [energy_add, zero_diagonal_orthogonal P Y hs ht hm hd a]
  linarith [energy_nonneg (rowVariation P a)]

theorem rebalanced_diagonal (P X : Matrix ι ι ℝ) (t : ι → ℝ)
    (hs : Pᵀ = P) (ht : ∀ i, (laplacian P).mulVec t i = -X i i) (i : ι) :
    (X + rowVariation P t) i i = 0 := by
  simp [Matrix.add_apply, variation_diagonal P t hs, ht]

theorem rebalanced_energy (P X : Matrix ι ι ℝ) (t : ι → ℝ)
    (hps : Pᵀ = P) (hpi : P * P = P)
    (hxs : Xᵀ = X) (hxt : P * X + X * P = X) (hxm : P * X * P = 0)
    (ht : ∀ i, (laplacian P).mulVec t i = -X i i) :
    energy (X + rowVariation P t) =
      energy X - (1 / 2 : ℝ) * ∑ i, t i * (laplacian P).mulVec t i := by
  rw [energy_add, variation_pairing P X t hxs hxt hxm,
    variation_energy P t hps hpi]
  simp_rw [ht, mul_neg, sum_neg_distrib]
  ring

theorem rebalanced_orthogonal (P X : Matrix ι ι ℝ) (t a : ι → ℝ)
    (hps : Pᵀ = P) (hpi : P * P = P)
    (hxs : Xᵀ = X) (hxt : P * X + X * P = X) (hxm : P * X * P = 0)
    (ht : ∀ i, (laplacian P).mulVec t i = -X i i) :
    pairing (X + rowVariation P t) (rowVariation P a) = 0 := by
  apply zero_diagonal_orthogonal P _ _ _ _ _ a
  · rw [transpose_add, hxs, variation_symmetric P t hps]
  · have hr := variation_tangent P t hpi
    simp only [Matrix.mul_add, Matrix.add_mul]
    calc
      P * X + P * rowVariation P t + (X * P + rowVariation P t * P) =
          (P * X + X * P) + (P * rowVariation P t + rowVariation P t * P) := by abel
      _ = X + rowVariation P t := by rw [hxt, hr]
  · simp only [Matrix.mul_add, Matrix.add_mul, hxm,
      variation_middle_zero P t hpi, add_zero]
  · exact rebalanced_diagonal P X t hps ht

theorem rebalanced_minimal (P X : Matrix ι ι ℝ) (t a : ι → ℝ)
    (hps : Pᵀ = P) (hpi : P * P = P)
    (hxs : Xᵀ = X) (hxt : P * X + X * P = X) (hxm : P * X * P = 0)
    (ht : ∀ i, (laplacian P).mulVec t i = -X i i) :
    energy (X + rowVariation P t) ≤ energy (X + rowVariation P t + rowVariation P a) := by
  rw [energy_add (X + rowVariation P t) (rowVariation P a),
    rebalanced_orthogonal P X t a hps hpi hxs hxt hxm ht]
  linarith [energy_nonneg (rowVariation P a)]

theorem laplacian_nonnegative (P : Matrix ι ι ℝ) (t : ι → ℝ)
    (hs : Pᵀ = P) (hi : P * P = P) :
    0 ≤ ∑ i, t i * (laplacian P).mulVec t i := by
  have h := energy_nonneg (rowVariation P t)
  rw [variation_energy P t hs hi] at h
  linarith

omit [DecidableEq ι] in
theorem energy_zero_iff (A : Matrix ι ι ℝ) : energy A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hsum : ∑ i, ∑ j, (A i j) ^ 2 = 0 := by
      simpa [energy, pairing, pow_two] using h
    have hi (i : ι) : ∑ j, (A i j) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg fun i _ =>
        sum_nonneg fun j _ => sq_nonneg (A i j)).mp hsum i (mem_univ i)
    ext i j
    have hij : (A i j) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (A i j)).mp (hi i) j (mem_univ j)
    simpa using (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp [energy, pairing]

theorem rebalanced_unique (P X : Matrix ι ι ℝ) (t a : ι → ℝ)
    (hps : Pᵀ = P) (hpi : P * P = P)
    (hxs : Xᵀ = X) (hxt : P * X + X * P = X) (hxm : P * X * P = 0)
    (ht : ∀ i, (laplacian P).mulVec t i = -X i i)
    (he : energy (X + rowVariation P t + rowVariation P a) = energy (X + rowVariation P t)) :
    rowVariation P a = 0 := by
  apply (energy_zero_iff _).mp
  rw [energy_add (X + rowVariation P t) (rowVariation P a),
    rebalanced_orthogonal P X t a hps hpi hxs hxt hxm ht] at he
  linarith

omit [DecidableEq ι] in
theorem symmetric_solvable (M : Matrix ι ι ℝ) (d : ι → ℝ) (hm : Mᵀ = M)
    (hk : ∀ z : ι → ℝ, M.mulVec z = 0 → ∑ i, z i * d i = 0) :
    ∃ t : ι → ℝ, M.mulVec t = d := by
  classical
  let F := M.toEuclideanLin
  have hs : F.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    simpa [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm] using hm
  have hv : WithLp.toLp 2 d ∈ (LinearMap.ker F)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hz' : M.mulVec (WithLp.ofLp z) = 0 := by
      have h := congrArg WithLp.ofLp (LinearMap.mem_ker.mp hz)
      simpa [F, Matrix.ofLp_toLpLin, Matrix.toLin'_apply] using h
    have h := hk (WithLp.ofLp z) hz'
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h
  have hr : (LinearMap.ker F)ᗮ = LinearMap.range F := by
    rw [← hs.orthogonal_range]
    exact Submodule.orthogonal_orthogonal _
  rw [hr] at hv
  obtain ⟨z, hz⟩ := hv
  refine ⟨WithLp.ofLp z, ?_⟩
  have h := congrArg WithLp.ofLp hz
  simpa [F, Matrix.ofLp_toLpLin, Matrix.toLin'_apply] using h

omit [Fintype ι] in
theorem laplacian_symmetric (P : Matrix ι ι ℝ) (hp : Pᵀ = P) :
    (laplacian P)ᵀ = laplacian P := by
  have hs (i j : ι) : P j i = P i j := congrFun (congrFun hp i) j
  ext i j
  by_cases hij : i = j
  · subst j
    simp [laplacian, Matrix.transpose_apply]
  · simp [laplacian, Matrix.transpose_apply, hs, hij, Ne.symm hij]

theorem exists_rebalancing (P X : Matrix ι ι ℝ)
    (hps : Pᵀ = P) (hpi : P * P = P)
    (hxs : Xᵀ = X) (hxt : P * X + X * P = X) (hxm : P * X * P = 0) :
    ∃ t : ι → ℝ, ∀ i, (laplacian P).mulVec t i = -X i i := by
  have hk (z : ι → ℝ) (hz : (laplacian P).mulVec z = 0) :
      ∑ i, z i * (-X i i) = 0 := by
    have he : energy (rowVariation P z) = 0 := by
      rw [variation_energy P z hps hpi, hz]
      simp
    have hzero := (energy_zero_iff _).mp he
    have hpair := variation_pairing P X z hxs hxt hxm
    rw [hzero] at hpair
    simp only [pairing, Matrix.zero_apply, mul_zero, sum_const_zero] at hpair
    simp_rw [mul_neg, sum_neg_distrib]
    linarith
  obtain ⟨t, ht⟩ := symmetric_solvable (laplacian P) (fun i => -X i i)
    (laplacian_symmetric P hps) hk
  exact ⟨t, fun i => congrFun ht i⟩

end
end HeadComplexity.RowScalingGeometry
