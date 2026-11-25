import HeadComplexity.Atoms.RoPEClosedRank
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Weight

/-!
# Finite coefficient matrices for polynomial-valued linear maps

A bounded-degree coefficient projection preserves the rank of any map whose
image has that degree bound. Candidate maps need no degree bound to inherit a
rank upper bound under projection. This bridges coefficient convergence to the
closed matrix-rank strata without a topology on the full polynomial ring.
-/

noncomputable section

namespace HeadComplexity.RoPEPolynomialRankLimit

open MvPolynomial
open scoped BigOperators Topology

abbrev Exponent (σ : Type*) (d : ℕ) := {e : σ →₀ ℕ // Finsupp.degree e ≤ d}

instance {σ : Type*} [Finite σ] (d : ℕ) : Fintype (Exponent σ d) :=
  (Finsupp.finite_of_degree_le (σ := σ) d).fintype

def coefficientMap {σ : Type*} (d : ℕ) :
    MvPolynomial σ ℝ →ₗ[ℝ] (Exponent σ d → ℝ) :=
  LinearMap.pi (fun e ↦ MvPolynomial.lcoeff ℝ e.val)

@[simp] theorem coefficientMap_apply {σ : Type*} (d : ℕ)
    (P : MvPolynomial σ ℝ) (e : Exponent σ d) : coefficientMap d P e = P.coeff e.val := rfl

theorem coeff_zero_of_large {σ : Type*} (d : ℕ) (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ d) (e : σ →₀ ℕ) (he : d < Finsupp.degree e) : P.coeff e = 0 := by
  by_contra hne
  have hle := le_totalDegree (mem_support_iff.mpr hne)
  change Finsupp.degree e ≤ P.totalDegree at hle
  omega

theorem coefficientMap_zero_iff {σ : Type*} (d : ℕ) (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ d) : coefficientMap d P = 0 ↔ P = 0 := by
  constructor
  · intro hz
    ext e
    by_cases he : Finsupp.degree e ≤ d
    · exact congrFun hz ⟨e, he⟩
    · exact coeff_zero_of_large d P hP e (by omega)
  · rintro rfl
    exact map_zero _

theorem coefficientMap_comp_ker {σ V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : ℕ) (L : V →ₗ[ℝ] MvPolynomial σ ℝ) (hdeg : ∀ v, (L v).totalDegree ≤ d) :
    ((coefficientMap d).comp L).ker = L.ker := by
  apply Submodule.ext
  intro v
  exact coefficientMap_zero_iff d (L v) (hdeg v)

theorem coefficientMap_comp_rank {σ V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) (L : V →ₗ[ℝ] MvPolynomial σ ℝ)
    (hdeg : ∀ v, (L v).totalDegree ≤ d) :
    Module.finrank ℝ ((coefficientMap d).comp L).range = Module.finrank ℝ L.range := by
  have h1 := ((coefficientMap d).comp L).finrank_range_add_finrank_ker
  have h2 := L.finrank_range_add_finrank_ker
  rw [coefficientMap_comp_ker d L hdeg] at h1
  omega

def coefficientMatrix {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (L : (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ) : Matrix (Exponent σ d) ι ℝ :=
  LinearMap.toMatrix' ((coefficientMap d).comp L)

@[simp] theorem coefficientMatrix_apply {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (L : (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ) (e : Exponent σ d) (i : ι) :
    coefficientMatrix d L e i = (L (Pi.single i 1)).coeff e.val := by
  simp [coefficientMatrix, LinearMap.toMatrix'_apply]

theorem coefficientMatrix_rank {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (L : (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ) :
    (coefficientMatrix d L).rank = Module.finrank ℝ ((coefficientMap d).comp L).range := by
  change Module.finrank ℝ (Matrix.toLin' (coefficientMatrix d L)).range = _
  rw [coefficientMatrix, Matrix.toLin'_toMatrix']

theorem coefficientMatrix_rank_le {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (L : (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ) :
    (coefficientMatrix d L).rank ≤ Module.finrank ℝ L.range := by
  rw [coefficientMatrix_rank, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

theorem coefficientMatrix_rank_eq {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (L : (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (hdeg : ∀ v, (L v).totalDegree ≤ d) :
    (coefficientMatrix d L).rank = Module.finrank ℝ L.range := by
  rw [coefficientMatrix_rank, coefficientMap_comp_rank d L hdeg]

theorem rank_le_of_coefficient_tendsto {σ ι : Type*} [Finite σ] [Finite ι]
    [DecidableEq ι] (d r : ℕ)
    (L : ℕ → (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (M : (ι → ℝ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (hdeg : ∀ v, (M v).totalDegree ≤ d)
    (hlim : ∀ i e, Filter.Tendsto (fun k ↦ (L k (Pi.single i 1)).coeff e)
      Filter.atTop (nhds ((M (Pi.single i 1)).coeff e)))
    (hrank : ∀ k, Module.finrank ℝ (L k).range ≤ r) :
    Module.finrank ℝ M.range ≤ r := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [← coefficientMatrix_rank_eq d M hdeg]
  apply RoPEClosedRank.matrix_rank_le_of_tendsto r (fun k ↦ coefficientMatrix d (L k))
    (coefficientMatrix d M)
  · apply tendsto_pi_nhds.mpr
    intro e
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [coefficientMatrix_apply] using hlim i e.val
  · intro k
    exact (coefficientMatrix_rank_le d (L k)).trans (hrank k)

end HeadComplexity.RoPEPolynomialRankLimit
