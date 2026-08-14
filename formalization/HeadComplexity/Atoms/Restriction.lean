import HeadComplexity.Atoms.FracAtomHead
import HeadComplexity.Atoms.HeadToFracAtom
import HeadComplexity.BooleanCube.CoordinateFace

set_option linter.style.header false

/-!
# Restricting atoms to coordinate faces

A linear-fractional atom remains an atom after any coordinate restriction.
The fixed coordinates contribute constants to its numerator and denominator,
while the free coordinates retain their original parameters. This gives
restriction monotonicity for both atom representations and attention heads.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace FracAtom

variable {m n : ℕ}

/-- Restrict an atom to a coordinate face. Contributions from fixed
coordinates are absorbed into `eta` and `gamma`. -/
noncomputable def restrict (phi : FracAtom n) (rho : CoordFace m n) : FracAtom m where
  η := phi.η + ∑ j ∈ rho.fixedSet,
    phi.wt rho.base j * (phi.m j + if rho.base j then phi.δ else 0)
  δ := phi.δ
  γ := phi.γ + ∑ j ∈ rho.fixedSet, phi.wt rho.base j
  α := phi.α
  ρ := fun i => phi.ρ (rho.free i)
  m := fun i => phi.m (rho.free i)
  hγ := add_pos_of_pos_of_nonneg phi.hγ
    (Finset.sum_nonneg fun j _ => (phi.wt_pos rho.base j).le)
  hα := phi.hα
  hρ := fun i => phi.hρ (rho.free i)

@[simp] theorem restrict_wt (phi : FracAtom n) (rho : CoordFace m n)
    (x : Fin m → Bool) (i : Fin m) :
    (phi.restrict rho).wt x i = phi.wt (rho.apply x) (rho.free i) := by
  simp [FracAtom.wt, restrict]

/-- Restriction preserves the value of an atom exactly. -/
@[simp] theorem restrict_eval (phi : FracAtom n) (rho : CoordFace m n)
    (x : Fin m → Bool) :
    (phi.restrict rho).eval x = phi.eval (rho.apply x) := by
  unfold FracAtom.eval
  simp_rw [restrict_wt]
  simp only [restrict]
  rw [rho.sum_eq_free_add_fixed (fun j => phi.wt (rho.apply x) j)]
  rw [rho.sum_eq_free_add_fixed (fun j =>
    phi.wt (rho.apply x) j * (phi.m j + if rho.apply x j then phi.δ else 0))]
  have hfixed_wt : (∑ j ∈ rho.fixedSet, phi.wt (rho.apply x) j) =
      ∑ j ∈ rho.fixedSet, phi.wt rho.base j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [FracAtom.wt, rho.apply_fixed x hj]
  have hfixed_num :
      (∑ j ∈ rho.fixedSet,
        phi.wt (rho.apply x) j * (phi.m j + if rho.apply x j then phi.δ else 0)) =
      ∑ j ∈ rho.fixedSet,
        phi.wt rho.base j * (phi.m j + if rho.base j then phi.δ else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [FracAtom.wt, rho.apply_fixed x hj]
  rw [hfixed_wt, hfixed_num]
  simp only [CoordFace.apply_free]
  ring

end FracAtom

variable {m n H : ℕ}

/-- Atom computability is monotone under coordinate restriction. -/
theorem fracComputable.restrict {f : (Fin n → Bool) → Bool}
    (rho : CoordFace m n) (hf : fracComputable n H f) :
    fracComputable m H (fun x => f (rho.apply x)) := by
  rcases hf with ⟨phi, c, hphi⟩
  refine ⟨fun h => (phi h).restrict rho, c, ?_⟩
  intro x
  simpa using hphi (rho.apply x)

/-- Head computability is monotone under coordinate restriction. -/
theorem computableWithHeadsN.restrict {f : (Fin n → Bool) → Bool}
    (rho : CoordFace m n) (hf : computableWithHeadsN n H f) :
    computableWithHeadsN m H (fun x => f (rho.apply x)) :=
  computable_of_fracComputable
    (fracComputable.restrict rho (fracComputable_of_computable hf))

end HeadComplexity
