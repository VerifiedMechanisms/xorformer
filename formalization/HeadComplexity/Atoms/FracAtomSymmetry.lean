import HeadComplexity.Atoms.Restriction
import HeadComplexity.BooleanCube.Symmetry

set_option linter.style.header false

/-!
# Exact symmetries of fractional atoms

The one-head atom class is closed exactly under coordinate permutations,
simultaneous input complementation, and negation of its scalar output.  These
identities supply the algebraic part of the structural invariances in theorem
28.  Target complementation additionally needs a finite-margin strictification
at the result level because the representation convention is one-sided on
false inputs.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace FracAtom

variable {n : ℕ}

/-- Negate the scalar value of an atom without changing its denominator. -/
def neg (phi : FracAtom n) : FracAtom n where
  η := -phi.η
  δ := -phi.δ
  γ := phi.γ
  α := phi.α
  ρ := phi.ρ
  m := fun i ↦ -phi.m i
  hγ := phi.hγ
  hα := phi.hα
  hρ := phi.hρ

@[simp] theorem neg_wt (phi : FracAtom n) (x : Fin n → Bool) (i : Fin n) :
    phi.neg.wt x i = phi.wt x i := rfl

@[simp] theorem neg_eval (phi : FracAtom n) (x : Fin n → Bool) :
    phi.neg.eval x = -phi.eval x := by
  have hnum :
      (∑ i, phi.neg.wt x i * (phi.neg.m i + if x i then phi.neg.δ else 0)) =
        -(∑ i, phi.wt x i * (phi.m i + if x i then phi.δ else 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [neg_wt]
    cases x i with
    | false => simp [neg]
    | true => simp [neg]; ring
  have hden : (∑ i, phi.neg.wt x i) = ∑ i, phi.wt x i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact neg_wt phi x i
  unfold FracAtom.eval
  rw [hnum, hden]
  simp only [neg]
  ring

/-- Relabel an atom by a permutation of the input coordinates. -/
def permute (phi : FracAtom n) (sigma : Equiv.Perm (Fin n)) : FracAtom n where
  η := phi.η
  δ := phi.δ
  γ := phi.γ
  α := phi.α
  ρ := fun i ↦ phi.ρ (sigma.symm i)
  m := fun i ↦ phi.m (sigma.symm i)
  hγ := phi.hγ
  hα := phi.hα
  hρ := fun i ↦ phi.hρ (sigma.symm i)

@[simp] theorem permute_wt (phi : FracAtom n) (sigma : Equiv.Perm (Fin n))
    (x : Fin n → Bool) (i : Fin n) :
    (phi.permute sigma).wt x (sigma i) = phi.wt (permuteBits sigma x) i := by
  simp [FracAtom.wt, permute, permuteBits]

@[simp] theorem permute_eval (phi : FracAtom n) (sigma : Equiv.Perm (Fin n))
    (x : Fin n → Bool) :
    (phi.permute sigma).eval x = phi.eval (permuteBits sigma x) := by
  have hden :
      (∑ j, (phi.permute sigma).wt x j) =
        ∑ i, phi.wt (permuteBits sigma x) i := by
    exact (Fintype.sum_equiv sigma
      (fun i ↦ phi.wt (permuteBits sigma x) i)
      (fun j ↦ (phi.permute sigma).wt x j)
      (fun i ↦ (permute_wt phi sigma x i).symm)).symm
  have hnum :
      (∑ j, (phi.permute sigma).wt x j *
        ((phi.permute sigma).m j + if x j then (phi.permute sigma).δ else 0)) =
        ∑ i, phi.wt (permuteBits sigma x) i *
          (phi.m i + if permuteBits sigma x i then phi.δ else 0) := by
    exact (Fintype.sum_equiv sigma
      (fun i ↦ phi.wt (permuteBits sigma x) i *
        (phi.m i + if permuteBits sigma x i then phi.δ else 0))
      (fun j ↦ (phi.permute sigma).wt x j *
        ((phi.permute sigma).m j + if x j then (phi.permute sigma).δ else 0))
      (fun i ↦ by rw [permute_wt]; simp [permute, permuteBits])).symm
  unfold FracAtom.eval
  rw [hden, hnum]
  rfl

/-- Transform an atom under simultaneous complementation of every bit. -/
noncomputable def flip (phi : FracAtom n) : FracAtom n where
  η := phi.η
  δ := -phi.δ
  γ := phi.γ
  α := phi.α⁻¹
  ρ := fun i ↦ phi.ρ i * phi.α
  m := fun i ↦ phi.m i + phi.δ
  hγ := phi.hγ
  hα := inv_pos.mpr phi.hα
  hρ := fun i ↦ mul_pos (phi.hρ i) phi.hα

@[simp] theorem flip_wt (phi : FracAtom n) (x : Fin n → Bool) (i : Fin n) :
    phi.flip.wt x i = phi.wt (flipBits x) i := by
  cases hxi : x i with
  | false => simp [FracAtom.wt, flip, flipBits, hxi]
  | true =>
      simp [FracAtom.wt, flip, flipBits, hxi, phi.hα.ne']

@[simp] theorem flip_eval (phi : FracAtom n) (x : Fin n → Bool) :
    phi.flip.eval x = phi.eval (flipBits x) := by
  have hden :
      (∑ i, phi.flip.wt x i) = ∑ i, phi.wt (flipBits x) i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact flip_wt phi x i
  have hnum :
      (∑ i, phi.flip.wt x i *
        (phi.flip.m i + if x i then phi.flip.δ else 0)) =
        ∑ i, phi.wt (flipBits x) i *
          (phi.m i + if flipBits x i then phi.δ else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [flip_wt]
    cases hxi : x i <;> simp [flip, flipBits, hxi]
  unfold FracAtom.eval
  rw [hden, hnum]
  rfl

end FracAtom

variable {n H : ℕ}

/-- Atom computability is preserved by coordinate permutations. -/
theorem fracComputable.permute {f : (Fin n → Bool) → Bool}
    (sigma : Equiv.Perm (Fin n)) (hf : fracComputable n H f) :
    fracComputable n H (fun x ↦ f (permuteBits sigma x)) := by
  rcases hf with ⟨phi, c, hphi⟩
  refine ⟨fun h ↦ (phi h).permute sigma, c, ?_⟩
  intro x
  simpa using hphi (permuteBits sigma x)

/-- Atom computability is preserved by simultaneous bit complementation. -/
theorem fracComputable.flip {f : (Fin n → Bool) → Bool}
    (hf : fracComputable n H f) :
    fracComputable n H (fun x ↦ f (flipBits x)) := by
  rcases hf with ⟨phi, c, hphi⟩
  refine ⟨fun h ↦ (phi h).flip, c, ?_⟩
  intro x
  simpa using hphi (flipBits x)

end HeadComplexity
