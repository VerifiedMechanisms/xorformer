import HeadComplexity.Atoms.ExactHammingProfile
import HeadComplexity.Atoms.FracAtomApproximation
import HeadComplexity.Polynomial.ParityThresholdDegree
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

/-!
# Uniform fractional approximation of Walsh characters

A Walsh character on a coordinate set `S` is parity on those `|S|` active
coordinates.  Exact Hamming-profile interpolation realizes its scalar `±1`
values with `|S|` atoms.  The quantitative dummy-coordinate lift then embeds
that score into the ambient cube with arbitrarily small uniform error.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- Increasing enumeration of the coordinates in a finite set. -/
noncomputable def finsetCoordinateEmbedding (S : Finset (Fin n)) :
    Fin S.card ↪ Fin n :=
  (S.orderEmbOfFin rfl).toEmbedding

/-- Walsh character, presented as parity on the increasing enumeration of
its active coordinate set. -/
noncomputable def walshCharacter (S : Finset (Fin n))
    (bits : Fin n → Bool) : ℝ :=
  if hammingWeight (pullBitsAlong (finsetCoordinateEmbedding S) bits) % 2 = 0
    then 1 else -1

/-- The parity presentation agrees with the conventional Walsh product. -/
theorem walshCharacter_eq_prod (S : Finset (Fin n))
    (bits : Fin n → Bool) :
    walshCharacter S bits =
      ∏ i ∈ S, (1 - 2 * boolToReal (bits i)) := by
  let e : Fin S.card ↪ Fin n := finsetCoordinateEmbedding S
  have hprod := prod_one_sub_two (pullBitsAlong e bits)
  have hreindex :
      (∏ i : Fin S.card, (1 - 2 * boolToReal (bits (e i)))) =
        ∏ i ∈ S, (1 - 2 * boolToReal (bits i)) := by
    calc
      (∏ i : Fin S.card, (1 - 2 * boolToReal (bits (e i)))) =
          ∏ s : S, (1 - 2 * boolToReal (bits s.1)) := by
            simpa [e, finsetCoordinateEmbedding] using
              (S.orderIsoOfFin rfl).toEquiv.prod_comp
                (fun s : S ↦ (1 - 2 * boolToReal (bits s.1)))
      _ = ∏ i ∈ S, (1 - 2 * boolToReal (bits i)) := by
        simpa using Finset.prod_attach S
          (fun i ↦ (1 - 2 * boolToReal (bits i)))
  change (∏ i : Fin S.card, (1 - 2 * boolToReal (bits (e i)))) = _ at hprod
  rw [hreindex] at hprod
  rw [walshCharacter]
  change (if hammingWeight (pullBitsAlong e bits) % 2 = 0 then 1 else -1) = _
  by_cases heven : hammingWeight (pullBitsAlong e bits) % 2 = 0
  · have hEven : Even (hammingWeight (pullBitsAlong e bits)) :=
      Nat.even_iff.mpr heven
    rw [if_pos heven, hprod, hEven.neg_one_pow]
  · have hOdd : Odd (hammingWeight (pullBitsAlong e bits)) := by
      rw [Nat.odd_iff]
      omega
    rw [if_neg heven, hprod, hOdd.neg_one_pow]

/-- Any signed Walsh character has a `|S|`-atom ambient score with arbitrary
uniform accuracy. -/
theorem exists_walsh_atoms_uniform (S : Finset (Fin n)) (coefficient : ℝ)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∃ (phi : Fin S.card → FracAtom n) (c : ℝ), ∀ bits,
      |(c + ∑ h, (phi h).eval bits) -
        coefficient * walshCharacter S bits| < tolerance := by
  let target : Fin (S.card + 1) → ℝ := fun k ↦
    coefficient * if (k : ℕ) % 2 = 0 then 1 else -1
  obtain ⟨psi, c, hexact⟩ :=
    exists_exact_hamming_atoms (n := S.card) target
  obtain ⟨epsilon, hepsilon, hclose⟩ :=
    exists_liftDummyAlong_uniform psi c (finsetCoordinateEmbedding S)
      tolerance htolerance
  refine ⟨fun h ↦ (psi h).liftDummy (finsetCoordinateEmbedding S)
      epsilon hepsilon, c, fun bits ↦ ?_⟩
  have htarget := hexact (pullBitsAlong (finsetCoordinateEmbedding S) bits)
  have happrox := hclose bits
  rw [htarget] at happrox
  simpa [target, walshCharacter] using happrox

end HeadComplexity
