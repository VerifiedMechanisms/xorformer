import HeadComplexity.Results.IntegralClearedCertificate
import HeadComplexity.Results.StructuralInvariances
import HeadComplexity.Results.ThresholdDegree

set_option linter.style.header false

/-!
# Lightweight certificates for five-bit degree-two exactness

This module isolates the symbolic parts of theorem 187 from its large external
cocircuit and tangent-cover archives.  It proves the `K_5` coloring reduction,
the soundness of exact integral Gordan circuits, the soundness of wrong-edge
witnesses, and the final passage from a symmetry-complete archive of two-head
certificates to `HStar = 2`.

No exhaustive table is evaluated here.  The missing archive is represented by
the `FiveBitDegreeTwoArchive.Covers` field, so the conditional theorem exposes
exactly the finite statement that a future kernel certificate must establish.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-! ## The complementary-cycle reduction on `K_5` -/

/-- An undirected two-coloring of the edges of `K_5`.  Loop colors are ignored. -/
structure K5EdgeColoring where
  color : Fin 5 → Fin 5 → Bool
  symmetric : ∀ i j, color i j = color j i

namespace K5EdgeColoring

/-- A triangle whose three edges all have color `shade`. -/
def HasMonochromaticTriangle (C : K5EdgeColoring) (shade : Bool) : Prop :=
  ∃ a b c : Fin 5,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      C.color a b = shade ∧ C.color a c = shade ∧ C.color b c = shade

/-- The number of edges of one color incident to a vertex. -/
def colorDegree (C : K5EdgeColoring) (shade : Bool) (v : Fin 5) : ℕ :=
  ((Finset.univ.erase v).filter fun w ↦ C.color v w = shade).card

/-- If a vertex has three incident edges of one color, either those edges or
the triangle between their other endpoints is monochromatic. -/
theorem monochromaticTriangle_of_two_lt_colorDegree
    (C : K5EdgeColoring) {shade : Bool} {v : Fin 5}
    (hdegree : 2 < C.colorDegree shade v) :
    C.HasMonochromaticTriangle shade ∨
      C.HasMonochromaticTriangle (!shade) := by
  classical
  rw [colorDegree, Finset.two_lt_card_iff] at hdegree
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hdegree
  have hav : a ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).1
  have hbv : b ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).1
  have hcv : c ≠ v := (Finset.mem_erase.mp (Finset.mem_filter.mp hc).1).1
  have hva : C.color v a = shade := (Finset.mem_filter.mp ha).2
  have hvb : C.color v b = shade := (Finset.mem_filter.mp hb).2
  have hvc : C.color v c = shade := (Finset.mem_filter.mp hc).2
  by_cases habColor : C.color a b = shade
  · exact Or.inl ⟨v, a, b, hav.symm, hbv.symm, hab,
      hva, hvb, habColor⟩
  · have habNot : C.color a b = !shade := by
      cases shade <;> simp_all
    by_cases hacColor : C.color a c = shade
    · exact Or.inl ⟨v, a, c, hav.symm, hcv.symm, hac,
        hva, hvc, hacColor⟩
    · have hacNot : C.color a c = !shade := by
        cases shade <;> simp_all
      by_cases hbcColor : C.color b c = shade
      · exact Or.inl ⟨v, b, c, hbv.symm, hcv.symm, hbc,
          hvb, hvc, hbcColor⟩
      · have hbcNot : C.color b c = !shade := by
          cases shade <;> simp_all
        exact Or.inr ⟨a, b, c, hab, hac, hbc,
          habNot, hacNot, hbcNot⟩

/-- In a triangle-free two-coloring of `K_5`, every vertex has exactly two
incident edges of each color.  Thus both color classes are complementary
two-regular graphs, the combinatorial core of the complementary-five-cycle
reduction in theorem 187. -/
theorem colorDegree_eq_two_of_no_monochromaticTriangle
    (C : K5EdgeColoring)
    (hmono : ∀ shade, ¬ C.HasMonochromaticTriangle shade) :
    ∀ shade v, C.colorDegree shade v = 2 := by
  classical
  intro shade v
  have hle : C.colorDegree shade v ≤ 2 := by
    by_contra h
    have hgt : 2 < C.colorDegree shade v := Nat.lt_of_not_ge h
    rcases C.monochromaticTriangle_of_two_lt_colorDegree hgt with h | h
    · exact hmono shade h
    · exact hmono (!shade) h
  have hleNot : C.colorDegree (!shade) v ≤ 2 := by
    by_contra h
    have hgt : 2 < C.colorDegree (!shade) v := Nat.lt_of_not_ge h
    rcases C.monochromaticTriangle_of_two_lt_colorDegree hgt with h | h
    · exact hmono (!shade) h
    · exact hmono (!!shade) h
  have hpartition :
      C.colorDegree shade v + C.colorDegree (!shade) v = 4 := by
    let neighbors : Finset (Fin 5) := Finset.univ.erase v
    have hcard : neighbors.card = 4 := by
      simp [neighbors]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := neighbors) (p := fun w ↦ C.color v w = shade)
    have hnot :
        (neighbors.filter fun w ↦ ¬ C.color v w = shade) =
          neighbors.filter fun w ↦ C.color v w = !shade := by
      ext w
      cases shade <;> simp
    rw [hnot, hcard] at hsplit
    exact hsplit
  omega

end K5EdgeColoring

/-! ## Exact finite leaf certificates -/

/-- Real evaluation of an integral row against a coefficient vector. -/
noncomputable def integralRowEval {k : ℕ}
    (row : Fin k → ℤ) (theta : Fin k → ℝ) : ℝ :=
  ∑ j, (row j : ℝ) * theta j

/-- An exact nonnegative integral dependence among finitely many rows.  This
is the kernel-facing content of a Gordan leaf. -/
structure IntegralGordanCircuit (m k : ℕ) (row : Fin m → Fin k → ℤ) where
  weight : Fin m → ℕ
  nonzero : ∃ i, 0 < weight i
  balance : ∀ j, ∑ i, (weight i : ℤ) * row i j = 0

namespace IntegralGordanCircuit

variable {m k : ℕ} {row : Fin m → Fin k → ℤ}

/-- A checked Gordan circuit rules out a coefficient vector that is strictly
positive on every row. -/
theorem excludes_strict_solution
    (C : IntegralGordanCircuit m k row) :
    ¬ ∃ theta : Fin k → ℝ, ∀ i, 0 < integralRowEval (row i) theta := by
  rintro ⟨theta, htheta⟩
  obtain ⟨i, hi⟩ := C.nonzero
  have hnonneg : ∀ a : Fin m,
      0 ≤ (C.weight a : ℝ) * integralRowEval (row a) theta := by
    intro a
    exact mul_nonneg (Nat.cast_nonneg _) (htheta a).le
  have hpositive :
      0 < ∑ a, (C.weight a : ℝ) * integralRowEval (row a) theta := by
    exact Finset.sum_pos' (fun a _ ↦ hnonneg a)
      ⟨i, Finset.mem_univ i, mul_pos (by exact_mod_cast hi) (htheta i)⟩
  have hzero :
      (∑ a, (C.weight a : ℝ) * integralRowEval (row a) theta) = 0 := by
    simp only [integralRowEval, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    have hbalance :
        (∑ a, (C.weight a : ℝ) * (row a j : ℝ)) = 0 := by
      exact_mod_cast C.balance j
    rw [hbalance, zero_mul]
  linarith

end IntegralGordanCircuit

/-- Strict membership in a finite open sign cell.  The rows already include
the target signs, so every evaluation is required to be positive. -/
def InStrictSignCell {m k : ℕ} (row : Fin m → Fin k → ℝ)
    (theta : Fin k → ℝ) : Prop :=
  ∀ i, 0 < ∑ j, row i j * theta j

/-- Weak membership in the closure of a finite sign cell. -/
def InClosedSignCell {m k : ℕ} (row : Fin m → Fin k → ℝ)
    (theta : Fin k → ℝ) : Prop :=
  ∀ i, 0 ≤ ∑ j, row i j * theta j

/-- A coordinate sign is locked if every strict representative has that sign. -/
def CoordinateLocked {m k : ℕ} (row : Fin m → Fin k → ℝ)
    (coordinate : Fin k) (sign : ℝ) : Prop :=
  ∀ theta, InStrictSignCell row theta → 0 < sign * theta coordinate

/-- A weak representative with the wrong strict coordinate sign disproves
locking, provided the open sign cell is nonempty.  Scaling the weak witness
and adding one strict representative stays in the open cell and eventually
reverses the chosen coordinate. -/
theorem not_coordinateLocked_of_wrongEdge
    {row : Fin m → Fin k → ℝ} {coordinate : Fin k} {sign : ℝ}
    (hstrict : ∃ theta, InStrictSignCell row theta)
    (wrong : Fin k → ℝ) (hweak : InClosedSignCell row wrong)
    (hwrong : sign * wrong coordinate < 0) :
    ¬ CoordinateLocked row coordinate sign := by
  rintro hlocked
  obtain ⟨theta, htheta⟩ := hstrict
  let a : ℝ := sign * theta coordinate
  let b : ℝ := sign * wrong coordinate
  let t : ℝ := (|a| + 1) / (-b)
  have hbneg : b < 0 := hwrong
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos (by positivity) (neg_pos.mpr hbneg)
  let combined : Fin k → ℝ := fun j ↦ theta j + t * wrong j
  have hcombined : InStrictSignCell row combined := by
    intro i
    have hs := htheta i
    have hw := hweak i
    change 0 < ∑ j, row i j * (theta j + t * wrong j)
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hfactor :
        (∑ j, row i j * (t * wrong j)) =
          t * ∑ j, row i j * wrong j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor]
    nlinarith
  have hlockedCombined := hlocked combined hcombined
  have habs : a ≤ |a| := le_abs_self a
  have hbpos : 0 < -b := neg_pos.mpr hbneg
  have hbne : b ≠ 0 := ne_of_lt hbneg
  have htidentity : t * b = -(|a| + 1) := by
    dsimp [t]
    field_simp [hbne]
  change 0 < sign * (theta coordinate + t * wrong coordinate) at hlockedCombined
  have hrewrite :
      sign * (theta coordinate + t * wrong coordinate) = a + t * b := by
    dsimp [a, b]
    ring
  rw [hrewrite, htidentity] at hlockedCombined
  linarith

/-! ## Archive reflection and the conditional headline theorem -/

/-- The exact order-40 input symmetries, together with output complementation,
used to quotient the five-bit archive. -/
def fiveBitSymmetry (sigma : Equiv.Perm (Fin 5))
    (complementInput complementOutput : Bool)
    (f : (Fin 5 → Bool) → Bool) : (Fin 5 → Bool) → Bool :=
  if complementOutput then
    fun x ↦ !(f (permuteBits sigma (if complementInput then flipBits x else x)))
  else
    fun x ↦ f (permuteBits sigma (if complementInput then flipBits x else x))

/-- The exact symmetries used by the archive preserve head complexity. -/
theorem HStar_fiveBitSymmetry (sigma : Equiv.Perm (Fin 5))
    (complementInput complementOutput : Bool)
    (f : (Fin 5 → Bool) → Bool) :
    HStar 5 (fiveBitSymmetry sigma complementInput complementOutput f) =
      HStar 5 f := by
  cases complementInput <;> cases complementOutput
  · simpa [fiveBitSymmetry] using HStar_permute sigma f
  · simpa [fiveBitSymmetry] using
      (HStar_complement (fun x ↦ f (permuteBits sigma x))).trans
        (HStar_permute sigma f)
  · simpa [fiveBitSymmetry] using
      (HStar_flip (fun x ↦ f (permuteBits sigma x))).trans
        (HStar_permute sigma f)
  · simpa [fiveBitSymmetry] using
      (HStar_complement
        (fun x ↦ f (permuteBits sigma (flipBits x)))).trans
        ((HStar_flip (fun x ↦ f (permuteBits sigma x))).trans
          (HStar_permute sigma f))

/-- A finite family of exact two-head representatives together with the one
nonlocal fact that it covers every five-bit function of threshold degree two.

The `certificate` field is a kernel-checkable cleared rational certificate
after clearing denominators to integers.  The `covers` field is precisely the
external cocircuit/tangent-cover obligation not supplied by this module. -/
structure FiveBitDegreeTwoArchive (archive : Type) where
  representative : archive → (Fin 5 → Bool) → Bool
  certificate : ∀ a, IntegralClearedScoreCertificate 5 2 (representative a)
  Covers : Prop
  covers_iff : Covers ↔
    ∀ f : (Fin 5 → Bool) → Bool, thresholdDeg f = 2 →
      ∃ a sigma complementInput complementOutput,
        f = fiveBitSymmetry sigma complementInput complementOutput
          (representative a)

namespace FiveBitDegreeTwoArchive

variable {archive : Type}

/-- Archive coverage and checked two-head rows give the upper bound. -/
theorem HStar_le_two (A : FiveBitDegreeTwoArchive archive)
    (hA : A.Covers) (f : (Fin 5 → Bool) → Bool)
    (hdegree : thresholdDeg f = 2) :
    HStar 5 f ≤ 2 := by
  obtain ⟨a, sigma, complementInput, complementOutput, rfl⟩ :=
    (A.covers_iff.mp hA) f hdegree
  rw [HStar_fiveBitSymmetry]
  exact (A.certificate a).HStar_le

/-- **Conditional theorem 187.** Once the exact finite archive coverage is
supplied, every five-bit degree-two function has head complexity exactly two. -/
theorem exact (A : FiveBitDegreeTwoArchive archive)
    (hA : A.Covers) (f : (Fin 5 → Bool) → Bool)
    (hdegree : thresholdDeg f = 2) :
    HStar 5 f = 2 := by
  apply Nat.le_antisymm (A.HStar_le_two hA f hdegree)
  rw [← hdegree]
  exact thresholdDeg_le_HStar f

end FiveBitDegreeTwoArchive

end HeadComplexity
