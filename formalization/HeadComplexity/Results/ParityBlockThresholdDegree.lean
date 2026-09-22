import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.ThresholdDegree
import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Atoms.UniformApproximation

set_option linter.style.header false

/-!
# Parity-block threshold-degree amplification

Iterating the fresh-bit XOR construction gives an arbitrary fresh parity
block.  The exact threshold-degree identity is inherited one coordinate at a
time from `thresholdDeg_freshXor`.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

universe u

variable {m : ℕ}

/-- XOR a Boolean feature with `k` fresh coordinates.  The fresh coordinates
are prepended one at a time; their XOR is therefore independent of this
chosen recursive ordering. -/
def parityBlockXor : (k : ℕ) → ((Fin m → Bool) → Bool) →
    (Fin (m + k) → Bool) → Bool
  | 0, T => T
  | k + 1, T => freshXor (parityBlockXor k T)

@[simp] theorem parityBlockXor_zero
    (T : (Fin m → Bool) → Bool) :
    parityBlockXor 0 T = T := rfl

@[simp] theorem parityBlockXor_succ
    (k : ℕ) (T : (Fin m → Bool) → Bool) :
    parityBlockXor (k + 1) T = freshXor (parityBlockXor k T) := rfl

/-- **Parity-block threshold-degree amplifier.** XOR with `k` fresh bits
raises threshold degree by exactly `k`. -/
theorem thresholdDeg_parityBlockXor
    (k : ℕ) (T : (Fin m → Bool) → Bool) :
    thresholdDeg (parityBlockXor k T) = thresholdDeg T + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [parityBlockXor_succ, thresholdDeg_freshXor, ih]
      omega

/-- The threshold-degree amplifier gives the corresponding composable lower
bound on head complexity. -/
theorem thresholdDeg_add_le_HStar_parityBlockXor
    (k : ℕ) (T : (Fin m → Bool) → Bool) :
    thresholdDeg T + k ≤ HStar (m + k) (parityBlockXor k T) := by
  rw [← thresholdDeg_parityBlockXor k T]
  exact thresholdDeg_le_HStar _

/-! ## Sparse polynomial-threshold fallback -/

theorem squarefreeMonomial_image_succ
    (S : Finset (Fin m)) (bits : Fin (m + 1) → Bool) :
    squarefreeMonomial (S.image Fin.succ) bits =
      squarefreeMonomial S (tailBits bits) := by
  unfold squarefreeMonomial tailBits
  rw [Finset.prod_image (Fin.succ_injective m).injOn]

theorem squarefreeMonomial_insert_zero_image_succ
    (S : Finset (Fin m)) (bits : Fin (m + 1) → Bool) :
    squarefreeMonomial (insert 0 (S.image Fin.succ)) bits =
      boolToReal (bits 0) * squarefreeMonomial S (tailBits bits) := by
  have hzero : (0 : Fin (m + 1)) ∉ S.image Fin.succ := by simp
  unfold squarefreeMonomial tailBits
  rw [Finset.prod_insert hzero,
    Finset.prod_image (Fin.succ_injective m).injOn]

/-- A strict sign score presented as a constant plus finitely many signed
squarefree monomials. The index type is deliberately arbitrary so that the
fresh-XOR transformation can preserve the term structure. -/
structure SparseMonomialCertificate (ι : Type*) [Fintype ι]
    (f : (Fin m → Bool) → Bool) where
  bias : ℝ
  coefficient : ι → ℝ
  support : ι → Finset (Fin m)
  strict : StrictSignRepresentsScore
    (fun bits ↦ bias + ∑ i, coefficient i * squarefreeMonomial (support i) bits)
    f

namespace SparseMonomialCertificate

variable {ι : Type*} [Fintype ι] {T : (Fin m → Bool) → Bool}

/-- A sparse monomial certificate compiles with one approximating atom per
nonconstant monomial term. -/
theorem computable (C : SparseMonomialCertificate ι T) :
    computableWithHeadsN m (Fintype.card ι) T := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let g : Fin (Fintype.card ι) → (Fin m → Bool) → ℝ :=
    fun h bits ↦ C.coefficient (e.symm h) *
      squarefreeMonomial (C.support (e.symm h)) bits
  refine computableWithHeadsN_of_uniformlyOneAtomApproximable g ?_ C.bias ?_
  · intro h
    exact uniformlyOneAtomApproximable_signedMonomial
      (C.support (e.symm h)) (C.coefficient (e.symm h))
  · intro bits
    have hsum : (∑ h, g h bits) =
        ∑ i, C.coefficient i * squarefreeMonomial (C.support i) bits := by
      simpa [g] using e.symm.sum_comp
        (fun i ↦ C.coefficient i * squarefreeMonomial (C.support i) bits)
    change
      ((0 < C.bias + ∑ h, g h bits ↔ T bits = true) ∧
        C.bias + ∑ h, g h bits ≠ 0)
    rw [hsum]
    exact C.strict bits

theorem HStar_le_card (C : SparseMonomialCertificate ι T) :
    HStar m T ≤ Fintype.card ι :=
  HStar_le_of_computableWithHeadsN C.computable

/-- Multiplication of a sparse score by the fresh-bit sign switch
`1 - 2z` replaces every old monomial by its tail lift and its product with
`z`, and adds the product of `z` with the old bias. -/
noncomputable def freshXor (C : SparseMonomialCertificate ι T) :
    SparseMonomialCertificate (Sum ι (Sum ι Unit))
      (HeadComplexity.freshXor T) where
  bias := C.bias
  coefficient
    | Sum.inl i => C.coefficient i
    | Sum.inr (Sum.inl i) => -2 * C.coefficient i
    | Sum.inr (Sum.inr _) => -2 * C.bias
  support
    | Sum.inl i => (C.support i).image Fin.succ
    | Sum.inr (Sum.inl i) => insert 0 ((C.support i).image Fin.succ)
    | Sum.inr (Sum.inr _) => {0}
  strict := by
    intro bits
    have hscore :
        C.bias +
            ∑ i : Sum ι (Sum ι Unit),
              (match i with
                | Sum.inl j => C.coefficient j
                | Sum.inr (Sum.inl j) => -2 * C.coefficient j
                | Sum.inr (Sum.inr _) => -2 * C.bias) *
              squarefreeMonomial
                (match i with
                  | Sum.inl j => (C.support j).image Fin.succ
                  | Sum.inr (Sum.inl j) =>
                      insert 0 ((C.support j).image Fin.succ)
                  | Sum.inr (Sum.inr _) => {0}) bits =
          (1 - 2 * boolToReal (bits 0)) *
            (C.bias + ∑ i, C.coefficient i *
              squarefreeMonomial (C.support i) (tailBits bits)) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp_rw [squarefreeMonomial_image_succ,
        squarefreeMonomial_insert_zero_image_succ]
      cases hz : bits 0
      · simp [squarefreeMonomial, boolToReal, hz]
      · simp [squarefreeMonomial, boolToReal, hz]
        have htwo :
            (∑ x, 2 * C.coefficient x *
                ∏ j ∈ C.support x,
                  if tailBits bits j = true then (1 : ℝ) else 0) =
              2 * ∑ x, C.coefficient x *
                ∏ j ∈ C.support x,
                  if tailBits bits j = true then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [htwo]
        ring
    dsimp only
    rw [hscore]
    let R := C.bias + ∑ i, C.coefficient i *
      squarefreeMonomial (C.support i) (tailBits bits)
    change
      ((0 < (1 - 2 * boolToReal (bits 0)) * R ↔
          HeadComplexity.freshXor T bits = true) ∧
        (1 - 2 * boolToReal (bits 0)) * R ≠ 0)
    have hold : (0 < R ↔ T (tailBits bits) = true) ∧ R ≠ 0 := by
      simpa [R] using C.strict (tailBits bits)
    cases hz : bits 0
    · simpa [R, HeadComplexity.freshXor, freshBitGate, hz, boolToReal]
        using hold
    · cases hT : T (tailBits bits)
      · have hnpos : ¬ 0 < R := by simpa [hT] using hold.1
        have hRneg : R < 0 := lt_of_le_of_ne (le_of_not_gt hnpos) hold.2
        norm_num [HeadComplexity.freshXor, freshBitGate, hz, hT, boolToReal]
        exact ⟨hRneg, hold.2⟩
      · have hRpos : 0 < R := by simpa [hT] using hold.1
        norm_num [HeadComplexity.freshXor, freshBitGate, hz, hT, boolToReal]
        exact ⟨hRpos.le, hold.2⟩

end SparseMonomialCertificate

/-- The closed-form sparse-monomial index for a parity block. -/
abbrev ParitySparseIndex (k : ℕ) (ι : Type u) [Fintype ι] :=
  Fin (2 ^ k * (Fintype.card ι + 1) - 1)

namespace SparseMonomialCertificate

variable {ι : Type*} [Fintype ι] {T : (Fin m → Bool) → Bool}

/-- Transport a sparse certificate along a finite reindexing. -/
noncomputable def reindex {κ : Type*} [Fintype κ]
    (C : SparseMonomialCertificate ι T) (e : κ ≃ ι) :
    SparseMonomialCertificate κ T where
  bias := C.bias
  coefficient := fun j ↦ C.coefficient (e j)
  support := fun j ↦ C.support (e j)
  strict := by
    intro bits
    dsimp only
    have hsum :
        (∑ j : κ, C.coefficient (e j) *
            squarefreeMonomial (C.support (e j)) bits) =
          ∑ i : ι, C.coefficient i *
            squarefreeMonomial (C.support i) bits := by
      exact e.sum_comp
        (fun i ↦ C.coefficient i * squarefreeMonomial (C.support i) bits)
    rw [hsum]
    exact C.strict bits

/-- Iterate the sparse fresh-XOR transformation over a parity block. -/
noncomputable def parityBlock
    (C : SparseMonomialCertificate ι T) (k : ℕ) :
    SparseMonomialCertificate (ParitySparseIndex k ι)
      (parityBlockXor k T) := by
  induction k with
  | zero =>
      let e : ParitySparseIndex 0 ι ≃ ι :=
        Fintype.equivOfCardEq (by simp [ParitySparseIndex])
      simpa using C.reindex e
  | succ k ih =>
      let source := Sum (ParitySparseIndex k ι)
        (Sum (ParitySparseIndex k ι) Unit)
      let e : ParitySparseIndex (k + 1) ι ≃ source :=
        Fintype.equivOfCardEq (by
          dsimp [source, ParitySparseIndex]
          simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_unit,
            pow_succ]
          have hpositive : 0 < 2 ^ k * (Fintype.card ι + 1) := by
            positivity
          have hdouble :
              2 ^ k * 2 * (Fintype.card ι + 1) =
                2 * (2 ^ k * (Fintype.card ι + 1)) := by ring
          rw [hdouble]
          omega)
      simpa [source, Nat.add_assoc] using ih.freshXor.reindex e

theorem HStar_parityBlockXor_le
    (C : SparseMonomialCertificate ι T) (k : ℕ) :
    HStar (m + k) (parityBlockXor k T) ≤
      2 ^ k * (Fintype.card ι + 1) - 1 := by
  have h := (C.parityBlock k).HStar_le_card
  simpa [ParitySparseIndex] using h

end SparseMonomialCertificate

namespace SquarefreePolynomial

theorem eval_eq_constant_add_nonconstantSupport
    (P : SquarefreePolynomial m) (bits : Fin m → Bool) :
    P.eval bits = P.coeff ∅ +
      ∑ S ∈ P.nonconstantSupport,
        P.coeff S * squarefreeMonomial S bits := by
  classical
  let term : Finset (Fin m) → ℝ :=
    fun S ↦ P.coeff S * squarefreeMonomial S bits
  have hsupp : P.nonconstantSupport ⊆
      (Finset.univ : Finset (Finset (Fin m))).erase ∅ := by
    intro S hS
    simp only [nonconstantSupport, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS
    exact Finset.mem_erase.mpr ⟨hS.1.ne_empty, Finset.mem_univ S⟩
  have hsum :
      (∑ S ∈ P.nonconstantSupport, term S) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).erase ∅, term S := by
    apply Finset.sum_subset hsupp
    intro S hS hnot
    have hne : S.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
    have hcoeff : P.coeff S = 0 := by
      by_contra hc
      exact hnot (by simp [nonconstantSupport, hne, hc])
    simp [term, hcoeff]
  calc
    P.eval bits = ∑ S : Finset (Fin m), term S := by
      simpa [term] using (P.fullSum_eq_eval bits).symm
    _ = (∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).erase ∅,
          term S) + term ∅ := by
      exact (Finset.sum_erase_add
        (Finset.univ : Finset (Finset (Fin m))) term
        (Finset.mem_univ (∅ : Finset (Fin m)))).symm
    _ = P.coeff ∅ +
        ∑ S ∈ P.nonconstantSupport,
          P.coeff S * squarefreeMonomial S bits := by
      rw [← hsum]
      simp [term, squarefreeMonomial, add_comm]

/-- A strict squarefree sign polynomial gives its canonical sparse-monomial
certificate, with one index per nonconstant monomial in its support. -/
noncomputable def sparseMonomialCertificate
    (P : SquarefreePolynomial m) (T : (Fin m → Bool) → Bool)
    (hP : P.StrictSignRepresents T) :
    SparseMonomialCertificate
      {S // S ∈ P.nonconstantSupport} T where
  bias := P.coeff ∅
  coefficient := fun S ↦ P.coeff S.1
  support := fun S ↦ S.1
  strict := by
    intro bits
    have hsum :
        (∑ S : {S // S ∈ P.nonconstantSupport},
            P.coeff S.1 * squarefreeMonomial S.1 bits) =
          ∑ S ∈ P.nonconstantSupport,
            P.coeff S * squarefreeMonomial S bits := by
      rw [← P.nonconstantSupport.sum_attach, Finset.attach_eq_univ]
    change
      ((0 < P.coeff ∅ +
          ∑ S : {S // S ∈ P.nonconstantSupport},
            P.coeff S.1 * squarefreeMonomial S.1 bits ↔ T bits = true) ∧
        P.coeff ∅ +
          ∑ S : {S // S ∈ P.nonconstantSupport},
            P.coeff S.1 * squarefreeMonomial S.1 bits ≠ 0)
    rw [hsum, ← P.eval_eq_constant_add_nonconstantSupport]
    exact hP bits

end SquarefreePolynomial

/-- Sparse-PTF fallback from a fixed strict polynomial certificate. -/
theorem HStar_parityBlockXor_le_ptfSupportCost
    (k : ℕ) (T : (Fin m → Bool) → Bool) (P : SquarefreePolynomial m)
    (hP : P.StrictSignRepresents T) :
    HStar (m + k) (parityBlockXor k T) ≤
      2 ^ k * (P.ptfSupportCost + 1) - 1 := by
  have h := (P.sparseMonomialCertificate T hP).HStar_parityBlockXor_le k
  simpa [SquarefreePolynomial.ptfSupportCost] using h

/-- Sparse-PTF fallback in terms of the minimum polynomial-threshold
sparsity of the base feature. -/
theorem HStar_parityBlockXor_le_ptfSparsity
    (k : ℕ) (T : (Fin m → Bool) → Bool) :
    HStar (m + k) (parityBlockXor k T) ≤
      2 ^ k * (ptfSparsity T + 1) - 1 := by
  obtain ⟨P, hP, hcost⟩ := ptfSparsity_spec T
  obtain ⟨Q, hQ, -, hQcost⟩ := P.exists_strictification T hP
  calc
    HStar (m + k) (parityBlockXor k T) ≤
        2 ^ k * (Q.ptfSupportCost + 1) - 1 :=
      HStar_parityBlockXor_le_ptfSupportCost k T Q hQ
    _ = 2 ^ k * (ptfSparsity T + 1) - 1 := by rw [hQcost, hcost]

end HeadComplexity
