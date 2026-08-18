import HeadComplexity.Atoms.PositiveStatisticRawBit
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.PositiveProjection

set_option linter.style.header false

/-!
# Positive-order one-bit gate bounds

The raw-bit compiler turns a positive weighted sign polynomial for a feature
into gate certificates with the same number of heads, except for XOR and XNOR,
which use one additional head.  Combining this construction with the exact
one-bit threshold-degree classification gives the theorem 144 sandwich and the
theorem 141 exact table when the two feature invariants coincide.
-/

namespace HeadComplexity

open Finset Polynomial
open scoped BigOperators

variable {m K : ℕ}

/-- Head-complexity form of theorem 138. -/
theorem HStar_le_of_positiveStatisticRawBitDegLE
    {f : (Fin (m + 1) → Bool) → Bool}
    (h : PositiveStatisticRawBitDegLE f K) (hK : 0 < K) :
    HStar (m + 1) f ≤ K :=
  HStar_le_of_computableWithHeadsN (h.computable hK)

/-- A uniform strict bound for a univariate polynomial evaluated on a finite
Boolean cube. -/
noncomputable def univariateCubeStrictBound (P : ℝ[X]) (lam : Fin m → ℝ) : ℝ :=
  1 + ∑ y : Fin m → Bool, |P.eval (wT lam y)|

theorem abs_eval_lt_univariateCubeStrictBound
    (P : ℝ[X]) (lam : Fin m → ℝ) (y : Fin m → Bool) :
    |P.eval (wT lam y)| < univariateCubeStrictBound P lam := by
  classical
  have hle : |P.eval (wT lam y)| ≤
      ∑ z : Fin m → Bool, |P.eval (wT lam z)| :=
    Finset.single_le_sum (fun z _ ↦ abs_nonneg (P.eval (wT lam z)))
      (Finset.mem_univ y)
  unfold univariateCubeStrictBound
  linarith

/-- A strict positive-statistic certificate remains computable after adding
an ignored fresh coordinate. -/
theorem strictPositiveStatistic_ignoreFresh_computable
    {f : (Fin m → Bool) → Bool}
    (lam : Fin m → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : ℝ[X]) (hP : P.natDegree ≤ K)
    (hstrict : StrictUnivariateSignRep P (wT lam) f)
    (hK : 0 < K) :
    computableWithHeadsN (m + 1) K (fun x ↦ f (tailBits x)) := by
  apply PositiveStatisticRawBitDegLE.computable (K := K) (hK := hK)
  refine ⟨lam, hlam, P, 0, hP, ?_, ?_⟩
  · simpa using hK
  · intro z y
    simpa using hstrict.signRepresents y

set_option linter.flexible false in
/-- A strict positive-statistic feature may occupy either raw-bit slice while
the other slice is an arbitrary constant, at no additional head cost. -/
theorem strictPositiveStatistic_oneSliceFeature_computable
    {f : (Fin m → Bool) → Bool}
    (lam : Fin m → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : ℝ[X]) (hP : P.natDegree ≤ K)
    (hstrict : StrictUnivariateSignRep P (wT lam) f)
    (hK : 0 < K) (active constant : Bool) :
    computableWithHeadsN (m + 1) K
      (oneSliceFeature active constant f) := by
  let M := univariateCubeStrictBound P lam
  let s : ℝ := if constant then M else -M
  let P0 : ℝ[X] := if active then P + C s else P
  let R : ℝ[X] := if active then C (-s) else C s
  apply PositiveStatisticRawBitDegLE.computable (K := K) (hK := hK)
  refine ⟨lam, hlam, P0, R, ?_, ?_, ?_⟩
  · dsimp [P0]
    split
    · exact (natDegree_add_le P (C s)).trans
        (max_le hP (by simp))
    · exact hP
  · dsimp [R]
    split <;> simp only [natDegree_C] <;> omega
  · intro z y
    have habs := abs_eval_lt_univariateCubeStrictBound P lam y
    have hlo : -M < P.eval (wT lam y) := by
      exact neg_lt_of_abs_lt (by simpa [M] using habs)
    have hhi : P.eval (wT lam y) < M := by
      exact lt_of_abs_lt (by simpa [M] using habs)
    cases active <;> cases z <;> cases constant <;>
      simp [P0, R, s, oneSliceFeature, boolToReal] <;>
      first | exact hstrict.signRepresents y | linarith

/-- Fresh XOR of a strict positive-statistic feature costs one extra head. -/
theorem strictPositiveStatistic_freshXor_computable
    {f : (Fin m → Bool) → Bool}
    (lam : Fin m → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : ℝ[X]) (hP : P.natDegree ≤ K)
    (hstrict : StrictUnivariateSignRep P (wT lam) f) :
    computableWithHeadsN (m + 1) (K + 1) (freshXor f) := by
  let R : ℝ[X] := C (-2) * P
  apply PositiveStatisticRawBitDegLE.computable (K := K + 1)
    (hK := Nat.succ_pos K)
  refine ⟨lam, hlam, P, R, hP.trans (Nat.le_succ K), ?_, ?_⟩
  · exact (natDegree_C_mul_le (-2) P).trans_lt
      (hP.trans_lt (Nat.lt_succ_self K))
  · intro z y
    cases z
    · simpa [R, freshXor, boolToReal] using hstrict.signRepresents y
    · cases hy : f y
      · have hp : P.eval (wT lam y) < 0 := (hstrict y).2 hy
        simp [R, freshXor, hy, boolToReal]
        linarith
      · have hp : 0 < P.eval (wT lam y) := (hstrict y).1 hy
        simp [R, freshXor, hy, boolToReal]
        linarith

/-- Fresh XNOR of a strict positive-statistic feature costs one extra head. -/
theorem strictPositiveStatistic_freshXnor_computable
    {f : (Fin m → Bool) → Bool}
    (lam : Fin m → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : ℝ[X]) (hP : P.natDegree ≤ K)
    (hstrict : StrictUnivariateSignRep P (wT lam) f) :
    computableWithHeadsN (m + 1) (K + 1)
      (complementFn (freshXor f)) := by
  let R : ℝ[X] := C 2 * P
  apply PositiveStatisticRawBitDegLE.computable (K := K + 1)
    (hK := Nat.succ_pos K)
  refine ⟨lam, hlam, -P, R, ?_, ?_, ?_⟩
  · simpa using hP.trans (Nat.le_succ K)
  · exact (natDegree_C_mul_le 2 P).trans_lt
      (hP.trans_lt (Nat.lt_succ_self K))
  · intro z y
    cases z
    · cases hy : f y
      · have hp : P.eval (wT lam y) < 0 := (hstrict y).2 hy
        simp [R, freshXor, complementFn, hy, boolToReal]
        linarith
      · have hp : 0 < P.eval (wT lam y) := (hstrict y).1 hy
        simp [R, freshXor, complementFn, hy, boolToReal]
        linarith
    · have heval : (-P).eval (wT lam y) +
          boolToReal true * R.eval (wT lam y) = P.eval (wT lam y) := by
        simp [R, boolToReal]
        ring
      rw [heval]
      simpa [freshXor, complementFn] using hstrict.signRepresents y

/-! ## Gate upper bounds -/

/-- Constant functions have zero head complexity. -/
theorem HStar_constantFn (c : Bool) :
    HStar m (fun _ : Fin m → Bool ↦ c) = 0 :=
  (HStar_eq_zero_iff _).2 (fun _ _ ↦ rfl)

/-- The fresh raw bit is a nonconstant affine threshold and hence has exactly
one head. -/
theorem HStar_freshRawBit :
    HStar (m + 1) (fun x : Fin (m + 1) → Bool ↦ x 0) = 1 := by
  apply (HStar_eq_one_iff _).2
  constructor
  · intro hc
    have h := hc (consBit false fun _ ↦ false)
      (consBit true fun _ ↦ false)
    simp at h
  · refine ⟨-(1 / 2 : ℝ), Fin.cases 1 (fun _ ↦ 0), ?_⟩
    intro x
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, one_mul, Fin.cases_succ, zero_mul,
      Finset.sum_const_zero, add_zero]
    cases hx : x 0 <;> norm_num [boolToReal]

/-- The complemented fresh raw bit also has exactly one head. -/
theorem HStar_freshRawBitComplement :
    HStar (m + 1) (fun x : Fin (m + 1) → Bool ↦ !(x 0)) = 1 := by
  apply (HStar_eq_one_iff _).2
  constructor
  · intro hc
    have h := hc (consBit false fun _ ↦ false)
      (consBit true fun _ ↦ false)
    simp at h
  · refine ⟨(1 / 2 : ℝ), Fin.cases (-1) (fun _ ↦ 0), ?_⟩
    intro x
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, zero_mul,
      Finset.sum_const_zero, add_zero]
    cases hx : x 0 <;> norm_num [boolToReal]

/-- When the feature is constant, every gate reduces exactly to a constant or
a raw-bit literal. -/
theorem oneBitGate_HStar_constantFeature (c : Bool)
    (G : Bool → Bool → Bool) :
    HStar (m + 1) (freshBitGate G (fun _ : Fin m → Bool ↦ c)) =
      if G false c = G true c then 0 else 1 := by
  generalize h0 : G false c = a
  generalize h1 : G true c = b
  cases a <;> cases b
  · rw [show freshBitGate G (fun _ : Fin m → Bool ↦ c) =
        (fun _ : Fin (m + 1) → Bool ↦ false) by
      funext x
      cases hx : x 0 <;> simp [freshBitGate, hx, h0, h1]]
    simp [HStar_constantFn]
  · rw [show freshBitGate G (fun _ : Fin m → Bool ↦ c) =
        (fun x : Fin (m + 1) → Bool ↦ x 0) by
      funext x
      cases hx : x 0 <;> simp [freshBitGate, hx, h0, h1]]
    simp [HStar_freshRawBit]
  · rw [show freshBitGate G (fun _ : Fin m → Bool ↦ c) =
        (fun x : Fin (m + 1) → Bool ↦ !(x 0)) by
      funext x
      cases hx : x 0 <;> simp [freshBitGate, hx, h0, h1]]
    simp [HStar_freshRawBitComplement]
  · rw [show freshBitGate G (fun _ : Fin m → Bool ↦ c) =
        (fun _ : Fin (m + 1) → Bool ↦ true) by
      funext x
      cases hx : x 0 <;> simp [freshBitGate, hx, h0, h1]]
    simp [HStar_constantFn]

/-- Extensional form of the constant-feature branch. -/
theorem oneBitGate_HStar_of_constant
    (T : (Fin m → Bool) → Bool) (hT : ∀ x y, T x = T y)
    (G : Bool → Bool → Bool) :
    HStar (m + 1) (freshBitGate G T) =
      if G false (T default) = G true (T default) then 0 else 1 := by
  have hTeq : T = fun _ ↦ T default := by
    funext y
    exact hT y default
  rw [hTeq]
  exact oneBitGate_HStar_constantFeature (T default) G

/-- Positive weighted sign degree gives the all-gates upper half of theorem
144 after the gate slices are put in canonical form. -/
theorem HStar_gateOfSliceKinds_le_positiveWeightedSignDeg
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (k0 k1 : UnarySliceKind) :
    HStar (m + 1) (freshBitGate (gateOfSliceKinds k0 k1) T) ≤
      oneBitGateDegree (positiveWeightedSignDeg T) k0 k1 := by
  let K := positiveWeightedSignDeg T
  have hK : 0 < K := by
    have hdeg := thresholdDeg_pos_of_nonconstant hT
    have hle := thresholdDeg_le_positiveWeightedSignDeg T
    omega
  obtain ⟨lam, hlam, hpoly⟩ := positiveWeightedSignDeg_spec T
  obtain ⟨P, hP, hstrict⟩ :=
    exists_strictUnivariateSignRep_of_UnivariateThresholdDegLE hpoly
  cases k0 with
  | const c0 =>
      cases k1 with
      | const c1 =>
          cases c0 <;> cases c1
          · rw [show freshBitGate
                (gateOfSliceKinds (.const false) (.const false)) T =
                (fun _ : Fin (m + 1) → Bool ↦ false) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            simp [oneBitGateDegree, HStar_constantFn]
          · rw [show freshBitGate
                (gateOfSliceKinds (.const false) (.const true)) T =
                (fun x : Fin (m + 1) → Bool ↦ x 0) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            simp [oneBitGateDegree, HStar_freshRawBit]
          · rw [show freshBitGate
                (gateOfSliceKinds (.const true) (.const false)) T =
                (fun x : Fin (m + 1) → Bool ↦ !(x 0)) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            simp [oneBitGateDegree, HStar_freshRawBitComplement]
          · rw [show freshBitGate
                (gateOfSliceKinds (.const true) (.const true)) T =
                (fun _ : Fin (m + 1) → Bool ↦ true) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            simp [oneBitGateDegree, HStar_constantFn]
      | id =>
          change HStar (m + 1) (oneSliceFeature true c0 T) ≤ K
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_oneSliceFeature_computable
              lam hlam P hP hstrict hK true c0)
      | neg =>
          change HStar (m + 1)
            (oneSliceFeature true c0 (complementFn T)) ≤ K
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_oneSliceFeature_computable
              lam hlam (-P) (by simpa using hP) hstrict.neg hK true c0)
  | id =>
      cases k1 with
      | const c1 =>
          rw [show freshBitGate (gateOfSliceKinds .id (.const c1)) T =
              oneSliceFeature false c1 T by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, hx]]
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_oneSliceFeature_computable
              lam hlam P hP hstrict hK false c1)
      | id =>
          rw [show freshBitGate (gateOfSliceKinds .id .id) T =
              (fun x : Fin (m + 1) → Bool ↦ T (tailBits x)) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_ignoreFresh_computable
              lam hlam P hP hstrict hK)
      | neg =>
          rw [show freshBitGate (gateOfSliceKinds .id .neg) T = freshXor T by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, freshXor, gateOfSliceKinds,
                UnarySliceKind.eval, hx]]
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_freshXor_computable
              lam hlam P hP hstrict)
  | neg =>
      cases k1 with
      | const c1 =>
          rw [show freshBitGate (gateOfSliceKinds .neg (.const c1)) T =
              oneSliceFeature false c1 (complementFn T) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, complementFn, hx]]
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_oneSliceFeature_computable
              lam hlam (-P) (by simpa using hP) hstrict.neg hK false c1)
      | id =>
          rw [show freshBitGate (gateOfSliceKinds .neg .id) T =
              complementFn (freshXor T) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, freshXor, gateOfSliceKinds,
                UnarySliceKind.eval, complementFn, hx]]
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_freshXnor_computable
              lam hlam P hP hstrict)
      | neg =>
          rw [show freshBitGate (gateOfSliceKinds .neg .neg) T =
              (fun x : Fin (m + 1) → Bool ↦ complementFn T (tailBits x)) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                complementFn, hx]]
          change HStar (m + 1)
            (fun x : Fin (m + 1) → Bool ↦ complementFn T (tailBits x)) ≤ K
          exact HStar_le_of_computableWithHeadsN
            (strictPositiveStatistic_ignoreFresh_computable
              lam hlam (-P) (by simpa using hP) hstrict.neg hK)

/-! ## Theorem 144 sandwich and theorem 141 exactness -/

/-- Canonical-slice form of the all-gates sandwich. -/
theorem gateOfSliceKinds_HStar_sandwich_positiveWeightedSignDeg
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (k0 k1 : UnarySliceKind) :
    oneBitGateDegree (thresholdDeg T) k0 k1 ≤
        HStar (m + 1) (freshBitGate (gateOfSliceKinds k0 k1) T) ∧
      HStar (m + 1) (freshBitGate (gateOfSliceKinds k0 k1) T) ≤
        oneBitGateDegree (positiveWeightedSignDeg T) k0 k1 := by
  constructor
  · rw [← thresholdDeg_gateOfSliceKinds T hT k0 k1]
    exact thresholdDeg_le_HStar _
  · exact HStar_gateOfSliceKinds_le_positiveWeightedSignDeg T hT k0 k1

/-- Theorem 144 in the polynomial presentation of the positive-order
invariant.  Classifying both unary gate slices gives simultaneous lower and
upper bounds for every two-input Boolean gate. -/
theorem oneBitGate_HStar_sandwich_positiveWeightedSignDeg
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (G : Bool → Bool → Bool) :
    oneBitGateDegree (thresholdDeg T)
          (UnarySliceKind.classify (G false))
          (UnarySliceKind.classify (G true)) ≤
        HStar (m + 1) (freshBitGate G T) ∧
      HStar (m + 1) (freshBitGate G T) ≤
        oneBitGateDegree (positiveWeightedSignDeg T)
          (UnarySliceKind.classify (G false))
          (UnarySliceKind.classify (G true)) := by
  let k0 := UnarySliceKind.classify (G false)
  let k1 := UnarySliceKind.classify (G true)
  rw [freshBitGate_eq_gateOfSliceKinds G T k0 k1
    (fun u ↦ (UnarySliceKind.eval_classify (G false) u).symm)
    (fun u ↦ (UnarySliceKind.eval_classify (G true) u).symm)]
  exact gateOfSliceKinds_HStar_sandwich_positiveWeightedSignDeg T hT k0 k1

/-- Theorem 144 in the literal optimized positive-projection presentation. -/
theorem oneBitGate_HStar_sandwich_positiveProjection
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (G : Bool → Bool → Bool) :
    oneBitGateDegree (thresholdDeg T)
          (UnarySliceKind.classify (G false))
          (UnarySliceKind.classify (G true)) ≤
        HStar (m + 1) (freshBitGate G T) ∧
      HStar (m + 1) (freshBitGate G T) ≤
        oneBitGateDegree (positiveProjectionSignChanges T)
          (UnarySliceKind.classify (G false))
          (UnarySliceKind.classify (G true)) := by
  rw [positiveProjectionSignChanges_eq_positiveWeightedSignDeg]
  exact oneBitGate_HStar_sandwich_positiveWeightedSignDeg T hT G

/-- Theorem 141 in the polynomial presentation.  If positive weighted sign
degree is threshold-degree tight for the feature, the complete gate table is
exact. -/
theorem oneBitGate_HStar_exact_of_degree_tight_positiveWeightedSignDeg
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (htight : thresholdDeg T = positiveWeightedSignDeg T)
    (G : Bool → Bool → Bool) :
    HStar (m + 1) (freshBitGate G T) =
      oneBitGateDegree (thresholdDeg T)
        (UnarySliceKind.classify (G false))
        (UnarySliceKind.classify (G true)) := by
  have hs := oneBitGate_HStar_sandwich_positiveWeightedSignDeg T hT G
  rw [← htight] at hs
  exact Nat.le_antisymm hs.2 hs.1

/-- Theorem 141 in the literal positive-projection presentation. -/
theorem oneBitGate_HStar_exact_of_degree_tight_positiveProjection
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (htight : thresholdDeg T = positiveProjectionSignChanges T)
    (G : Bool → Bool → Bool) :
    HStar (m + 1) (freshBitGate G T) =
      oneBitGateDegree (thresholdDeg T)
        (UnarySliceKind.classify (G false))
        (UnarySliceKind.classify (G true)) := by
  apply oneBitGate_HStar_exact_of_degree_tight_positiveWeightedSignDeg T hT
  rwa [← positiveProjectionSignChanges_eq_positiveWeightedSignDeg]

end HeadComplexity
