import HeadComplexity.Polynomial.FreshBit
import HeadComplexity.Results.ThresholdDegree

set_option linter.style.header false

/-!
# One-bit gate threshold-degree trichotomy

For a nonconstant Boolean feature `T`, adjoining a fresh raw bit and applying
any two-input Boolean gate has one of four threshold degrees: `0`, `1`,
`thresholdDeg T`, or `thresholdDeg T + 1`.  Constant gates and raw-bit literals
give the first two cases.  XOR and XNOR give the last case.  Every remaining
feature-dependent gate preserves threshold degree.
-/

namespace HeadComplexity

open Finset MvPolynomial

variable {m d e : ℕ}

/-- Pointwise Boolean complement. -/
def complementFn (f : (Fin m → Bool) → Bool) : (Fin m → Bool) → Bool :=
  fun y ↦ !(f y)

/-- Apply a two-input gate to a fresh first bit and an `m`-bit feature. -/
def freshBitGate (G : Bool → Bool → Bool)
    (T : (Fin m → Bool) → Bool) : (Fin (m + 1) → Bool) → Bool :=
  fun x ↦ G (x 0) (T (tailBits x))

/-- XOR a feature with a fresh first bit. -/
def freshXor (T : (Fin m → Bool) → Bool) :
    (Fin (m + 1) → Bool) → Bool :=
  freshBitGate xor T

@[simp] theorem complementFn_apply
    (f : (Fin m → Bool) → Bool) (y : Fin m → Bool) :
    complementFn f y = !(f y) := rfl

@[simp] theorem complementFn_complementFn
    (f : (Fin m → Bool) → Bool) :
    complementFn (complementFn f) = f := by
  funext y
  simp [complementFn]

@[simp] theorem freshBitGate_consBit (G : Bool → Bool → Bool)
    (T : (Fin m → Bool) → Bool) (z : Bool) (y : Fin m → Bool) :
    freshBitGate G T (consBit z y) = G z (T y) := by
  simp [freshBitGate]

@[simp] theorem freshXor_consBit
    (T : (Fin m → Bool) → Bool) (z : Bool) (y : Fin m → Bool) :
    freshXor T (consBit z y) = xor z (T y) := by
  simp [freshXor]

/-! ## General threshold-degree infrastructure -/

/-- Strict signs imply the classifier convention used by `SignRepresents`. -/
theorem StrictSignRep.signRepresents
    {P : MvPolynomial (Fin m) ℝ} {f : (Fin m → Bool) → Bool}
    (h : StrictSignRep P f) : SignRepresents P f := by
  intro y
  cases hy : f y
  · simp only [Bool.false_eq_true, iff_false]
    exact not_lt_of_ge (le_of_lt ((h y).2 hy))
  · simp only [iff_true]
    exact (h y).1 hy

/-- Complementing a function preserves every threshold-degree upper bound. -/
theorem ThresholdDegLE.complement
    {f : (Fin m → Bool) → Bool} (h : ThresholdDegLE f d) :
    ThresholdDegLE (complementFn f) d := by
  obtain ⟨P, hPdeg, hPstrict⟩ := exists_strictSignRep_of_ThresholdDegLE h
  refine ⟨-P, ?_, ?_⟩
  · simpa using hPdeg
  · intro y
    rw [map_neg]
    cases hy : f y
    · simp only [complementFn, hy, Bool.not_false, iff_true]
      linarith [(hPstrict y).2 hy]
    · simp only [complementFn, hy, Bool.not_true, Bool.false_eq_true, iff_false]
      linarith [(hPstrict y).1 hy]

/-- Threshold degree is invariant under output complement. -/
theorem thresholdDeg_complement (f : (Fin m → Bool) → Bool) :
    thresholdDeg (complementFn f) = thresholdDeg f := by
  apply Nat.le_antisymm
  · exact thresholdDeg_le_of_ThresholdDegLE (thresholdDeg_spec f).complement
  · have h := (thresholdDeg_spec (complementFn f)).complement
    simpa using thresholdDeg_le_of_ThresholdDegLE h

/-- Specializing the fresh bit preserves a threshold-degree certificate. -/
theorem ThresholdDegLE.freshSlice
    {F : (Fin (m + 1) → Bool) → Bool} (h : ThresholdDegLE F e)
    (z : Bool) :
    ThresholdDegLE (fun y ↦ F (consBit z y)) e := by
  obtain ⟨P, hPdeg, hPsign⟩ := h
  refine ⟨freshSlicePolynomial z P,
    (freshSlicePolynomial_totalDegree_le z P).trans hPdeg, ?_⟩
  intro y
  rw [freshSlicePolynomial_eval]
  exact hPsign (consBit z y)

/-- Restricting the fresh bit cannot increase minimum threshold degree. -/
theorem thresholdDeg_freshSlice_le
    (F : (Fin (m + 1) → Bool) → Bool) (z : Bool) :
    thresholdDeg (fun y ↦ F (consBit z y)) ≤ thresholdDeg F :=
  thresholdDeg_le_of_ThresholdDegLE ((thresholdDeg_spec F).freshSlice z)

/-- A tail certificate lifts to a function which ignores the fresh bit. -/
theorem ThresholdDegLE.ignoreFresh
    {f : (Fin m → Bool) → Bool} (h : ThresholdDegLE f d) :
    ThresholdDegLE (fun x ↦ f (tailBits x)) d := by
  obtain ⟨P, hPdeg, hPsign⟩ := h
  refine ⟨liftFreshPolynomial P,
    (liftFreshPolynomial_totalDegree_le P).trans hPdeg, ?_⟩
  intro x
  rw [← consBit_head_tail x, liftFreshPolynomial_eval]
  exact hPsign (tailBits x)

/-- A function and the same function with an ignored fresh coordinate have the
same threshold degree. -/
theorem thresholdDeg_ignoreFresh (f : (Fin m → Bool) → Bool) :
    thresholdDeg (fun x ↦ f (tailBits x)) = thresholdDeg f := by
  apply Nat.le_antisymm
  · exact thresholdDeg_le_of_ThresholdDegLE (thresholdDeg_spec f).ignoreFresh
  · simpa using thresholdDeg_freshSlice_le
      (fun x ↦ f (tailBits x)) false

/-- Degree zero sign representations compute only constant Boolean functions. -/
theorem constant_of_ThresholdDegLE_zero
    {f : (Fin m → Bool) → Bool} (h : ThresholdDegLE f 0) :
    ∀ x y, f x = f y := by
  obtain ⟨P, hPdeg, hPsign⟩ := h
  have hPzero : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hPdeg
  have hPC : P = C (P.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hPzero
  intro x y
  have hxy : (f x = true) ↔ (f y = true) := by
    rw [← hPsign x, ← hPsign y, hPC]
    simp
  apply Bool.eq_iff_iff.mpr
  exact hxy

/-- Every nonconstant Boolean function has positive threshold degree. -/
theorem thresholdDeg_pos_of_nonconstant
    {f : (Fin m → Bool) → Bool} (hf : ¬ (∀ x y, f x = f y)) :
    0 < thresholdDeg f := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact hf (constant_of_ThresholdDegLE_zero (hzero ▸ thresholdDeg_spec f))

/-! ## Fresh XOR raises threshold degree -/

/-- A degree-`d` certificate for a feature gives a degree-`d+1` certificate
after XOR with a fresh bit. -/
theorem ThresholdDegLE.freshXor_succ
    {f : (Fin m → Bool) → Bool} (h : ThresholdDegLE f d) :
    ThresholdDegLE (freshXor f) (d + 1) := by
  obtain ⟨P, hPdeg, hPstrict⟩ := exists_strictSignRep_of_ThresholdDegLE h
  refine ⟨freshXorPolynomial P,
    freshXorPolynomial_totalDegree_le P d hPdeg, ?_⟩
  intro x
  let z := x 0
  let y := tailBits x
  have hx : x = consBit z y := by
    simp [z, y]
  rw [hx, freshXorPolynomial_eval, freshXor_consBit]
  cases z
  · simpa using hPstrict.signRepresents y
  · cases hy : f y
    · have hp : eval (cubePoint y) P < 0 := (hPstrict y).2 hy
      have hneg : 0 < -eval (cubePoint y) P := neg_pos.mpr hp
      simpa [hy] using hneg
    · have hp : 0 < eval (cubePoint y) P := (hPstrict y).1 hy
      have hneg : ¬ 0 < -eval (cubePoint y) P :=
        not_lt_of_ge (neg_nonpos.mpr hp.le)
      simpa [hy] using hneg

/-- The difference of the two fresh-XOR slices recovers a feature certificate
with one lower degree. -/
theorem ThresholdDegLE.of_freshXor
    {f : (Fin m → Bool) → Bool}
    (h : ThresholdDegLE (HeadComplexity.freshXor f) e) :
    ThresholdDegLE f (e - 1) := by
  obtain ⟨P, hPdeg, hPstrict⟩ := exists_strictSignRep_of_ThresholdDegLE h
  refine ⟨-freshDifferencePolynomial P, ?_, ?_⟩
  · simpa using (freshDifferencePolynomial_totalDegree_le P).trans
      (Nat.sub_le_sub_right hPdeg 1)
  · intro y
    rw [map_neg, freshDifferencePolynomial_eval]
    cases hy : f y
    · have h0 := (hPstrict (consBit false y)).2 (by simp [freshXor, hy])
      have h1 := (hPstrict (consBit true y)).1 (by simp [freshXor, hy])
      simp only [Bool.false_eq_true, iff_false]
      linarith
    · have h0 := (hPstrict (consBit false y)).1 (by simp [freshXor, hy])
      have h1 := (hPstrict (consBit true y)).2 (by simp [freshXor, hy])
      simp only [iff_true]
      linarith

/-- Fresh XOR is nonconstant, even when the underlying feature is constant. -/
theorem freshXor_nonconstant (f : (Fin m → Bool) → Bool) :
    ¬ (∀ x y, freshXor f x = freshXor f y) := by
  intro hconst
  let y : Fin m → Bool := fun _ ↦ false
  have h := hconst (consBit false y) (consBit true y)
  simp [freshXor] at h

/-- **Fresh-bit XOR theorem.** XOR with a fresh raw bit raises threshold degree
by exactly one. -/
theorem thresholdDeg_freshXor (f : (Fin m → Bool) → Bool) :
    thresholdDeg (freshXor f) = thresholdDeg f + 1 := by
  apply Nat.le_antisymm
  · exact thresholdDeg_le_of_ThresholdDegLE (thresholdDeg_spec f).freshXor_succ
  · have hback := thresholdDeg_le_of_ThresholdDegLE
        (ThresholdDegLE.of_freshXor (thresholdDeg_spec (freshXor f)))
    have hpos := thresholdDeg_pos_of_nonconstant (freshXor_nonconstant f)
    omega

/-- XNOR with a fresh bit has the same one-unit degree increase. -/
theorem thresholdDeg_freshXnor (f : (Fin m → Bool) → Bool) :
    thresholdDeg (complementFn (freshXor f)) = thresholdDeg f + 1 := by
  rw [thresholdDeg_complement, thresholdDeg_freshXor]

/-! ## Constant slices and one active feature slice -/

/-- A gate-shaped function with one feature slice and one constant slice. -/
def oneSliceFeature (active constant : Bool)
    (f : (Fin m → Bool) → Bool) : (Fin (m + 1) → Bool) → Bool :=
  fun x ↦ if x 0 = active then f (tailBits x) else constant

@[simp] theorem oneSliceFeature_consBit (active constant : Bool)
    (f : (Fin m → Bool) → Bool) (z : Bool) (y : Fin m → Bool) :
    oneSliceFeature active constant f (consBit z y) =
      if z = active then f y else constant := by
  simp [oneSliceFeature]

/-- Polynomial indicator of the slice on which the feature is inactive. -/
noncomputable def inactiveSlicePolynomial (active : Bool) :
    MvPolynomial (Fin (m + 1)) ℝ :=
  if active then C 1 - X 0 else X 0

@[simp] theorem inactiveSlicePolynomial_eval (active z : Bool)
    (y : Fin m → Bool) :
    eval (cubePoint (consBit z y)) (inactiveSlicePolynomial active) =
      if z = active then 0 else 1 := by
  cases active <;> cases z <;>
    simp [inactiveSlicePolynomial, cubePoint, boolToReal]

theorem inactiveSlicePolynomial_totalDegree_le (active : Bool) :
    (inactiveSlicePolynomial active : MvPolynomial (Fin (m + 1)) ℝ).totalDegree ≤ 1 := by
  cases active
  · simp [inactiveSlicePolynomial]
  · exact (totalDegree_sub _ _).trans (by simp)

/-- A uniform strict bound for the values of a polynomial on the finite cube. -/
noncomputable def cubeStrictBound (P : MvPolynomial (Fin m) ℝ) : ℝ :=
  1 + ∑ y : Fin m → Bool, |eval (cubePoint y) P|

theorem abs_eval_lt_cubeStrictBound (P : MvPolynomial (Fin m) ℝ)
    (y : Fin m → Bool) :
    |eval (cubePoint y) P| < cubeStrictBound P := by
  classical
  have hle : |eval (cubePoint y) P| ≤
      ∑ z : Fin m → Bool, |eval (cubePoint z) P| :=
    Finset.single_le_sum (fun z _ ↦ abs_nonneg (eval (cubePoint z) P))
      (Finset.mem_univ y)
  unfold cubeStrictBound
  linarith

/-- A degree-`d`, nonconstant feature certificate extends across one arbitrary
constant fresh-bit slice without increasing degree. -/
theorem ThresholdDegLE.oneSliceFeature
    {f : (Fin m → Bool) → Bool} (h : ThresholdDegLE f d)
    (hd : 1 ≤ d) (active constant : Bool) :
    ThresholdDegLE (oneSliceFeature active constant f) d := by
  obtain ⟨P, hPdeg, hPstrict⟩ := exists_strictSignRep_of_ThresholdDegLE h
  let M := cubeStrictBound P
  let Q : MvPolynomial (Fin (m + 1)) ℝ :=
    liftFreshPolynomial P +
      (if constant then C M else C (-M)) * inactiveSlicePolynomial active
  refine ⟨Q, ?_, ?_⟩
  · unfold Q
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (liftFreshPolynomial_totalDegree_le P).trans hPdeg
    · refine (totalDegree_mul _ _).trans ?_
      have hconst :
          (if constant then C M else C (-M) :
            MvPolynomial (Fin (m + 1)) ℝ).totalDegree ≤ 0 := by
        cases constant <;> simp
      exact (Nat.add_le_add hconst
        (inactiveSlicePolynomial_totalDegree_le active)).trans (by omega)
  · intro x
    let z := x 0
    let y := tailBits x
    have hx : x = consBit z y := by
      simp [z, y]
    rw [hx]
    change 0 < eval (cubePoint (consBit z y)) Q ↔ _
    have hQeval : eval (cubePoint (consBit z y)) Q =
        eval (cubePoint y) P +
          (if constant then M else -M) * (if z = active then 0 else 1) := by
      cases active <;> cases z <;> cases constant <;>
        simp [Q, inactiveSlicePolynomial, cubePoint, boolToReal, consBit]
    rw [hQeval, oneSliceFeature_consBit]
    by_cases hza : z = active
    · rw [if_pos hza, if_pos hza]
      simpa only [mul_zero, add_zero] using hPstrict.signRepresents y
    · rw [if_neg hza, if_neg hza]
      simp only [mul_one]
      have habs := abs_eval_lt_cubeStrictBound P y
      have hlo : -M < eval (cubePoint y) P := by
        dsimp [M]
        exact (neg_lt_of_abs_lt habs)
      have hhi : eval (cubePoint y) P < M := by
        dsimp [M]
        exact (lt_of_abs_lt habs)
      cases constant
      · simp only [if_false, Bool.false_eq_true, iff_false]
        linarith
      · simp only [if_true, iff_true]
        linarith

/-- A nonconstant feature has exactly the same threshold degree when placed on
one fresh-bit slice and made constant on the other. -/
theorem thresholdDeg_oneSliceFeature
    (f : (Fin m → Bool) → Bool) (hf : ¬ (∀ x y, f x = f y))
    (active constant : Bool) :
    thresholdDeg (oneSliceFeature active constant f) = thresholdDeg f := by
  apply Nat.le_antisymm
  · exact thresholdDeg_le_of_ThresholdDegLE
      ((thresholdDeg_spec f).oneSliceFeature
        (thresholdDeg_pos_of_nonconstant hf) active constant)
  · have hs := thresholdDeg_freshSlice_le
        (oneSliceFeature active constant f) active
    simpa using hs

/-- Constant Boolean functions have threshold degree zero. -/
theorem thresholdDeg_constant (c : Bool) :
    thresholdDeg (fun _ : Fin m → Bool ↦ c) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply thresholdDeg_le_of_ThresholdDegLE
  refine ⟨if c then C 1 else 0, ?_, ?_⟩
  · cases c <;> simp
  · intro x
    cases c <;> simp

/-- The fresh raw bit and its complement both have threshold degree one. -/
theorem thresholdDeg_freshRawBit :
    thresholdDeg (fun x : Fin (m + 1) → Bool ↦ x 0) = 1 := by
  apply Nat.le_antisymm
  · apply thresholdDeg_le_of_ThresholdDegLE
    refine ⟨X 0, by simp, ?_⟩
    intro x
    cases h : x 0 <;> simp [cubePoint, boolToReal, h]
  · have hnon : ¬ (∀ x y : Fin (m + 1) → Bool, x 0 = y 0) := by
      intro h
      have := h (consBit false fun _ ↦ false) (consBit true fun _ ↦ false)
      simp at this
    exact thresholdDeg_pos_of_nonconstant hnon

theorem thresholdDeg_freshRawBitComplement :
    thresholdDeg (fun x : Fin (m + 1) → Bool ↦ !(x 0)) = 1 := by
  change thresholdDeg (complementFn (fun x : Fin (m + 1) → Bool ↦ x 0)) = 1
  rw [thresholdDeg_complement, thresholdDeg_freshRawBit]

/-! ## Exhaustive gate classification -/

/-- Every unary Boolean slice is constant, the identity, or negation. -/
inductive UnarySliceKind where
  | const (c : Bool)
  | id
  | neg
  deriving DecidableEq

namespace UnarySliceKind

/-- Evaluate the canonical unary function represented by a slice kind. -/
def eval : UnarySliceKind → Bool → Bool
  | .const c, _ => c
  | .id, u => u
  | .neg, u => !u

/-- Classify a unary Boolean function from its two values. -/
def classify (U : Bool → Bool) : UnarySliceKind :=
  if U false = U true then .const (U false)
  else if U false then .neg else .id

@[simp] theorem eval_classify (U : Bool → Bool) (u : Bool) :
    (classify U).eval u = U u := by
  cases h0 : U false <;> cases h1 : U true <;> cases u <;>
    simp [classify, eval, h0, h1]

end UnarySliceKind

/-- The threshold-degree outcome associated with the two unary gate slices. -/
def oneBitGateDegree (d : ℕ) : UnarySliceKind → UnarySliceKind → ℕ
  | .const a, .const b => if a = b then 0 else 1
  | .id, .neg => d + 1
  | .neg, .id => d + 1
  | _, _ => d

/-- Canonical two-input gate associated with a pair of unary slice kinds. -/
def gateOfSliceKinds (k0 k1 : UnarySliceKind) : Bool → Bool → Bool :=
  fun z u ↦ if z then k1.eval u else k0.eval u

/-- Complementing a nonconstant feature preserves nonconstancy. -/
theorem complementFn_nonconstant
    {f : (Fin m → Bool) → Bool} (hf : ¬ (∀ x y, f x = f y)) :
    ¬ (∀ x y, complementFn f x = complementFn f y) := by
  intro hc
  apply hf
  intro x y
  have h := hc x y
  exact Bool.not_inj h

/-- Replacing a gate by extensionally equal unary slices does not change the
fresh-bit gate function. -/
theorem freshBitGate_eq_gateOfSliceKinds
    (G : Bool → Bool → Bool) (T : (Fin m → Bool) → Bool)
    (k0 k1 : UnarySliceKind)
    (h0 : ∀ u, G false u = k0.eval u)
    (h1 : ∀ u, G true u = k1.eval u) :
    freshBitGate G T = freshBitGate (gateOfSliceKinds k0 k1) T := by
  funext x
  rw [← consBit_head_tail x]
  cases hz : x 0 <;>
    simp [freshBitGate, gateOfSliceKinds, h0, h1]

/-- Threshold degree for a gate whose two unary slices have already been put
in canonical form. -/
theorem thresholdDeg_gateOfSliceKinds
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (k0 k1 : UnarySliceKind) :
    thresholdDeg (freshBitGate (gateOfSliceKinds k0 k1) T) =
      oneBitGateDegree (thresholdDeg T) k0 k1 := by
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
            exact thresholdDeg_constant false
          · rw [show freshBitGate
                (gateOfSliceKinds (.const false) (.const true)) T =
                (fun x : Fin (m + 1) → Bool ↦ x 0) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            exact thresholdDeg_freshRawBit
          · rw [show freshBitGate
                (gateOfSliceKinds (.const true) (.const false)) T =
                (fun x : Fin (m + 1) → Bool ↦ !(x 0)) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            exact thresholdDeg_freshRawBitComplement
          · rw [show freshBitGate
                (gateOfSliceKinds (.const true) (.const true)) T =
                (fun _ : Fin (m + 1) → Bool ↦ true) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            exact thresholdDeg_constant true
      | id =>
          change thresholdDeg (oneSliceFeature true c0 T) = thresholdDeg T
          exact thresholdDeg_oneSliceFeature T hT true c0
      | neg =>
          change thresholdDeg (oneSliceFeature true c0 (complementFn T)) =
            thresholdDeg T
          rw [thresholdDeg_oneSliceFeature (complementFn T)
            (complementFn_nonconstant hT) true c0, thresholdDeg_complement]
  | id =>
      cases k1 with
      | const c1 =>
          rw [show freshBitGate (gateOfSliceKinds .id (.const c1)) T =
              oneSliceFeature false c1 T by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, hx]]
          exact thresholdDeg_oneSliceFeature T hT false c1
      | id =>
          rw [show freshBitGate (gateOfSliceKinds .id .id) T =
              (fun x : Fin (m + 1) → Bool ↦ T (tailBits x)) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
          exact thresholdDeg_ignoreFresh T
      | neg =>
          rw [show freshBitGate (gateOfSliceKinds .id .neg) T = freshXor T by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, freshXor, gateOfSliceKinds,
                UnarySliceKind.eval, hx]]
          exact thresholdDeg_freshXor T
  | neg =>
      cases k1 with
      | const c1 =>
          rw [show freshBitGate (gateOfSliceKinds .neg (.const c1)) T =
              oneSliceFeature false c1 (complementFn T) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, complementFn, hx]]
          rw [thresholdDeg_oneSliceFeature (complementFn T)
            (complementFn_nonconstant hT) false c1, thresholdDeg_complement]
          simp [oneBitGateDegree]
      | id =>
          rw [show freshBitGate (gateOfSliceKinds .neg .id) T =
              complementFn (freshXor T) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, freshXor, gateOfSliceKinds,
                UnarySliceKind.eval, complementFn, hx]]
          exact thresholdDeg_freshXnor T
      | neg =>
          rw [show freshBitGate (gateOfSliceKinds .neg .neg) T =
              (fun x : Fin (m + 1) → Bool ↦ complementFn T (tailBits x)) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                complementFn, hx]]
          rw [thresholdDeg_ignoreFresh, thresholdDeg_complement]
          rfl

/-- **Theorem 82, one-bit gate threshold-degree trichotomy.** Classifying the
two unary slices of an arbitrary Boolean gate gives the exact threshold degree:
two constant slices give degree zero or one according as they agree; opposite
nonconstant slices give `d+1`; every other feature-dependent case gives `d`. -/
theorem oneBitGate_thresholdDeg_trichotomy
    (T : (Fin m → Bool) → Bool) (hT : ¬ (∀ x y, T x = T y))
    (G : Bool → Bool → Bool) :
    thresholdDeg (freshBitGate G T) =
      oneBitGateDegree (thresholdDeg T)
        (UnarySliceKind.classify (G false))
        (UnarySliceKind.classify (G true)) := by
  let k0 := UnarySliceKind.classify (G false)
  let k1 := UnarySliceKind.classify (G true)
  rw [freshBitGate_eq_gateOfSliceKinds G T k0 k1
    (fun u ↦ (UnarySliceKind.eval_classify (G false) u).symm)
    (fun u ↦ (UnarySliceKind.eval_classify (G true) u).symm)]
  exact thresholdDeg_gateOfSliceKinds T hT k0 k1

end HeadComplexity
