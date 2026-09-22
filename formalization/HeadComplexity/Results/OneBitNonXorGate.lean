import HeadComplexity.Atoms.FracAtomApproximation
import HeadComplexity.Atoms.UniformApproximation
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.PositiveOrderOneBitGate
import HeadComplexity.Results.StructuralInvariances

set_option linter.style.header false

/-!
# One-bit non-XOR gate recursion

Every two-input gate other than XOR and XNOR combines a fresh raw bit with an
arbitrary Boolean feature at a cost of at most one additional head.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {m H : ℕ}

/-- A fractional certificate can be shifted to make both Boolean classes
strict while preserving its atoms. -/
private theorem exists_strict_fracCertificate
    {f : (Fin m → Bool) → Bool} (hf : fracComputable m H f) :
    ∃ (phi : Fin H → FracAtom m) (c : ℝ),
      StrictSignRepresentsScore (fun y ↦ c + ∑ h, (phi h).eval y) f := by
  classical
  obtain ⟨phi, c, hphi⟩ := hf
  let score : (Fin m → Bool) → ℝ := fun y ↦ c + ∑ h, (phi h).eval y
  let trueInputs : Finset (Fin m → Bool) :=
    Finset.univ.filter fun y ↦ f y = true
  by_cases htrue : trueInputs.Nonempty
  · let margin : ℝ := trueInputs.inf' htrue score / 2
    have hmargin : 0 < margin := by
      apply half_pos
      rw [Finset.lt_inf'_iff]
      intro y hy
      exact (hphi y).mpr (Finset.mem_filter.mp hy).2
    refine ⟨phi, c - margin, fun y ↦ ?_⟩
    have hrewrite : c - margin + ∑ h, (phi h).eval y = score y - margin := by
      dsimp [score]
      ring
    change ((0 < c - margin + ∑ h, (phi h).eval y ↔ f y = true) ∧
      c - margin + ∑ h, (phi h).eval y ≠ 0)
    rw [hrewrite]
    cases hfy : f y with
    | false =>
        have hnpos : score y ≤ 0 := by
          apply le_of_not_gt
          intro hpos
          have := (hphi y).mp hpos
          simp [hfy] at this
        constructor
        · simp only [Bool.false_eq_true, iff_false]
          linarith
        · linarith
    | true =>
        have hy : y ∈ trueInputs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ y, hfy⟩
        have hle : trueInputs.inf' htrue score ≤ score y :=
          Finset.inf'_le score hy
        have hpos : 0 < score y - margin := by
          dsimp [margin] at hmargin ⊢
          linarith
        exact ⟨by simp [hpos], ne_of_gt hpos⟩
  · refine ⟨phi, c - 1, fun y ↦ ?_⟩
    have hfalse : f y = false := by
      cases hfy : f y with
      | false => rfl
      | true =>
          exact (htrue ⟨y,
            Finset.mem_filter.mpr ⟨Finset.mem_univ y, hfy⟩⟩).elim
    have hnpos : score y ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have := (hphi y).mp hpos
      simp [hfalse] at this
    have hrewrite : c - 1 + ∑ h, (phi h).eval y = score y - 1 := by
      dsimp [score]
      ring
    change ((0 < c - 1 + ∑ h, (phi h).eval y ↔ f y = true) ∧
      c - 1 + ∑ h, (phi h).eval y ≠ 0)
    rw [hrewrite]
    constructor
    · simp only [hfalse, Bool.false_eq_true, iff_false]
      linarith
    · linarith

/-- The score of one existing atom, pulled back along the tail coordinates,
is uniformly approximable by one ambient atom. -/
private theorem uniformlyOneAtomApproximable_tailFracAtom
    (phi : FracAtom m) :
    UniformlyOneAtomApproximable
      (fun x : Fin (m + 1) → Bool ↦ phi.eval (tailBits x)) := by
  intro tolerance htolerance
  let family : Fin 1 → FracAtom m := fun _ ↦ phi
  obtain ⟨epsilon, hepsilon, happrox⟩ :=
    exists_liftDummyAlong_uniform family 0 (Fin.succEmb m) tolerance htolerance
  refine ⟨phi.liftDummy (Fin.succEmb m) epsilon hepsilon, fun x ↦ ?_⟩
  have hx := happrox x
  have hpull : pullBitsAlong (Fin.succEmb m) x = tailBits x := by
    funext i
    rfl
  simpa [family, hpull] using hx

/-- Add one raw affine term to an existing family of tail-coordinate atoms.
The raw term consumes exactly the new head. -/
private theorem computableWithHeadsN_tailAtoms_add_raw
    (phi : Fin H → FracAtom m) (bias rawCoeff : ℝ)
    (f : (Fin (m + 1) → Bool) → Bool)
    (hstrict : StrictSignRepresentsScore
      (fun x ↦ bias + rawCoeff * boolToReal (x 0) +
        ∑ h, (phi h).eval (tailBits x)) f) :
    computableWithHeadsN (m + 1) (H + 1) f := by
  let g : Fin (H + 1) → (Fin (m + 1) → Bool) → ℝ :=
    Fin.cases (fun x ↦ rawCoeff * boolToReal (x 0))
      (fun h x ↦ (phi h).eval (tailBits x))
  refine computableWithHeadsN_of_uniformlyOneAtomApproximable
    (H := H + 1) g ?_ bias ?_
  · intro j
    refine Fin.cases ?_ (fun h ↦ ?_) j
    · let coeff : Fin (m + 1) → ℝ := Fin.cases rawCoeff (fun _ ↦ 0)
      have haffine := uniformlyOneAtomApproximable_affineValue 0 coeff
      have heq : affineValue 0 coeff =
          (fun x : Fin (m + 1) → Bool ↦ rawCoeff * boolToReal (x 0)) := by
        funext x
        unfold affineValue
        rw [Fin.sum_univ_succ]
        simp [coeff]
      rw [heq] at haffine
      simpa [g] using haffine
    · exact uniformlyOneAtomApproximable_tailFracAtom (phi h)
  · intro x
    change ((0 < bias + ∑ h, g h x ↔ f x = true) ∧
      bias + ∑ h, g h x ≠ 0)
    rw [Fin.sum_univ_succ]
    simpa [g, add_assoc] using hstrict x

/-- A uniform strict bound for a finite fractional score. -/
private noncomputable def fracScoreStrictBound
    (phi : Fin H → FracAtom m) (c : ℝ) : ℝ :=
  1 + ∑ y : Fin m → Bool, |c + ∑ h, (phi h).eval y|

private theorem abs_fracScore_lt_strictBound
    (phi : Fin H → FracAtom m) (c : ℝ) (y : Fin m → Bool) :
    |c + ∑ h, (phi h).eval y| < fracScoreStrictBound phi c := by
  classical
  have hle : |c + ∑ h, (phi h).eval y| ≤
      ∑ z : Fin m → Bool, |c + ∑ h, (phi h).eval z| :=
    Finset.single_le_sum
      (fun z _ ↦ abs_nonneg (c + ∑ h, (phi h).eval z))
      (Finset.mem_univ y)
  unfold fracScoreStrictBound
  linarith

/-- Placing an arbitrary feature on one fresh-bit slice and a constant on the
other costs at most one extra head. -/
theorem oneSliceFeature_computable_succ
    (f : (Fin m → Bool) → Bool) (hf : computableWithHeadsN m H f)
    (active constant : Bool) :
    computableWithHeadsN (m + 1) (H + 1)
      (oneSliceFeature active constant f) := by
  obtain ⟨phi, c, hstrict⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hf)
  let M := fracScoreStrictBound phi c
  have hbound (y : Fin m → Bool) :
      |c + ∑ h, (phi h).eval y| < M := by
    exact abs_fracScore_lt_strictBound phi c y
  cases active <;> cases constant
  · apply computableWithHeadsN_tailAtoms_add_raw phi c (-M)
    intro x
    have hs := hstrict (tailBits x)
    have hb := hbound (tailBits x)
    cases hx : x 0
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      change ((0 < c + ∑ h, (phi h).eval (tailBits x) ↔
          f (tailBits x) = true) ∧
        c + ∑ h, (phi h).eval (tailBits x) ≠ 0)
      exact hs
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      have hneg : c - M + ∑ h, (phi h).eval (tailBits x) < 0 := by
        linarith [lt_of_abs_lt hb]
      constructor <;> linarith
  · apply computableWithHeadsN_tailAtoms_add_raw phi c M
    intro x
    have hs := hstrict (tailBits x)
    have hb := hbound (tailBits x)
    cases hx : x 0
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      change ((0 < c + ∑ h, (phi h).eval (tailBits x) ↔
          f (tailBits x) = true) ∧
        c + ∑ h, (phi h).eval (tailBits x) ≠ 0)
      exact hs
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      have hpos : 0 < c + M + ∑ h, (phi h).eval (tailBits x) := by
        linarith [neg_lt_of_abs_lt hb]
      exact ⟨hpos, ne_of_gt hpos⟩
  · apply computableWithHeadsN_tailAtoms_add_raw phi (c - M) M
    intro x
    have hs := hstrict (tailBits x)
    have hb := hbound (tailBits x)
    cases hx : x 0
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      have hneg : c - M + ∑ h, (phi h).eval (tailBits x) < 0 := by
        linarith [lt_of_abs_lt hb]
      exact ⟨hneg.le, ne_of_lt hneg⟩
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      change ((0 < c + ∑ h, (phi h).eval (tailBits x) ↔
          f (tailBits x) = true) ∧
        c + ∑ h, (phi h).eval (tailBits x) ≠ 0)
      exact hs
  · apply computableWithHeadsN_tailAtoms_add_raw phi (c + M) (-M)
    intro x
    have hs := hstrict (tailBits x)
    have hb := hbound (tailBits x)
    cases hx : x 0
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      have hpos : 0 < c + M + ∑ h, (phi h).eval (tailBits x) := by
        linarith [neg_lt_of_abs_lt hb]
      exact ⟨hpos, ne_of_gt hpos⟩
    · simp [oneSliceFeature, hx, boolToReal] at ⊢
      change ((0 < c + ∑ h, (phi h).eval (tailBits x) ↔
          f (tailBits x) = true) ∧
        c + ∑ h, (phi h).eval (tailBits x) ≠ 0)
      exact hs

/-- Head-complexity form of the one-active-slice construction. -/
theorem HStar_oneSliceFeature_le_succ
    (f : (Fin m → Bool) → Bool) (active constant : Bool) :
    HStar (m + 1) (oneSliceFeature active constant f) ≤ HStar m f + 1 :=
  HStar_le_of_computableWithHeadsN
    (oneSliceFeature_computable_succ f (HStar_computable f) active constant)

/-- XOR and XNOR as explicit binary gates. -/
def xorGate : Bool → Bool → Bool := xor

def xnorGate : Bool → Bool → Bool := fun z u ↦ !(xor z u)

/-- Canonical-slice form of the non-XOR recursion. -/
private theorem HStar_gateOfSliceKinds_le_succ
    (T : (Fin m → Bool) → Bool) (k₀ k₁ : UnarySliceKind)
    (hxor : ¬ (k₀ = .id ∧ k₁ = .neg))
    (hxnor : ¬ (k₀ = .neg ∧ k₁ = .id)) :
    HStar (m + 1) (freshBitGate (gateOfSliceKinds k₀ k₁) T) ≤
      HStar m T + 1 := by
  cases k₀ with
  | const c₀ =>
      cases k₁ with
      | const c₁ =>
          cases c₀ <;> cases c₁
          · rw [show freshBitGate
                (gateOfSliceKinds (.const false) (.const false)) T =
                (fun _ : Fin (m + 1) → Bool ↦ false) by
              funext x
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval]]
            rw [HStar_constantFn]
            omega
          · rw [show freshBitGate
                (gateOfSliceKinds (.const false) (.const true)) T =
                (fun x : Fin (m + 1) → Bool ↦ x 0) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            rw [HStar_freshRawBit]
            omega
          · rw [show freshBitGate
                (gateOfSliceKinds (.const true) (.const false)) T =
                (fun x : Fin (m + 1) → Bool ↦ !(x 0)) by
              funext x
              cases hx : x 0 <;>
                simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
            rw [HStar_freshRawBitComplement]
            omega
          · rw [show freshBitGate
                (gateOfSliceKinds (.const true) (.const true)) T =
                (fun _ : Fin (m + 1) → Bool ↦ true) by
              funext x
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval]]
            rw [HStar_constantFn]
            omega
      | id =>
          rw [show freshBitGate (gateOfSliceKinds (.const c₀) .id) T =
              oneSliceFeature true c₀ T by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, hx]]
          exact HStar_oneSliceFeature_le_succ T true c₀
      | neg =>
          rw [show freshBitGate (gateOfSliceKinds (.const c₀) .neg) T =
              oneSliceFeature true c₀ (complementFn T) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, complementFn, hx]]
          calc
            HStar (m + 1) (oneSliceFeature true c₀ (complementFn T)) ≤
                HStar m (complementFn T) + 1 :=
              HStar_oneSliceFeature_le_succ (complementFn T) true c₀
            _ = HStar m T + 1 := by
              have hcomp : HStar m (complementFn T) = HStar m T := by
                change HStar m (fun x ↦ !(T x)) = HStar m T
                exact HStar_complement T
              rw [hcomp]
  | id =>
      cases k₁ with
      | const c₁ =>
          rw [show freshBitGate (gateOfSliceKinds .id (.const c₁)) T =
              oneSliceFeature false c₁ T by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, hx]]
          exact HStar_oneSliceFeature_le_succ T false c₁
      | id =>
          rw [show freshBitGate (gateOfSliceKinds .id .id) T =
              (fun x : Fin (m + 1) → Bool ↦ T (tailBits x)) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval, hx]]
          have hlift := (HStar_computable T).liftDummyAlong (Fin.succEmb m)
          have hpull : (fun x : Fin (m + 1) → Bool ↦
              T (pullBitsAlong (Fin.succEmb m) x)) =
              (fun x ↦ T (tailBits x)) := by
            funext x
            apply congrArg T
            funext i
            rfl
          rw [hpull] at hlift
          have hle : HStar (m + 1) (fun x ↦ T (tailBits x)) ≤ HStar m T := by
            apply HStar_le_of_computableWithHeadsN
            exact hlift
          exact hle.trans (Nat.le_add_right _ 1)
      | neg =>
          exact (hxor ⟨rfl, rfl⟩).elim
  | neg =>
      cases k₁ with
      | const c₁ =>
          rw [show freshBitGate (gateOfSliceKinds .neg (.const c₁)) T =
              oneSliceFeature false c₁ (complementFn T) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                oneSliceFeature, complementFn, hx]]
          calc
            HStar (m + 1) (oneSliceFeature false c₁ (complementFn T)) ≤
                HStar m (complementFn T) + 1 :=
              HStar_oneSliceFeature_le_succ (complementFn T) false c₁
            _ = HStar m T + 1 := by
              have hcomp : HStar m (complementFn T) = HStar m T := by
                change HStar m (fun x ↦ !(T x)) = HStar m T
                exact HStar_complement T
              rw [hcomp]
      | id =>
          exact (hxnor ⟨rfl, rfl⟩).elim
      | neg =>
          rw [show freshBitGate (gateOfSliceKinds .neg .neg) T =
              (fun x : Fin (m + 1) → Bool ↦ complementFn T (tailBits x)) by
            funext x
            cases hx : x 0 <;>
              simp [freshBitGate, gateOfSliceKinds, UnarySliceKind.eval,
                complementFn, hx]]
          have hlift :=
            (HStar_computable (complementFn T)).liftDummyAlong (Fin.succEmb m)
          have hpull : (fun x : Fin (m + 1) → Bool ↦
              complementFn T (pullBitsAlong (Fin.succEmb m) x)) =
              (fun x ↦ complementFn T (tailBits x)) := by
            funext x
            apply congrArg (complementFn T)
            funext i
            rfl
          rw [hpull] at hlift
          have hle : HStar (m + 1)
              (fun x ↦ complementFn T (tailBits x)) ≤
              HStar m (complementFn T) := by
            apply HStar_le_of_computableWithHeadsN
            exact hlift
          have hcomp : HStar m (complementFn T) = HStar m T := by
            change HStar m (fun x ↦ !(T x)) = HStar m T
            exact HStar_complement T
          calc
            HStar (m + 1) (fun x ↦ complementFn T (tailBits x)) ≤
                HStar m (complementFn T) := hle
            _ = HStar m T := hcomp
            _ ≤ HStar m T + 1 := Nat.le_add_right _ 1

/-- **One-bit non-XOR recursion.** Every binary gate other than XOR and XNOR
adds at most one head when one input is a fresh raw bit. -/
theorem HStar_freshBitGate_le_succ_of_ne_xor_xnor
    (T : (Fin m → Bool) → Bool) (G : Bool → Bool → Bool)
    (hxor : G ≠ xorGate) (hxnor : G ≠ xnorGate) :
    HStar (m + 1) (freshBitGate G T) ≤ HStar m T + 1 := by
  let k₀ := UnarySliceKind.classify (G false)
  let k₁ := UnarySliceKind.classify (G true)
  have hG : G = gateOfSliceKinds k₀ k₁ := by
    funext z u
    cases z
    · simpa [gateOfSliceKinds, k₀] using
        (UnarySliceKind.eval_classify (G false) u).symm
    · simpa [gateOfSliceKinds, k₁] using
        (UnarySliceKind.eval_classify (G true) u).symm
  have hkxor : ¬ (k₀ = .id ∧ k₁ = .neg) := by
    rintro ⟨hk₀, hk₁⟩
    apply hxor
    rw [hG, hk₀, hk₁]
    funext z u
    cases z <;> cases u <;> rfl
  have hkxnor : ¬ (k₀ = .neg ∧ k₁ = .id) := by
    rintro ⟨hk₀, hk₁⟩
    apply hxnor
    rw [hG, hk₀, hk₁]
    funext z u
    cases z <;> cases u <;> rfl
  rw [hG]
  exact HStar_gateOfSliceKinds_le_succ T k₀ k₁ hkxor hkxnor

end HeadComplexity
