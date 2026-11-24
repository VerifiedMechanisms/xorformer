import HeadComplexity.Atoms.RoPE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.header false

/-!
# Literal pure rotary attention and its scalar extraction

The token embedding is shared by all heads, there are no positional embeddings,
the query token is fixed, and the query attends to itself. Only queries and keys
are position transformed. Values are unrotated and depend only on the token.

`PureRotaryFamily` takes the position transforms as a parameter. Consequently
its extraction theorem applies in particular to every block-rotation frequency
schedule, with no rank, interpolation, or nondegeneracy assumption. No existing
vanilla definition is changed.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

/-- One common position-transform schedule, used by every head. -/
abbrev RotarySchedule (n d : ℕ) := SeqPos n → Vec d →ₗ[ℝ] Vec d

/-- Shared-embedding pure rotary attention. The same linear value map can absorb
an output projection; values themselves have no positional dependence. -/
structure PureRotaryFamily (n d H : ℕ) where
  tokenEmbed : Fin 3 → Vec d
  WQ : Fin H → Vec d →ₗ[ℝ] Vec d
  WK : Fin H → Vec d →ₗ[ℝ] Vec d
  WV : Fin H → Vec d →ₗ[ℝ] Vec d

namespace PureRotaryFamily

variable {n d H : ℕ}

/-- The logit of token `t` at position `p`, against the fixed query token. -/
noncomputable def logit (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (h : Fin H) (p : SeqPos n) (t : Fin 3) : ℝ :=
  ⟪R p (M.WK h (M.tokenEmbed t)), R none (M.WQ h (M.tokenEmbed 2))⟫_ℝ

noncomputable def sigma (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (h : Fin H) (x : Fin n → Bool) (p : SeqPos n) : ℝ :=
  Real.exp (M.logit R h p (Head.seqTok x p))

noncomputable def value (M : PureRotaryFamily n d H) (h : Fin H)
    (x : Fin n → Bool) (p : SeqPos n) : Vec d :=
  M.WV h (M.tokenEmbed (Head.seqTok x p))

noncomputable def denominator (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (h : Fin H) (x : Fin n → Bool) : ℝ :=
  ∑ p, M.sigma R h x p

noncomputable def numerator (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (h : Fin H) (x : Fin n → Bool) : Vec d :=
  ∑ p, M.sigma R h x p • M.value h x p

noncomputable def headUpdate (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (h : Fin H) (x : Fin n → Bool) : Vec d :=
  (M.denominator R h x)⁻¹ • M.numerator R h x

noncomputable def attnUpdate (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (x : Fin n → Bool) : Vec d :=
  ∑ h, M.headUpdate R h x

noncomputable def residual (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (x : Fin n → Bool) : Vec d :=
  M.tokenEmbed 2 + M.attnUpdate R x

/-- Exact scalar extraction needs no property of the positional transforms. -/
noncomputable def toAtom (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (w : Vec d) (h : Fin H) : PureRoPEAtom n where
  a i := Real.exp (M.logit R h (some i) 0)
  b i := Real.exp (M.logit R h (some i) 1)
  γ := Real.exp (M.logit R h none 2)
  η := Real.exp (M.logit R h none 2) * ⟪w, M.WV h (M.tokenEmbed 2)⟫_ℝ
  v₀ := ⟪w, M.WV h (M.tokenEmbed 0)⟫_ℝ
  v₁ := ⟪w, M.WV h (M.tokenEmbed 1)⟫_ℝ
  ha _ := Real.exp_pos _
  hb _ := Real.exp_pos _
  hγ := Real.exp_pos _

theorem denominator_eq (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (w : Vec d) (h : Fin H) (x : Fin n → Bool) :
    M.denominator R h x =
      (M.toAtom R w h).γ + ∑ i, if x i then (M.toAtom R w h).b i
        else (M.toAtom R w h).a i := by
  rw [denominator, Fintype.sum_option]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [sigma, Head.seqTok, hx, toAtom]

theorem numerator_readout (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (w : Vec d) (h : Fin H) (x : Fin n → Bool) :
    ⟪w, M.numerator R h x⟫_ℝ =
      (M.toAtom R w h).η + ∑ i, if x i then (M.toAtom R w h).b i *
        (M.toAtom R w h).v₁ else (M.toAtom R w h).a i * (M.toAtom R w h).v₀ := by
  rw [numerator, inner_sum, Fintype.sum_option]
  simp_rw [inner_smul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [sigma, value, Head.seqTok, hx, toAtom]

/-- The exact real score of each literal head equals a pure scalar atom. -/
theorem head_readout_eq_atom (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (w : Vec d) (h : Fin H) (x : Fin n → Bool) :
    ⟪w, M.headUpdate R h x⟫_ℝ = (M.toAtom R w h).eval x := by
  rw [headUpdate, inner_smul_right, numerator_readout, denominator_eq M R w]
  rw [PureRoPEAtom.eval, div_eq_inv_mul]

/-- Exact score extraction, including the fixed residual and threshold. -/
theorem residual_score_eq (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (w : Vec d) (τ : ℝ) (x : Fin n → Bool) :
    ⟪w, M.residual R x⟫_ℝ - τ =
      (⟪w, M.tokenEmbed 2⟫_ℝ - τ) + ∑ h, (M.toAtom R w h).eval x := by
  rw [residual, inner_add_right, attnUpdate, inner_sum]
  simp_rw [head_readout_eq_atom]
  ring

/-- The strict positive-score threshold convention is preserved exactly. -/
theorem pureRoPEComputable_of_computesPred
    (M : PureRotaryFamily n d H) (R : RotarySchedule n d)
    (f : (Fin n → Bool) → Bool) (hf : computesPred f (M.residual R)) :
    pureRoPEComputable n H f := by
  obtain ⟨w, τ, hf⟩ := hf
  refine ⟨M.toAtom R w, ⟪w, M.tokenEmbed 2⟫_ℝ - τ, ?_⟩
  intro x
  rw [← M.residual_score_eq R w τ x, sub_pos]
  exact hf x

end PureRotaryFamily

/-- Counterclockwise planar rotations, one block for each frequency. Coordinates
are ordered by `finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)`. -/
noncomputable def blockRotation {m : ℕ} (ω : Fin m → ℝ) (t : ℝ) :
    Vec (m * 2) →ₗ[ℝ] Vec (m * 2) where
  toFun v := WithLp.toLp 2 (fun j =>
    let r := j.divNat
    let u := v (finProdFinEquiv (r, (0 : Fin 2)))
    let z := v (finProdFinEquiv (r, (1 : Fin 2)))
    if j.modNat = 0 then Real.cos (t * ω r) * u - Real.sin (t * ω r) * z
    else Real.sin (t * ω r) * u + Real.cos (t * ω r) * z)
  map_add' u v := by
    ext j
    simp only [PiLp.add_apply]
    split <;> ring
  map_smul' c v := by
    ext j
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

/-- Inputs occupy positions `1,...,n`; the fixed query occupies `n+1`. -/
def rotaryPosition {n : ℕ} : SeqPos n → ℝ
  | some i => (i.val : ℝ) + 1
  | none => (n : ℝ) + 1

/-- The literal shared rotary schedule with the given frequencies. -/
noncomputable def frequencySchedule {n m : ℕ} (ω : Fin m → ℝ) :
    RotarySchedule n (m * 2) :=
  fun p => blockRotation ω (rotaryPosition p)

/-- The standard base-10,000 schedule at rotary dimension `2m`. -/
noncomputable def standardRotaryFrequency (m : ℕ) (r : Fin m) : ℝ :=
  (10000 : ℝ) ^ (-(r.val : ℝ) / (m : ℝ))

/-- Literal pure rotary computability at one fixed width and schedule. -/
def pureRotaryComputableAt {n d : ℕ} (H : ℕ) (R : RotarySchedule n d)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ M : PureRotaryFamily n d H, computesPred f (M.residual R)

/-- Freely chosen frequencies are still shared across all heads. -/
def freePureRotaryComputable (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m) (ω : Fin m → ℝ),
    pureRotaryComputableAt H (frequencySchedule ω) f

/-- Fixed standard frequencies, with unrestricted finite even width. -/
def standardPureRotaryComputable (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m),
    pureRotaryComputableAt H (frequencySchedule (standardRotaryFrequency m)) f

/-- Every standard-frequency architecture is a free-frequency architecture. -/
theorem freePureRotaryComputable_of_standard {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : standardPureRotaryComputable n H f) : freePureRotaryComputable n H f := by
  obtain ⟨m, hm, hf⟩ := hf
  exact ⟨m, hm, standardRotaryFrequency m, hf⟩

/-- Architectural necessity is unconditional and covers any rotary frequencies. -/
theorem pureRoPEComputable_of_pureRotaryComputableAt {n d H : ℕ}
    {R : RotarySchedule n d} {f : (Fin n → Bool) → Bool}
    (hf : pureRotaryComputableAt H R f) : pureRoPEComputable n H f := by
  obtain ⟨M, hM⟩ := hf
  exact M.pureRoPEComputable_of_computesPred R f hM

theorem pureRoPEComputable_of_freePureRotaryComputable {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : freePureRotaryComputable n H f) :
    pureRoPEComputable n H f := by
  obtain ⟨m, hm, ω, hf⟩ := hf
  exact pureRoPEComputable_of_pureRotaryComputableAt hf

theorem pureRoPEComputable_of_standardPureRotaryComputable {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : standardPureRotaryComputable n H f) :
    pureRoPEComputable n H f :=
  pureRoPEComputable_of_freePureRotaryComputable
    (freePureRotaryComputable_of_standard hf)

end HeadComplexity
