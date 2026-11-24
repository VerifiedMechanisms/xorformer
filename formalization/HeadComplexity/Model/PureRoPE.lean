import HeadComplexity.Model.RotaryBlocks
import HeadComplexity.Model.SkipConnection
import HeadComplexity.Atoms.RoPE
import HeadComplexity.Analysis.RoPEFrequencies

set_option linter.style.header false

/-! # Literal standard-frequency pure rotary attention

Query and key vectors are rotated. Values depend only on the token, and each
head has its own output projection back into the shared residual space.
There are no additive positional embeddings.
-/

namespace HeadComplexity
noncomputable section
open scoped BigOperators InnerProductSpace

namespace PureRoPERotation

/-- Standard RoPE rotation at a real sequence position. -/
def rotate (m : ℕ) (position : ℝ) : Vec (m * 2) →ₗ[ℝ] Vec (m * 2) :=
  blockRotate (fun r ↦ position * RoPEFrequencies.frequency m r)

@[simp] theorem rotate_apply_zero {m : ℕ} (p : ℝ) (v : Vec (m * 2)) (r : Fin m) :
    rotate m p v (coord r 0) =
      Real.cos (p * RoPEFrequencies.frequency m r) * v (coord r 0) -
      Real.sin (p * RoPEFrequencies.frequency m r) * v (coord r 1) :=
  blockRotate_apply_zero _ _ _

@[simp] theorem rotate_apply_one {m : ℕ} (p : ℝ) (v : Vec (m * 2)) (r : Fin m) :
    rotate m p v (coord r 1) =
      Real.sin (p * RoPEFrequencies.frequency m r) * v (coord r 0) +
      Real.cos (p * RoPEFrequencies.frequency m r) * v (coord r 1) :=
  blockRotate_apply_one _ _ _

@[simp] theorem rotate_zero {m : ℕ} (v : Vec (m * 2)) : rotate m 0 v = v := by
  simp [rotate]

theorem rotate_add {m : ℕ} (p q : ℝ) (v : Vec (m * 2)) :
    rotate m p (rotate m q v) = rotate m (p + q) v := by
  simp only [rotate, blockRotate_add, add_mul]

theorem rotate_inner {m : ℕ} (p : ℝ) (x y : Vec (m * 2)) :
    ⟪rotate m p x, rotate m p y⟫_ℝ = ⟪x,y⟫_ℝ :=
  blockRotate_inner _ _ _

theorem rotate_inner_relative {m : ℕ} (p q : ℝ) (x y : Vec (m * 2)) :
    ⟪rotate m p x, rotate m q y⟫_ℝ = ⟪rotate m (p - q) x, y⟫_ℝ := by
  simp only [rotate, blockRotate_inner_relative, sub_mul]

theorem rotate_packKey_inner {m : ℕ} (p q : ℝ) (u v : Fin m → ℝ) :
    ⟪rotate m p (packKey u v), rotate m q (canonicalQuery m)⟫_ℝ =
      ∑ r, (Real.cos ((p - q) * RoPEFrequencies.frequency m r) * u r +
        Real.sin ((p - q) * RoPEFrequencies.frequency m r) * v r) := by
  rw [rotate_inner_relative]
  exact blockRotate_packKey_inner _ _ _

theorem rotate_single_inner_query {m : ℕ} (p : ℝ) (r : Fin m) (a : ℝ) :
    ⟪rotate m p (EuclideanSpace.single (coord r 0) a),
      rotate m p (canonicalQuery m)⟫_ℝ = a := by
  rw [rotate_inner, single_inner_canonicalQuery]

end PureRoPERotation

/-- Distinct original sequence positions; the fixed query is after all bits. -/
def pureRoPEPosition {n : ℕ} : SeqPos n → ℝ
  | some i => i.val
  | none => n

/-- The literal shared-embedding pure-RoPE model, with separate residual and
head widths and explicit output maps. Head width is the even number `m * 2`. -/
structure PureRoPEFamily (n d m H : ℕ) where
  tokenEmbed : Fin 3 → Vec d
  WQ : Fin H → Vec d →ₗ[ℝ] Vec (m * 2)
  WK : Fin H → Vec d →ₗ[ℝ] Vec (m * 2)
  WV : Fin H → Vec d →ₗ[ℝ] Vec (m * 2)
  WO : Fin H → Vec (m * 2) →ₗ[ℝ] Vec d

namespace PureRoPEFamily
variable {n d m H : ℕ}

/-- Attention weight for a specified position and token. The query is fixed. -/
def weight (M : PureRoPEFamily n d m H) (h : Fin H) (p : SeqPos n) (t : Fin 3) : ℝ :=
  Real.exp ⟪PureRoPERotation.rotate m (pureRoPEPosition p) (M.WK h (M.tokenEmbed t)),
    PureRoPERotation.rotate m n (M.WQ h (M.tokenEmbed 2))⟫_ℝ

def sigma (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) (p : SeqPos n) : ℝ :=
  M.weight h p (Head.seqTok bits p)

def value (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) (p : SeqPos n) : Vec (m * 2) :=
  M.WV h (M.tokenEmbed (Head.seqTok bits p))

def numerator (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) : Vec (m * 2) := ∑ p, M.sigma h bits p • M.value h bits p

def denominator (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) : ℝ := ∑ p, M.sigma h bits p

def headUpdate (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) : Vec d :=
  M.WO h ((M.denominator h bits)⁻¹ • M.numerator h bits)

def attnUpdate (M : PureRoPEFamily n d m H) (bits : Fin n → Bool) : Vec d :=
  ∑ h, M.headUpdate h bits

def residual (M : PureRoPEFamily n d m H) (bits : Fin n → Bool) : Vec d :=
  M.tokenEmbed 2 + M.attnUpdate bits

theorem sigma_pos (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) (p : SeqPos n) : 0 < M.sigma h bits p :=
  Real.exp_pos _

theorem denominator_pos (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) : 0 < M.denominator h bits :=
  positiveNormalizer_pos _ (M.sigma_pos h bits)

theorem denominator_ne_zero (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) : M.denominator h bits ≠ 0 :=
  (M.denominator_pos h bits).ne'

/-- The numerator/normalizer definition is exactly the ordinary softmax sum,
including the output projection for this head. -/
theorem headUpdate_eq_weighted_sum (M : PureRoPEFamily n d m H) (h : Fin H)
    (bits : Fin n → Bool) :
    M.headUpdate h bits = ∑ p,
      (M.sigma h bits p / M.denominator h bits) • M.WO h (M.value h bits p) := by
  simp only [headUpdate, numerator, map_smul, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_inv_mul]

theorem computesPred_residual_iff_attnUpdate (M : PureRoPEFamily n d m H)
    (f : (Fin n → Bool) → Bool) :
    computesPred f M.residual ↔ computesPred f M.attnUpdate :=
  (computesPred_iff_of_add_const f M.attnUpdate (M.tokenEmbed 2)).symm

/-- Scalar atom of an arbitrary literal head and arbitrary linear readout. -/
def scalarAtom (M : PureRoPEFamily n d m H) (w : Vec d) (h : Fin H) : PureRoPEAtom n where
  a i := M.weight h (some i) 0
  b i := M.weight h (some i) 1
  γ := M.weight h none 2
  η := M.weight h none 2 * ⟪w, M.WO h (M.WV h (M.tokenEmbed 2))⟫_ℝ
  v₀ := ⟪w, M.WO h (M.WV h (M.tokenEmbed 0))⟫_ℝ
  v₁ := ⟪w, M.WO h (M.WV h (M.tokenEmbed 1))⟫_ℝ
  ha _ := Real.exp_pos _
  hb _ := Real.exp_pos _
  hγ := Real.exp_pos _

theorem readout_head_eq_atom (M : PureRoPEFamily n d m H) (w : Vec d)
    (h : Fin H) (bits : Fin n → Bool) :
    ⟪w, M.headUpdate h bits⟫_ℝ = (M.scalarAtom w h).eval bits := by
  simp only [headUpdate, numerator, map_smul, inner_smul_right,
    PureRoPEAtom.eval, scalarAtom, denominator,
    Fintype.sum_option, sigma, value, Head.seqTok]
  simp only [cond_eq_ite]
  simp only [map_add, map_sum, inner_add_right, inner_sum, map_smul, inner_smul_right]
  simp only [apply_ite]
  rw [div_eq_inv_mul]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> simp

theorem readout_eq_atoms (M : PureRoPEFamily n d m H) (w : Vec d)
    (bits : Fin n → Bool) :
    ⟪w, M.attnUpdate bits⟫_ℝ = ∑ h, (M.scalarAtom w h).eval bits := by
  simp only [attnUpdate, inner_sum, readout_head_eq_atom]

end PureRoPEFamily

/-- Literal standard-RoPE computability with unrestricted positive finite widths. -/
def computableWithPureRoPEHeadsN (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (d m : ℕ), 0 < d ∧ 0 < m ∧
    ∃ M : PureRoPEFamily n d m H, computesPred f M.attnUpdate

/-- Every literal pure rotary model gives exactly the stated scalar normal form. -/
theorem pureRoPEComputable_of_architecture {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : computableWithPureRoPEHeadsN n H f) : pureRoPEComputable n H f := by
  obtain ⟨d,m,_,_,M,w,τ,hclass⟩ := hf
  refine ⟨M.scalarAtom w, -τ, ?_⟩
  intro bits
  rw [← M.readout_eq_atoms w bits]
  exact (show 0 < -τ + ⟪w,M.attnUpdate bits⟫_ℝ ↔ τ < ⟪w,M.attnUpdate bits⟫_ℝ by
    constructor <;> intro h <;> linarith).trans
    (hclass bits)

end
end HeadComplexity
