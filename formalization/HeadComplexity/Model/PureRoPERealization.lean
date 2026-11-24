import HeadComplexity.Model.PureRoPE

set_option linter.style.header false

/-!
# Constructive scalar-to-rotary realization

This module isolates the precise finite interpolation requirement and proves
that it suffices for exact real-score realization with shared token embeddings.
It includes the fixed query, self attention, and residual. Interpolation is an
explicit hypothesis, not an axiom or an assertion about every frequency list.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

/-- Finite-logit interpolation at one common query vector, including the self
position. The same query and schedule can be used by every head. -/
def RotaryInterpolates {n d : ℕ} (R : RotarySchedule n d) : Prop :=
  ∃ q : Vec d, ∀ y : SeqPos n → ℝ, ∃ k : Vec d,
    ∀ p, ⟪R p k, R none q⟫_ℝ = y p

private noncomputable def basisToken {d : ℕ} (hd : 3 ≤ d) (t : Fin 3) : Vec d :=
  EuclideanSpace.single (Fin.castLE hd t) 1

private noncomputable def assignTokens {d : ℕ} (hd : 3 ≤ d) (v : Fin 3 → Vec d) :
    Vec d →ₗ[ℝ] Vec d :=
  ∑ t, (LinearMap.toSpanSingleton ℝ (Vec d) (v t)).comp
    (EuclideanSpace.projₗ (Fin.castLE hd t))

private theorem assignTokens_basisToken {d : ℕ} (hd : 3 ≤ d)
    (v : Fin 3 → Vec d) (t : Fin 3) :
    assignTokens hd v (basisToken hd t) = v t := by
  simp only [assignTokens, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, basisToken, EuclideanSpace.projₗ,
    PiLp.projₗ_apply, PiLp.single_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hbt
    have h : Fin.castLE hd b ≠ Fin.castLE hd t := by
      exact fun h => hbt (Fin.castLE_injective hd h)
    simp [h]
  · simp

/-- Any scalar pure score is exactly realized when finite logits interpolate.
The width is common to all heads and is independent of their number. -/
theorem exists_pureRotaryFamily_score_of_interpolates {n d H : ℕ}
    (R : RotarySchedule n d) (hd : 3 ≤ d) (hR : RotaryInterpolates R)
    (p : Fin H → PureRoPEAtom n) (c : ℝ) :
    ∃ (M : PureRotaryFamily n d H) (w : Vec d) (τ : ℝ),
      ∀ x, ⟪w, M.residual R x⟫_ℝ - τ = c + ∑ h, (p h).eval x := by
  classical
  obtain ⟨q, hq⟩ := hR
  let logs (h : Fin H) (t : Fin 3) : SeqPos n → ℝ := fun pos =>
    match pos with
    | none => Real.log (p h).γ
    | some i => if t = 0 then Real.log ((p h).a i) else Real.log ((p h).b i)
  choose k hk using fun h t => hq (logs h t)
  let w := basisToken hd 0
  let values (h : Fin H) : Fin 3 → ℝ := ![(p h).v₀, (p h).v₁, (p h).η / (p h).γ]
  let M : PureRotaryFamily n d H := {
    tokenEmbed := basisToken hd
    WQ _ := assignTokens hd (fun _ => q)
    WK h := assignTokens hd (k h)
    WV h := assignTokens hd (fun t => values h t • w) }
  have hlog (h : Fin H) (pos : SeqPos n) (t : Fin 3) :
      M.logit R h pos t = logs h t pos := by
    simp only [PureRotaryFamily.logit, M, assignTokens_basisToken]
    exact hk h t pos
  have hval (h : Fin H) (t : Fin 3) :
      ⟪w, M.WV h (M.tokenEmbed t)⟫_ℝ = values h t := by
    simp only [M, assignTokens_basisToken, inner_smul_right]
    simp [w, basisToken]
  have hatom (h : Fin H) (x : Fin n → Bool) :
      (M.toAtom R w h).eval x = (p h).eval x := by
    have ha (i) := Real.exp_log ((p h).ha i)
    have hb (i) := Real.exp_log ((p h).hb i)
    simp [PureRoPEAtom.eval, PureRotaryFamily.toAtom, hlog, logs, hval, values,
      Real.exp_log (p h).hγ, ha, hb, mul_div_cancel₀ _ (p h).hγ.ne']
  refine ⟨M, w, ⟪w, M.tokenEmbed 2⟫_ℝ - c, ?_⟩
  intro x
  rw [M.residual_score_eq]
  simp [hatom]

/-- Exact Boolean equivalence at any width whose schedule interpolates. -/
theorem pureRotaryComputableAt_iff_scalar_of_interpolates {n d H : ℕ}
    (R : RotarySchedule n d) (hd : 3 ≤ d) (hR : RotaryInterpolates R)
    (f : (Fin n → Bool) → Bool) :
    pureRotaryComputableAt H R f ↔ pureRoPEComputable n H f := by
  constructor
  · exact pureRoPEComputable_of_pureRotaryComputableAt
  · rintro ⟨p, c, hp⟩
    obtain ⟨M, w, τ, hM⟩ := exists_pureRotaryFamily_score_of_interpolates R hd hR p c
    refine ⟨M, w, τ, fun x => ?_⟩
    change τ < ⟪w, M.residual R x⟫_ℝ ↔ _
    rw [← sub_pos, hM]
    exact hp x

end HeadComplexity
