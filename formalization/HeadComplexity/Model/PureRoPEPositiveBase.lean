import HeadComplexity.Model.RectangularPureRoPE

/-!
# Pure rotary interpolation for every fixed geometric base above one

This is a separate parameterized frequency convention. The original base-10000
standard schedule and all original vanilla definitions remain unchanged.
The same common finite width works for every positive head count and both
boundary cases: zero input length and zero heads.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

/-- A fixed geometric base, with the usual zero-based frequency index. -/
noncomputable def geometricRotaryFrequency (B : ℝ) (m : ℕ) (r : Fin m) : ℝ :=
  B ^ (-(r.val : ℝ) / (m : ℝ))

@[simp] theorem geometricRotaryFrequency_standard (m : ℕ) :
    geometricRotaryFrequency 10000 m = standardRotaryFrequency m := rfl

theorem geometricRotaryFrequency_pos {B : ℝ} (hB : 0 < B) (m : ℕ) (r : Fin m) :
    0 < geometricRotaryFrequency B m r := Real.rpow_pos_of_pos hB _

theorem geometricRotaryFrequency_le_one {B : ℝ} (hB : 1 ≤ B) (m : ℕ) (r : Fin m) :
    geometricRotaryFrequency B m r ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos hB
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem geometricRotaryFrequency_injective {B : ℝ} (hB : 1 < B)
    {m : ℕ} (hm : 0 < m) : Function.Injective (geometricRotaryFrequency B m) := by
  intro r s hrs
  have he := (Real.rpow_right_inj (by linarith : 0 < B) (ne_of_gt hB)).mp hrs
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have ht := congrArg (fun t : ℝ ↦ t * (m : ℝ)) he
  simp only [div_mul_cancel₀ _ hm0, neg_inj] at ht
  apply Fin.ext
  exact_mod_cast ht

theorem geometricRotaryFrequency_exp_injective {B : ℝ} (hB : 1 < B)
    {m : ℕ} (hm : 0 < m) :
    Function.Injective
      (fun r ↦ Complex.exp ((geometricRotaryFrequency B m r : ℂ) * Complex.I)) := by
  intro r s hrs
  have hr0 := geometricRotaryFrequency_pos (by linarith : 0 < B) m r
  have hs0 := geometricRotaryFrequency_pos (by linarith : 0 < B) m s
  have hr1 := geometricRotaryFrequency_le_one hB.le m r
  have hs1 := geometricRotaryFrequency_le_one hB.le m s
  have hπ := Real.two_le_pi
  have he : (geometricRotaryFrequency B m r : ℂ) * Complex.I =
      (geometricRotaryFrequency B m s : ℂ) * Complex.I :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith) hrs
  apply geometricRotaryFrequency_injective hB hm
  simpa using congrArg Complex.im he

/-- The width is independent of the chosen base and of the head count. -/
theorem geometricRotarySchedule_interpolates {B : ℝ} (hB : 1 < B) (n : ℕ) :
    RotaryInterpolates
      (frequencySchedule (n := n) (geometricRotaryFrequency B (n + 2))) := by
  apply frequencySchedule_interpolates_of_injective
  · omega
  · exact geometricRotaryFrequency_exp_injective hB (by omega)

/-- Exact affine scores are realized at one common width, also for n=0 and H=0. -/
theorem exists_geometricPureRotaryFamily_score {B : ℝ} (hB : 1 < B) {n H : ℕ}
    (p : Fin H → PureRoPEAtom n) (c : ℝ) :
    ∃ (M : PureRotaryFamily n ((n + 2) * 2) H)
      (w : Vec ((n + 2) * 2)) (τ : ℝ),
      ∀ x, ⟪w, M.residual (frequencySchedule (geometricRotaryFrequency B (n + 2))) x⟫_ℝ
        - τ = c + ∑ h, (p h).eval x :=
  exists_pureRotaryFamily_score_of_interpolates _ (by omega)
    (geometricRotarySchedule_interpolates hB n) p c

/-- The literal rectangular model with one prescribed geometric base. -/
def rectangularGeometricPureRotaryComputable (B : ℝ) (n H : ℕ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (dm : ℕ) (_ : 0 < dm) (m : ℕ) (_ : 0 < m)
    (M : RectangularPureRotaryFamily n dm (m * 2) H),
    computesPred f (M.residual (frequencySchedule (geometricRotaryFrequency B m)))

@[simp] theorem rectangularGeometricPureRotaryComputable_standard (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    rectangularGeometricPureRotaryComputable 10000 n H f ↔
      rectangularStandardPureRotaryComputable n H f := Iff.rfl

/-- Every base above one gives exactly the pure scalar class at every budget. -/
theorem rectangularGeometricPureRotaryComputable_iff_scalar {B : ℝ} (hB : 1 < B)
    (n H : ℕ) (f : (Fin n → Bool) → Bool) :
    rectangularGeometricPureRotaryComputable B n H f ↔ pureRoPEComputable n H f := by
  constructor
  · rintro ⟨dm, hdm, m, hm, M, hf⟩
    exact M.pureRoPEComputable_of_computesPred _ f hf
  · rintro ⟨p, c, hp⟩
    obtain ⟨M, w, τ, hM⟩ := exists_geometricPureRotaryFamily_score hB p c
    refine ⟨(n + 2) * 2, by omega, n + 2, by omega,
      RectangularPureRotaryFamily.ofSquare M, w, τ, fun x ↦ ?_⟩
    rw [RectangularPureRotaryFamily.ofSquare_residual]
    change τ < ⟪w, M.residual _ x⟫_ℝ ↔ _
    rw [← sub_pos, hM]
    exact hp x

theorem rectangularGeometricPureRotaryComputable_iff_standard {B : ℝ} (hB : 1 < B)
    (n H : ℕ) (f : (Fin n → Bool) → Bool) :
    rectangularGeometricPureRotaryComputable B n H f ↔
      rectangularStandardPureRotaryComputable n H f :=
  (rectangularGeometricPureRotaryComputable_iff_scalar hB n H f).trans
    (rectangularStandardPureRotaryComputable_iff_scalar n H f).symm

end HeadComplexity
