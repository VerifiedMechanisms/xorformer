import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Data.Finset.Powerset

set_option linter.style.header false

/-!
# Uniform approximation by one fractional atom

This module packages a compositional approximation interface. A finite sum of
uniformly one-atom-approximable score terms computes every predicate that the
original sum represents with a strict nonzero margin on the Boolean cube.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- A real-valued cube function can be approximated uniformly, to every
positive tolerance, by one fractional atom. -/
def UniformlyOneAtomApproximable (g : (Fin n → Bool) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ φ : FracAtom n, ∀ bits, |φ.eval bits - g bits| < ε

/-- A score strictly sign-represents a Boolean predicate when it has the right
positive set and never vanishes. -/
def StrictSignRepresentsScore (score : (Fin n → Bool) → ℝ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ bits, ((0 < score bits ↔ f bits = true) ∧ score bits ≠ 0)

/-- A finite sum of uniformly one-atom-approximable terms may be replaced by
one atom per term without changing a strict sign pattern. -/
theorem computableWithHeadsN_of_uniformlyOneAtomApproximable
    {H : ℕ} {f : (Fin n → Bool) → Bool}
    (g : Fin H → (Fin n → Bool) → ℝ) (hg : ∀ h, UniformlyOneAtomApproximable (g h))
    (bias : ℝ)
    (hstrict : StrictSignRepresentsScore (fun bits ↦ bias + ∑ h, g h bits) f) :
    computableWithHeadsN n H f := by
  classical
  let score : (Fin n → Bool) → ℝ := fun bits ↦ bias + ∑ h, g h bits
  obtain ⟨nearest, -, hmin⟩ :=
    (Finset.univ : Finset (Fin n → Bool)).exists_min_image
      (fun bits ↦ |score bits|) Finset.univ_nonempty
  let margin : ℝ := |score nearest|
  have hmargin : 0 < margin := abs_pos.mpr (hstrict nearest).2
  let ε : ℝ := margin / (H + 1 : ℝ)
  have hden : (0 : ℝ) < H + 1 := by positivity
  have hε : 0 < ε := div_pos hmargin hden
  choose φ hφ using fun h ↦ hg h ε hε
  apply computable_of_fracComputable
  refine ⟨φ, bias, fun bits ↦ ?_⟩
  let approx : ℝ := bias + ∑ h, (φ h).eval bits
  have hpoint_margin : margin ≤ |score bits| :=
    hmin bits (Finset.mem_univ bits)
  have hdiff : approx - score bits = ∑ h, ((φ h).eval bits - g h bits) := by
    dsimp [approx, score]
    rw [Finset.sum_sub_distrib]
    ring
  have habs_diff : |approx - score bits| ≤
      ∑ h, |(φ h).eval bits - g h bits| := by
    rw [hdiff]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum_le : (∑ h, |(φ h).eval bits - g h bits|) ≤ H * ε := by
    calc
      (∑ h, |(φ h).eval bits - g h bits|) ≤ ∑ _h : Fin H, ε :=
        Finset.sum_le_sum fun h _ ↦ (hφ h bits).le
      _ = H * ε := by simp
  have hbudget : (H : ℝ) * ε < margin := by
    have hHlt : (H : ℝ) < H + 1 := by norm_num
    have := (div_lt_one hden).mpr hHlt
    dsimp [ε]
    calc
      (H : ℝ) * (margin / (H + 1 : ℝ)) = margin * ((H : ℝ) / (H + 1 : ℝ)) := by ring
      _ < margin * 1 := mul_lt_mul_of_pos_left this hmargin
      _ = margin := mul_one margin
  have herr : |approx - score bits| < margin :=
    habs_diff.trans_lt (hsum_le.trans_lt hbudget)
  change 0 < approx ↔ f bits = true
  constructor
  · intro happ
    by_contra hftrue
    have hffalse : f bits = false := by
      cases hfb : f bits
      · rfl
      · exact (hftrue hfb).elim
    have hnpos : ¬ 0 < score bits := by
      intro hspos
      exact Bool.false_ne_true (hffalse.symm.trans ((hstrict bits).1.mp hspos))
    have hsneg : score bits < 0 := lt_of_le_of_ne (le_of_not_gt hnpos) (hstrict bits).2
    have habs_score : |score bits| = -score bits := abs_of_neg hsneg
    have hscore_le : score bits ≤ -margin := by
      have hm := hpoint_margin
      rw [habs_score] at hm
      linarith
    have hupper : approx - score bits < margin := (abs_lt.mp herr).2
    linarith
  · intro hftrue
    have hspos : 0 < score bits := (hstrict bits).1.mpr hftrue
    have habs_score : |score bits| = score bits := abs_of_pos hspos
    have hmargin_le_score : margin ≤ score bits := by rwa [← habs_score]
    have hlower : -margin < approx - score bits := (abs_lt.mp herr).1
    linarith

/-! ## Elementary bounds on cube coordinates -/

theorem boolToReal_nonneg (b : Bool) : 0 ≤ boolToReal b := by
  cases b <;> simp [boolToReal]

theorem boolToReal_le_one (b : Bool) : boolToReal b ≤ 1 := by
  cases b <;> simp [boolToReal]

private theorem sum_boolToReal_lt_succ (bits : Fin n → Bool) :
    (∑ i, boolToReal (bits i)) < (n + 1 : ℝ) := by
  have hle : (∑ i, boolToReal (bits i)) ≤ ∑ _i : Fin n, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ ↦ boolToReal_le_one (bits i)
  have hone : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  rw [hone] at hle
  exact lt_of_le_of_lt hle (by norm_num)

private theorem abs_affineValue_lt_bound (c : ℝ) (cs : Fin n → ℝ)
    (bits : Fin n → Bool) :
    |affineValue c cs bits| < 1 + |c| + ∑ i, |cs i| := by
  have hsum : |∑ i, cs i * boolToReal (bits i)| ≤ ∑ i, |cs i| := by
    calc
      |∑ i, cs i * boolToReal (bits i)| ≤
          ∑ i, |cs i * boolToReal (bits i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |cs i| := Finset.sum_le_sum fun i _ ↦ by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (by
          cases bits i <;> norm_num [boolToReal])
  calc
    |affineValue c cs bits| ≤ |c| + |∑ i, cs i * boolToReal (bits i)| := by
      unfold affineValue
      exact abs_add_le _ _
    _ ≤ |c| + ∑ i, |cs i| := add_le_add (le_refl _) hsum
    _ < 1 + |c| + ∑ i, |cs i| := by linarith

/-! ## Affine approximation -/

/-- Every affine cube function admits a uniform one-atom approximation. -/
theorem exists_fracAtom_approx_affineValue
    (c : ℝ) (cs : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : FracAtom n, ∀ bits, |φ.eval bits - affineValue c cs bits| < ε := by
  let C : ℝ := 1 + |c| + ∑ i, |cs i|
  have hC : 0 < C := by
    dsimp [C]
    have : 0 ≤ ∑ i, |cs i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    linarith [abs_nonneg c]
  let δ : ℝ := ε / (C * (n + 1 : ℝ))
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδ : 0 < δ := div_pos hε (mul_pos hC hn)
  let φ : FracAtom n := FracAtom.ofPositiveAffineRatio
    c cs 1 (fun _ ↦ δ) (by norm_num) (fun _ ↦ hδ)
  refine ⟨φ, fun bits ↦ ?_⟩
  let W : ℝ := ∑ i, boolToReal (bits i)
  let L : ℝ := affineValue c cs bits
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ ↦ boolToReal_nonneg (bits i)
  have hWlt : W < (n + 1 : ℝ) := sum_boolToReal_lt_succ bits
  have hLabs : |L| < C := abs_affineValue_lt_bound c cs bits
  have hB : affineValue 1 (fun _ : Fin n ↦ δ) bits = 1 + δ * W := by
    unfold affineValue
    dsimp [W]
    rw [Finset.mul_sum]
  have hBpos : 0 < affineValue 1 (fun _ : Fin n ↦ δ) bits :=
    affineValue_pos 1 (fun _ ↦ δ) (by norm_num) (fun _ ↦ hδ) bits
  have hnum_nonneg : 0 ≤ |L| * (δ * W) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hδ.le hW)
  have hnum_lt : |L| * (δ * W) < ε := by
    have hfirst : |L| * (δ * W) ≤ C * (δ * W) :=
      mul_le_mul_of_nonneg_right hLabs.le (mul_nonneg hδ.le hW)
    have hsecond : C * (δ * W) < C * (δ * (n + 1 : ℝ)) := by
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hWlt hδ) hC
    have heq : C * (δ * (n + 1 : ℝ)) = ε := by
      dsimp [δ]
      field_simp [hC.ne', hn.ne']
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  rw [show φ.eval bits = L / affineValue 1 (fun _ : Fin n ↦ δ) bits by
    exact FracAtom.ofPositiveAffineRatio_eval c cs 1 (fun _ ↦ δ)
      (by norm_num) (fun _ ↦ hδ) bits]
  rw [hB]
  have hden : 0 < 1 + δ * W := by positivity
  have herr : |L / (1 + δ * W) - L| = |L| * (δ * W) / (1 + δ * W) := by
    rw [show L / (1 + δ * W) - L = -(L * (δ * W) / (1 + δ * W)) by
      field_simp [hden.ne']
      ring]
    rw [abs_neg, abs_div, abs_mul, abs_of_nonneg (mul_nonneg hδ.le hW), abs_of_pos hden]
  rw [herr]
  have hden_one : 1 ≤ 1 + δ * W := by
    have : 0 ≤ δ * W := mul_nonneg hδ.le hW
    linarith
  exact (div_le_self hnum_nonneg hden_one).trans_lt hnum_lt

theorem uniformlyOneAtomApproximable_affineValue (c : ℝ) (cs : Fin n → ℝ) :
    UniformlyOneAtomApproximable (affineValue c cs) :=
  fun ε hε ↦ exists_fracAtom_approx_affineValue c cs ε hε

/-! ## Signed squarefree monomial approximation -/

/-- The squarefree monomial indexed by a coordinate set. -/
def squarefreeMonomial (S : Finset (Fin n)) (bits : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, boolToReal (bits i)

private theorem squarefreeMonomial_eq_one
    (S : Finset (Fin n)) (bits : Fin n → Bool)
    (hbits : ∀ i ∈ S, bits i = true) :
    squarefreeMonomial S bits = 1 := by
  unfold squarefreeMonomial
  exact Finset.prod_eq_one fun i hi ↦ by simp [boolToReal, hbits i hi]

private theorem squarefreeMonomial_eq_zero
    (S : Finset (Fin n)) (bits : Fin n → Bool) {i : Fin n}
    (hi : i ∈ S) (hbits : bits i = false) :
    squarefreeMonomial S bits = 0 := by
  unfold squarefreeMonomial
  apply Finset.prod_eq_zero hi
  simp [boolToReal, hbits]

/-- Every signed nonempty squarefree monomial admits a uniform one-atom
approximation. The construction uses a negative-orientation denominator which
concentrates its mass on the face where every coordinate in `S` is true. -/
theorem exists_fracAtom_approx_signedMonomial
    (S : Finset (Fin n)) (a ε : ℝ) (hε : 0 < ε) :
    ∃ φ : FracAtom n, ∀ bits,
      |φ.eval bits - a * squarefreeMonomial S bits| < ε := by
  classical
  by_cases ha : a = 0
  · subst a
    let φ : FracAtom n := FracAtom.ofPositiveAffineRatio
      0 (fun _ ↦ 0) 1 (fun _ ↦ 1) (by norm_num) (fun _ ↦ by norm_num)
    refine ⟨φ, fun bits ↦ ?_⟩
    rw [show φ.eval bits = affineValue 0 (fun _ : Fin n ↦ 0) bits /
        affineValue 1 (fun _ : Fin n ↦ 1) bits by
      exact FracAtom.ofPositiveAffineRatio_eval 0 (fun _ ↦ 0) 1 (fun _ ↦ 1)
        (by norm_num) (fun _ ↦ by norm_num) bits]
    simpa [affineValue] using hε
  · have haabs : 0 < |a| := abs_pos.mpr ha
    let R : ℝ := 1 + |a| / ε
    have hR : 0 < R := by dsimp [R]; positivity
    let C : ℝ := 1 + |a|
    have hC : 0 < C := by dsimp [C]; positivity
    let δ : ℝ := ε / (C * (n + 1 : ℝ))
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hδ : 0 < δ := div_pos hε (mul_pos hC hn)
    let w : Fin n → ℝ := fun i ↦ if i ∈ S then R else δ
    have hw : ∀ i, 0 < w i := fun i ↦ by
      dsimp [w]
      split <;> assumption
    let b₀ : ℝ := 1 + ∑ i, w i
    let b : Fin n → ℝ := fun i ↦ -w i
    have hb₀ : 0 < b₀ := by
      dsimp [b₀]
      have : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ ↦ (hw i).le
      linarith
    have hb : ∀ i, b i < 0 := fun i ↦ by dsimp [b]; exact neg_neg_of_pos (hw i)
    have hbmargin : ∑ i, -b i < b₀ := by
      dsimp [b₀, b]
      simp only [neg_neg]
      linarith
    let φ : FracAtom n := FracAtom.ofNegativeAffineRatio
      a (fun _ ↦ 0) b₀ b hb₀ hb hbmargin
    refine ⟨φ, fun bits ↦ ?_⟩
    let T : ℝ := ∑ i, w i * (1 - boolToReal (bits i))
    have hone_sub_nonneg : ∀ i, 0 ≤ 1 - boolToReal (bits i) := fun i ↦ by
      linarith [boolToReal_le_one (bits i)]
    have hT : 0 ≤ T :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i).le (hone_sub_nonneg i)
    have hden : affineValue b₀ b bits = 1 + T := by
      dsimp [b₀, b, T]
      unfold affineValue
      simp_rw [mul_sub]
      simp only [mul_one]
      rw [Finset.sum_sub_distrib]
      simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib]
      ring
    have hdenpos : 0 < 1 + T := by linarith
    rw [show φ.eval bits = affineValue a (fun _ : Fin n ↦ 0) bits /
        affineValue b₀ b bits by
      exact FracAtom.ofNegativeAffineRatio_eval a (fun _ ↦ 0) b₀ b
        hb₀ hb hbmargin bits]
    rw [show affineValue a (fun _ : Fin n ↦ 0) bits = a by simp [affineValue], hden]
    by_cases hall : ∀ i ∈ S, bits i = true
    · rw [squarefreeMonomial_eq_one S bits hall, mul_one]
      have hterm_le : ∀ i, w i * (1 - boolToReal (bits i)) ≤ δ := by
        intro i
        by_cases hi : i ∈ S
        · simp [hall i hi, boolToReal, hδ.le]
        · dsimp [w]
          rw [if_neg hi]
          have hle := boolToReal_nonneg (bits i)
          nlinarith
      have hTle : T ≤ (n : ℝ) * δ := by
        calc
          T ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ ↦ hterm_le i
          _ = (n : ℝ) * δ := by simp
      have hTlt : T < δ * (n + 1 : ℝ) := by
        have hnlt : (n : ℝ) < n + 1 := by norm_num
        calc
          T ≤ (n : ℝ) * δ := hTle
          _ < (n + 1 : ℝ) * δ := mul_lt_mul_of_pos_right hnlt hδ
          _ = δ * (n + 1 : ℝ) := by ring
      have hnum_nonneg : 0 ≤ |a| * T := mul_nonneg (abs_nonneg _) hT
      have hnum_lt : |a| * T < ε := by
        have hfirst : |a| * T ≤ C * T :=
          mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hT
        have hsecond : C * T < C * (δ * (n + 1 : ℝ)) :=
          mul_lt_mul_of_pos_left hTlt hC
        have heq : C * (δ * (n + 1 : ℝ)) = ε := by
          dsimp [δ]
          field_simp [hC.ne', hn.ne']
        exact hfirst.trans_lt (hsecond.trans_eq heq)
      have herr : |a / (1 + T) - a| = |a| * T / (1 + T) := by
        rw [show a / (1 + T) - a = -(a * T / (1 + T)) by
          field_simp [hdenpos.ne']
          ring]
        rw [abs_neg, abs_div, abs_mul, abs_of_nonneg hT, abs_of_pos hdenpos]
      rw [herr]
      exact (div_le_self hnum_nonneg (by linarith : 1 ≤ 1 + T)).trans_lt hnum_lt
    · push Not at hall
      obtain ⟨i, hi, hifalse⟩ := hall
      have hibool : bits i = false := by
        cases hbit : bits i
        · rfl
        · exact (hifalse hbit).elim
      rw [squarefreeMonomial_eq_zero S bits hi hibool, mul_zero, sub_zero,
        abs_div, abs_of_pos hdenpos]
      have hwi : w i = R := by simp [w, hi]
      have hiterm : w i * (1 - boolToReal (bits i)) = R := by
        rw [hwi, hibool]
        simp [boolToReal]
      have hTge : R ≤ T := by
        rw [← hiterm]
        exact Finset.single_le_sum
          (fun j _ ↦ mul_nonneg (hw j).le (hone_sub_nonneg j)) (Finset.mem_univ i)
      have hRden : R < 1 + T := by linarith
      have haR : |a| < ε * R := by
        dsimp [R]
        field_simp [hε.ne']
        linarith
      apply (div_lt_iff₀ hdenpos).mpr
      exact haR.trans (mul_lt_mul_of_pos_left hRden hε)

theorem uniformlyOneAtomApproximable_signedMonomial
    (S : Finset (Fin n)) (a : ℝ) :
    UniformlyOneAtomApproximable (fun bits ↦ a * squarefreeMonomial S bits) :=
  fun ε hε ↦ exists_fracAtom_approx_signedMonomial S a ε hε

end HeadComplexity
