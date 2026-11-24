import HeadComplexity.Polynomial.WeightedRootWrappers
import HeadComplexity.Polynomial.SignRegionMinima
import HeadComplexity.Polynomial.SignedSubsetCount
import HeadComplexity.Results.CountingLowerBound

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
Unconditional strict sign counting with positive integer variable weights.
The bound retains the product of the variable weights in its denominator.
-/

namespace HeadComplexity.PolynomialRootCount
open MvPolynomial Set Filter Metric
open scoped Topology BigOperators

private noncomputable def weightedSignAt {J : Type*} {n : ℕ}
    (c : SignedSubset J n) (j : J) : Bool := by
  classical
  exact if hj : j ∈ c.1.val then c.2 ⟨j, hj⟩ else false

theorem weighted_strict_sign_realizations_card_le {J T : Type*}
    [Fintype J] [Fintype T] {n D : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (hwD : ∀ i, w i ≤ D)
    (p : J → MvPolynomial (Fin n) ℝ) (hp : ∀ j, WeightedDegreeLE w (p j) D)
    (σ : T → J → Bool) (hσ : Function.Injective σ) (θ : T → Fin n → ℝ)
    (hθ : ∀ t j, 0 < eval (θ t) (signedPolynomial (σ t j) (p j))) :
    Fintype.card T ≤ (∏ i, (2 * D) / w i) * Fintype.card (SignedSubset J n) := by
  classical
  let e (i : Fin n) := (2 * D) / w i
  have he (i : Fin n) : 0 < e i := by
    exact Nat.div_pos (by have := hwD i; omega) (hw i)
  have hcut (i : Fin n) : 2 * D - w i < e i * w i := by
    have hmod := Nat.mod_lt (2 * D) (hw i)
    have hdecomp := Nat.div_add_mod (2 * D) (w i)
    have hle := hwD i
    have hcomm : w i * (2 * D / w i) = (2 * D / w i) * w i := Nat.mul_comm _ _
    dsimp [e]
    omega
  obtain ⟨F, hF, hpre⟩ := exists_countable_coefficient_field p
  let : Countable F := hF
  choose P hP using hpre
  have halg : algebraMap F ℝ = F.subtype := by ext; rfl
  have hPeval (z : Fin n → ℝ) (j : J) : eval z (p j) = aeval z (P j) := by
    rw [aeval_def, eval₂_eq_eval_map, halg]
    convert (congrArg (eval z) (hP j)).symm using 1
  obtain ⟨ε, hεind, hεpos, hθε⟩ := exists_generic_positive_margins F p σ θ hθ
  obtain ⟨q, hq, x, hxinj, hxregion, hxmin⟩ :=
    exists_strict_region_minima p ε hεpos σ hσ (fun t ↦ ⟨θ t, hθε t⟩)
  have hqweight : WeightedDegreeLE w q (2 * D) := by
    simpa [Nat.mul_comm] using weightedDegreeLE_of_totalDegree_le hq hwD
  let A (t : T) := activeConstraints p ε (σ t) (x t)
  have hA (t : T) : (A t).card ≤ n :=
    activeConstraints_card_le F p P ε hεind (σ t) (x t) (hPeval (x t))
  let code (t : T) : SignedSubset J n := ⟨⟨A t, hA t⟩, fun j ↦ σ t j⟩
  have hfiber (c : SignedSubset J n) :
      Fintype.card {t : T // code t = c} ≤ ∏ i, e i := by
    let B := {t : T // code t = c}
    let R (j : c.1.val) := signedPolynomial (c.2 j) (p j) - C (ε j)
    have hact (t : B) : A t = c.1.val := congrArg (fun s : SignedSubset J n ↦ s.1.val) t.2
    have hsign (t : B) (j : c.1.val) : σ t j = c.2 j := by
      have hj : (j : J) ∈ A t := (hact t).symm ▸ j.2
      have heq := congrArg (fun s : SignedSubset J n ↦ weightedSignAt s j) t.2
      simpa [weightedSignAt, code, hj, j.2] using heq
    have hRdeg (j : c.1.val) : WeightedDegreeLE w (R j) D := by
      apply weightedDegreeLE_sub
      · cases hb : c.2 j
        · simpa [signedPolynomial, hb] using weightedDegreeLE_neg (hp j)
        · simpa [signedPolynomial, hb] using hp j
      · exact weightedDegreeLE_mono (weightedDegreeLE_C w _) (Nat.zero_le _)
    have hz (t : B) (j : c.1.val) : eval (x t) (R j) = 0 := by
      have hj : (j : J) ∈ A t := (hact t).symm ▸ j.2
      have heq := (mem_activeConstraints p ε (σ t) (x t) j).mp hj
      simp [R, ← hsign t j, heq]
    have hlocal (t : B) : ∀ᶠ y in 𝓝 (x t),
        (∀ j : c.1.val, eval y (R j) = 0) → y ≠ x t → eval (x t) q < eval y q := by
      filter_upwards [strict_localMin_active p ε (σ t) q (x t) (hxregion t) (hxmin t)]
        with y hy hzero hne
      apply hy (fun j ↦ ?_) hne
      have hj : (j : J) ∈ c.1.val := hact t ▸ j.2
      have heq := hsign t ⟨j, hj⟩
      simpa only [R, heq] using hzero ⟨j, hj⟩
    exact weighted_constrained_minima_card_le w e hw he hcut R hRdeg q hqweight
      (fun t : B ↦ x t) (hxinj.comp Subtype.val_injective) hz hlocal
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := code)
    (fun _ _ ↦ Finset.mem_univ _) (∏ i, e i)
    (fun c _ ↦ by simpa [Fintype.card_subtype] using hfiber c)
  simpa [e] using hcount

theorem weighted_strict_sign_realizations_mul_weights_le {J T : Type*}
    [Fintype J] [Fintype T] {n D : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (hwD : ∀ i, w i ≤ D)
    (p : J → MvPolynomial (Fin n) ℝ) (hp : ∀ j, WeightedDegreeLE w (p j) D)
    (σ : T → J → Bool) (hσ : Function.Injective σ) (θ : T → Fin n → ℝ)
    (hθ : ∀ t j, 0 < eval (θ t) (signedPolynomial (σ t j) (p j))) :
    Fintype.card T * (∏ i, w i) ≤ (2 * D) ^ n * Fintype.card (SignedSubset J n) := by
  classical
  have hcount := weighted_strict_sign_realizations_card_le w hw hwD p hp σ hσ θ hθ
  have hprod : (∏ i, (2 * D) / w i) * (∏ i, w i) ≤ (2 * D) ^ n := by
    rw [← Finset.prod_mul_distrib]
    calc
      _ ≤ ∏ _i : Fin n, 2 * D :=
        Finset.prod_le_prod (fun i _ => Nat.div_mul_le_self (2 * D) (w i))
      _ = _ := by simp
  calc
    _ ≤ ((∏ i, (2 * D) / w i) * Fintype.card (SignedSubset J n)) * (∏ i, w i) :=
      Nat.mul_le_mul_right _ hcount
    _ = ((∏ i, (2 * D) / w i) * (∏ i, w i)) * Fintype.card (SignedSubset J n) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hprod

theorem weighted_strict_sign_realizations_bound {J K T : Type*}
    [Fintype J] [Fintype K] [Fintype T] {D : ℕ}
    (hK : 0 < Fintype.card K) (hKJ : Fintype.card K ≤ Fintype.card J)
    (w : K → ℕ) (hw : ∀ i, 0 < w i) (hwD : ∀ i, w i ≤ D)
    (p : J → MvPolynomial K ℝ) (hp : ∀ j, WeightedDegreeLE w (p j) D)
    (σ : T → J → Bool) (hσ : Function.Injective σ) (θ : T → K → ℝ)
    (hθ : ∀ t j, 0 < eval (θ t) (signedPolynomial (σ t j) (p j))) :
    (Fintype.card T : ℝ) ≤
      (4 * Real.exp 1 * D * Fintype.card J / Fintype.card K) ^ Fintype.card K /
        ∏ i, (w i : ℝ) := by
  classical
  let e := Fintype.equivFin K
  let W (i : Fin (Fintype.card K)) := w (e.symm i)
  let P (j : J) := rename e (p j)
  let X (t : T) := θ t ∘ e.symm
  have hW (i) : 0 < W i := hw _
  have hWD (i) : W i ≤ D := hwD _
  have hP (j : J) : WeightedDegreeLE W (P j) D := by
    exact weightedDegreeLE_rename (hp j) e (fun i => by simp [W])
  have hX (t : T) (j : J) : 0 < eval (X t) (signedPolynomial (σ t j) (P j)) := by
    have hh := hθ t j
    cases hb : σ t j <;>
      simpa [signedPolynomial, hb, P, X, eval_rename, Function.comp_def] using hh
  have hnat := weighted_strict_sign_realizations_mul_weights_le W hW hWD P hP σ hσ X hX
  have hweights : (∏ i, W i) = ∏ i, w i := Equiv.prod_comp e.symm w
  rw [hweights] at hnat
  have hreal : (Fintype.card T : ℝ) * (∏ i, (w i : ℝ)) ≤
      (2 * D : ℝ) ^ Fintype.card K * Fintype.card (SignedSubset J (Fintype.card K)) := by
    exact_mod_cast hnat
  have hbound : (Fintype.card T : ℝ) * (∏ i, (w i : ℝ)) ≤
      (4 * Real.exp 1 * D * Fintype.card J / Fintype.card K) ^ Fintype.card K := by
    calc
      _ ≤ (2 * D : ℝ) ^ Fintype.card K *
          (2 * Real.exp 1 * Fintype.card J / Fintype.card K) ^ Fintype.card K :=
        hreal.trans (mul_le_mul_of_nonneg_left (signedSubset_card_bound J hK hKJ) (by positivity))
      _ = _ := by rw [← mul_pow]; congr 1; ring
  exact (le_div_iff₀ (Finset.prod_pos fun i _ => by exact_mod_cast hw i)).mpr hbound

end HeadComplexity.PolynomialRootCount

namespace HeadComplexity
open MvPolynomial PolynomialRootCount

/-- Unconditional weighted strict Warren bound. -/
theorem weightedStrictPolynomialSignPatterns_card_le {I K : Type*}
    [Fintype I] [Fintype K] {D : ℕ}
    (hK : 0 < Fintype.card K) (hKI : Fintype.card K ≤ Fintype.card I)
    (w : K → ℕ) (hw : ∀ i, 0 < w i) (hwD : ∀ i, w i ≤ D)
    (P : I → MvPolynomial K ℝ) (hP : ∀ i, WeightedDegreeLE w (P i) D) :
    ((strictPolynomialSignPatterns P).ncard : ℝ) ≤
      (4 * Real.exp 1 * D * Fintype.card I / Fintype.card K) ^ Fintype.card K /
        ∏ i, (w i : ℝ) := by
  classical
  let T := strictPolynomialSignPatterns P
  let := Fintype.ofFinite T
  have hθ (t : T) : ∃ θ : K → ℝ, ∀ i,
      if t.val i then 0 < eval θ (P i) else eval θ (P i) < 0 := t.property
  choose θ hθ using hθ
  have hs (t : T) (i : I) : 0 < eval (θ t) (signedPolynomial (t.val i) (P i)) := by
    have h := hθ t i
    cases hb : t.val i <;> simpa [signedPolynomial, hb] using h
  have h := weighted_strict_sign_realizations_bound hK hKI w hw hwD P hP
    (fun t : T ↦ t.val) Subtype.val_injective θ hs
  simpa only [T, Set.fintypeCard_eq_ncard] using h

end HeadComplexity
