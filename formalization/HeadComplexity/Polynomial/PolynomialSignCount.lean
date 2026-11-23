import HeadComplexity.Polynomial.SignRegionMinima
import HeadComplexity.Polynomial.SignedSubsetCount

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Counting strict polynomial sign realizations

Each sign region supplies a strict minimum of a common quadratic objective.
Generic margins bound the number of active constraints. For a fixed signed
active set, the constrained-minimum bound controls the fiber cardinality.
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial Set Filter Metric
open scoped Topology

private noncomputable def signAt {J : Type*} {n : ℕ} (c : SignedSubset J n) (j : J) : Bool :=
  by
    classical
    exact if hj : j ∈ c.1.val then c.2 ⟨j, hj⟩ else false

/-- A finite family of distinct strict sign realizations is bounded by the
number of signed active sets times the constrained-minimum bound. -/
theorem strict_sign_realizations_card_le {J T : Type*} [Fintype J] [Fintype T]
    {n d : ℕ} (hd : 0 < d) (p : J → MvPolynomial (Fin n) ℝ)
    (hp : ∀ j, (p j).totalDegree ≤ d)
    (σ : T → J → Bool) (hσ : Function.Injective σ) (θ : T → Fin n → ℝ)
    (hθ : ∀ t j, 0 < eval (θ t) (signedPolynomial (σ t j) (p j))) :
    Fintype.card T ≤ (2 * d) ^ n * Fintype.card (SignedSubset J n) := by
  classical
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
  let A (t : T) := activeConstraints p ε (σ t) (x t)
  have hA (t : T) : (A t).card ≤ n :=
    activeConstraints_card_le F p P ε hεind (σ t) (x t) (hPeval (x t))
  let code (t : T) : SignedSubset J n := ⟨⟨A t, hA t⟩, fun j ↦ σ t j⟩
  have hfiber (c : SignedSubset J n) : Fintype.card {t : T // code t = c} ≤ (2 * d) ^ n := by
    let B := {t : T // code t = c}
    let R (j : c.1.val) := signedPolynomial (c.2 j) (p j) - C (ε j)
    have hact (t : B) : A t = c.1.val := congrArg (fun s : SignedSubset J n ↦ s.1.val) t.2
    have hsign (t : B) (j : c.1.val) : σ t j = c.2 j := by
      have hj : (j : J) ∈ A t := (hact t).symm ▸ j.2
      have he := congrArg (fun s : SignedSubset J n ↦ signAt s j) t.2
      simpa [signAt, code, hj, j.2] using he
    have hRdeg (j : c.1.val) : (R j).totalDegree ≤ d := by
      apply (totalDegree_sub _ _).trans
      apply max_le _ (by simp)
      cases hb : c.2 j <;> simpa [signedPolynomial, hb] using hp j
    have hz (t : B) (j : c.1.val) : eval (x t) (R j) = 0 := by
      have hj : (j : J) ∈ A t := (hact t).symm ▸ j.2
      have he := (mem_activeConstraints p ε (σ t) (x t) j).mp hj
      simp [R, ← hsign t j, he]
    have hlocal (t : B) : ∀ᶠ y in 𝓝 (x t),
        (∀ j : c.1.val, eval y (R j) = 0) → y ≠ x t → eval (x t) q < eval y q := by
      filter_upwards [strict_localMin_active p ε (σ t) q (x t) (hxregion t) (hxmin t)]
        with y hy hzero hne
      apply hy (fun j ↦ ?_) hne
      have hj : (j : J) ∈ c.1.val := hact t ▸ j.2
      have he := hsign t ⟨j, hj⟩
      simpa only [R, he] using hzero ⟨j, hj⟩
    exact constrained_minima_card_le hd R hRdeg q (hq.trans (by omega))
      (fun t : B ↦ x t) (hxinj.comp Subtype.val_injective) hz hlocal
  have hcount := Finset.card_le_mul_card_image_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := code)
    (fun _ _ ↦ Finset.mem_univ _) ((2 * d) ^ n)
    (fun c _ ↦ by simpa [Fintype.card_subtype] using hfiber c)
  simpa using hcount

/-- The strict Warren estimate for any finite family of distinct realized
sign vectors, with arbitrary finite index and variable types. -/
theorem strict_sign_realizations_bound {J K T : Type*}
    [Fintype J] [Fintype K] [Fintype T] {d : ℕ}
    (hd : 0 < d) (hK : 0 < Fintype.card K) (hKJ : Fintype.card K ≤ Fintype.card J)
    (p : J → MvPolynomial K ℝ) (hp : ∀ j, (p j).totalDegree ≤ d)
    (σ : T → J → Bool) (hσ : Function.Injective σ) (θ : T → K → ℝ)
    (hθ : ∀ t j, 0 < eval (θ t) (signedPolynomial (σ t j) (p j))) :
    (Fintype.card T : ℝ) ≤
      (4 * Real.exp 1 * d * Fintype.card J / Fintype.card K) ^ Fintype.card K := by
  classical
  let e := Fintype.equivFin K
  let P (j : J) := rename e (p j)
  let X (t : T) := θ t ∘ e.symm
  have hP (j : J) : (P j).totalDegree ≤ d := (totalDegree_rename_le e (p j)).trans (hp j)
  have hX (t : T) (j : J) : 0 < eval (X t) (signedPolynomial (σ t j) (P j)) := by
    have hh := hθ t j
    cases hb : σ t j <;>
      simpa [signedPolynomial, hb, P, X, eval_rename, Function.comp_def] using hh
  have hnat := strict_sign_realizations_card_le hd P hP σ hσ X hX
  have hreal : (Fintype.card T : ℝ) ≤
      (2 * d : ℝ) ^ Fintype.card K * Fintype.card (SignedSubset J (Fintype.card K)) := by
    exact_mod_cast hnat
  calc
    _ ≤ (2 * d : ℝ) ^ Fintype.card K *
        (2 * Real.exp 1 * Fintype.card J / Fintype.card K) ^ Fintype.card K :=
      hreal.trans (mul_le_mul_of_nonneg_left (signedSubset_card_bound J hK hKJ) (by positivity))
    _ = _ := by rw [← mul_pow]; congr 1; ring

end HeadComplexity.PolynomialRootCount
