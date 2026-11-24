import HeadComplexity.Polynomial.FourHeadLocalQuadratic

set_option linter.style.header false

/-!
# The original-model bridge for the finite four-head obstruction

The local pattern and its quadratic obstruction are defined in
`FourHeadLocalQuadratic`. This module derives the necessary quadratic from all
admissible affine fractions and proves the original architectural lower bound.
-/

namespace HeadComplexity.FourHeadLocalPattern

noncomputable section

open Finset PureRoPEThreeHead FourHeadSelectorQuadratic
open scoped BigOperators

def clearedFunction (r : Fin 4 → AffineFraction 17) (c : ℝ) (x : Fin 17 → Bool) : ℝ :=
  cleared c (fun h ↦ (r h).numerator x) (fun h ↦ (r h).denominator x)

def extractedFunction (r : Fin 4 → AffineFraction 17) (c : ℝ) (x : Fin 16 → Bool) : ℝ :=
  (clearedFunction r c (join true x) - clearedFunction r c (join false x) +
    clearedFunction r c (join true (flip x)) - clearedFunction r c (join false (flip x))) / 4

theorem clearedFunction_sign (r : Fin 4 → AffineFraction 17) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin 17 → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true) (x : Fin 17 → Bool) :
    0 < clearedFunction r c x ↔ f x = true := by
  have hp (h) : 0 < (r h).denominator x := (hr h).1 x
  unfold clearedFunction
  rw [cleared_eq _ _ _ (fun h ↦ (hp h).ne')]
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2)) (hp 3))]
  exact hf x

theorem extractedFunction_positive (r : Fin 4 → AffineFraction 17) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin 17 → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true)
    (x : Fin 16 → Bool) (hx : OrbitLabel f x true) : 0 < extractedFunction r c x := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hs := clearedFunction_sign r c hr f hf
  have h1' := (hs _).mpr h1
  have h2' : clearedFunction r c (join false x) ≤ 0 := by
    have := hs (join false x); rw [h2] at this; simpa using this
  have h3' := (hs _).mpr h3
  have h4' : clearedFunction r c (join false (flip x)) ≤ 0 := by
    have := hs (join false (flip x)); rw [h4] at this; simpa using this
  unfold extractedFunction
  linarith

theorem extractedFunction_negative (r : Fin 4 → AffineFraction 17) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (f : (Fin 17 → Bool) → Bool)
    (hf : ∀ x, 0 < c + ∑ h, (r h).eval x ↔ f x = true)
    (x : Fin 16 → Bool) (hx : OrbitLabel f x false) : extractedFunction r c x < 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hs := clearedFunction_sign r c hr f hf
  have h1' : clearedFunction r c (join true x) ≤ 0 := by
    have := hs (join true x); rw [h1] at this; simpa using this
  have h2' := (hs _).mpr h2
  have h3' : clearedFunction r c (join true (flip x)) ≤ 0 := by
    have := hs (join true (flip x)); rw [h3] at this; simpa using this
  have h4' := (hs _).mpr h4
  unfold extractedFunction
  linarith

def affineCenter (c : ℝ) (v : Fin 17 → ℝ) : ℝ := c + ∑ i, v i / 2

theorem affine_split (c : ℝ) (v : Fin 17 → ℝ) (t : Bool) (x : Fin 16 → Bool) :
    c + ∑ i, v i * boolToReal (join t x i) =
      affineCenter c v + (v 16 / 2) * spin t +
        linear (fun i : Fin 16 ↦ v (i.castAdd 1) / 2) x := by
  have he (b : Bool) (a : ℝ) : a * boolToReal b = a / 2 + (a / 2) * spin b := by
    cases b <;> norm_num [boolToReal, spin]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  rw [← add_assoc]
  change affineCenter c v + (∑ i, v i / 2 * spin (join t x i)) = _
  rw [Fin.sum_univ_add (a := 16) (b := 1)]
  simp [join, linear]
  ring

def denCenter (r : Fin 4 → AffineFraction 17) (h : Fin 4) : ℝ :=
  affineCenter (r h).d (r h).C
def numCenter (r : Fin 4 → AffineFraction 17) (h : Fin 4) : ℝ :=
  affineCenter (r h).b (r h).A
def denSelector (r : Fin 4 → AffineFraction 17) (h : Fin 4) : ℝ := (r h).C 16 / 2
def numSelector (r : Fin 4 → AffineFraction 17) (h : Fin 4) : ℝ := (r h).A 16 / 2
def denVector (r : Fin 4 → AffineFraction 17) (h : Fin 4) (i : Fin 16) : ℝ :=
  (r h).C (i.castAdd 1) / 2
def numVector (r : Fin 4 → AffineFraction 17) (h : Fin 4) (i : Fin 16) : ℝ :=
  (r h).A (i.castAdd 1) / 2

theorem numerator_split (r : Fin 4 → AffineFraction 17) (h : Fin 4)
    (t : Bool) (x : Fin 16 → Bool) :
    (r h).numerator (join t x) = numCenter r h + numSelector r h * spin t +
      linear (numVector r h) x := affine_split _ _ _ _

theorem denominator_split (r : Fin 4 → AffineFraction 17) (h : Fin 4)
    (t : Bool) (x : Fin 16 → Bool) :
    (r h).denominator (join t x) = denCenter r h + denSelector r h * spin t +
      linear (denVector r h) x := affine_split _ _ _ _

theorem extractedFunction_eq (r : Fin 4 → AffineFraction 17) (c : ℝ)
    (x : Fin 16 → Bool) :
    extractedFunction r c x = extracted c (denCenter r) (denSelector r)
      (numCenter r) (numSelector r) (fun h ↦ linear (numVector r h) x)
        (fun h ↦ linear (denVector r h) x) := by
  simp only [extractedFunction, clearedFunction, numerator_split, denominator_split,
    linear_flip, spin, Bool.false_eq_true, ite_false, ite_true, mul_one, mul_neg_one,
    sub_eq_add_neg, extracted]

theorem denVector_uniform (r : Fin 4 → AffineFraction 17) (hr : ∀ h, (r h).Admissible)
    (h : Fin 4) : AffineFraction.UniformSign (denVector r h) := by
  rcases (hr h).2.1 with hp | hn | hz
  · exact Or.inl (fun i ↦ div_pos (hp _) (by norm_num))
  · exact Or.inr (Or.inl (fun i ↦ div_neg_of_neg_of_pos (hn _) (by norm_num)))
  · exact Or.inr (Or.inr (fun i ↦ by simp [denVector, hz]))

theorem exists_quadratic (r : Fin 4 → AffineFraction 17) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) :
    ∃ (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ),
      (∀ h, AffineFraction.UniformSign (B h)) ∧
      ∀ x, extractedFunction r c x = productScore q A B x := by
  refine ⟨extracted c (denCenter r) (denSelector r) (numCenter r) (numSelector r) 0 0,
    fun h i ↦ firstFactor c (denCenter r) (denSelector r) (numCenter r) (numSelector r)
      (fun k ↦ numVector r k i) (fun k ↦ denVector r k i) h,
    denVector r, denVector_uniform r hr, ?_⟩
  intro x
  rw [extractedFunction_eq, extracted_eq]
  unfold productScore
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [firstFactor_linear]

theorem orient_quadratic (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ)
    (hB : ∀ h, AffineFraction.UniformSign (B h)) :
    ∃ A' B' : Fin 4 → Fin 16 → ℝ,
      (∀ h, (∀ i, 0 < B' h i) ∨ (∀ i, B' h i = 0)) ∧
      ∀ x, productScore q A B x = productScore q A' B' x := by
  have hs (h : Fin 4) : ∃ s : ℝ, s * s = 1 ∧
      ((∀ i, 0 < s * B h i) ∨ (∀ i, s * B h i = 0)) := by
    rcases hB h with hp | hn | hz
    · exact ⟨1, by norm_num, Or.inl (by simpa using hp)⟩
    · exact ⟨-1, by norm_num, Or.inl (fun i ↦ by simpa using neg_pos.mpr (hn i))⟩
    · exact ⟨1, by norm_num, Or.inr (by simpa using hz)⟩
  choose s hs2 hsB using hs
  refine ⟨fun h i ↦ s h * A h i, fun h i ↦ s h * B h i, hsB, ?_⟩
  intro x
  unfold productScore
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [linear_smul, linear_smul]
  calc
    _ = (s h * s h) * (linear (A h) x * linear (B h) x) := by rw [hs2]; ring
    _ = _ := by ring

theorem not_computable_four (f : (Fin 17 → Bool) → Bool) (hf : LocalPattern f) :
    ¬ computableWithHeadsN 17 4 f := by
  intro hc
  obtain ⟨r, c, hr, hsign⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 4 f).mp hc
  obtain ⟨q, A, B, hB, hq⟩ := exists_quadratic r c hr
  obtain ⟨A', B', hB', horient⟩ := orient_quadratic q A B hB
  have hq' (x) : extractedFunction r c x = productScore q A' B' x :=
    (hq x).trans (horient x)
  obtain ⟨hz, hs, hcross, hpair⟩ := hf
  apply quadratic_obstruction q A' B' hB'
  · rw [← hq']
    exact extractedFunction_negative r c hr f hsign _ hz
  · intro i
    rw [← hq']
    exact extractedFunction_positive r c hr f hsign _ (hs i)
  · intro i j hij
    rw [← hq']
    exact extractedFunction_negative r c hr f hsign _ (hcross i j hij)
  · intro i j hij
    rw [← hq']
    exact extractedFunction_negative r c hr f hsign _ (hpair i j hij)

def zeroFraction (n : ℕ) : AffineFraction n where
  A _ := 0
  b := 0
  C _ := 0
  d := 1

theorem zeroFraction_admissible (n : ℕ) : (zeroFraction n).Admissible := by
  refine ⟨?_, Or.inr (Or.inr (fun _ ↦ rfl)), ?_⟩
  · intro x
    simp [zeroFraction, AffineFraction.denominator]
  · intro _
    exact Or.inr (Or.inr (fun _ ↦ rfl))

theorem affineComputable_succ {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : affineFractionComputable n H f) : affineFractionComputable n (H + 1) f := by
  obtain ⟨r, c, hr, hsign⟩ := hf
  refine ⟨Fin.cons (zeroFraction n) r, c, ?_, ?_⟩
  · intro h
    exact Fin.cases (zeroFraction_admissible n) hr h
  · intro x
    simpa [Fin.sum_univ_succ, zeroFraction, AffineFraction.eval,
      AffineFraction.numerator, AffineFraction.denominator] using hsign x

theorem affineComputable_mono {n H K : ℕ} {f : (Fin n → Bool) → Bool}
    (hHK : H ≤ K) (hf : affineFractionComputable n H f) : affineFractionComputable n K f :=
  Nat.le_induction (P := fun K _ ↦ affineFractionComputable n K f) hf
    (fun _ _ h ↦ affineComputable_succ h) K hHK

theorem HStar_ge_five (f : (Fin 17 → Bool) → Bool) (hf : LocalPattern f) :
    5 ≤ HStar 17 f := by
  by_contra h
  have hle : HStar 17 f ≤ 4 := by omega
  apply not_computable_four f hf
  apply (computableWithHeadsN_iff_affineFractionComputable 4 f).mpr
  exact affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ f).mp (HStar_computable f))

theorem SharedHStar_ge_five (f : (Fin 17 → Bool) → Bool) (hf : LocalPattern f) :
    5 ≤ SharedHStar 17 f := by
  simpa only [SharedHStar_eq_HStar] using HStar_ge_five f hf

end

end HeadComplexity.FourHeadLocalPattern
