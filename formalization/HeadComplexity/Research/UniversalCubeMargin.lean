import HeadComplexity.Research.UniformMarginCompiler
import HeadComplexity.Research.LowDegreeMarginRepair
import HeadComplexity.Research.MarginInvariance

set_option linter.style.header false

/-!
Every Boolean truth table has a width-`2^n` original-head representation with
relative margin at least `1 / (2 * 3^n + 1)`. The explicit monomial coefficient
mass bound is independent of the truth table. This theorem does not preserve a
smaller input width and therefore does not resolve sparse margin repair.
-/

noncomputable section

namespace HeadComplexity.UniversalCubeMargin

open Finset RelativeMarginQuantifiers UniformMarginCompiler
open scoped BigOperators

def intercept (b : Bool) : ℝ := if b then 0 else 1
def slope (b : Bool) : ℝ := if b then 1 else -1

def vertexCoefficient {n : ℕ} (x : Fin n → Bool) (S : Finset (Fin n)) : ℝ :=
  (∏ i ∈ S, slope (x i)) * ∏ i ∈ Sᶜ, intercept (x i)

def cubeCoefficient {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) : ℝ :=
  ∑ x, signedLabel f x * vertexCoefficient x S

theorem vertex_expansion {n : ℕ} (x y : Fin n → Bool) :
    (∑ S : Finset (Fin n), vertexCoefficient x S * squarefreeMonomial S y) =
      if x = y then 1 else 0 := by
  classical
  have hexp :
      (∏ i, (slope (x i) * boolToReal (y i) + intercept (x i))) =
        ∑ S : Finset (Fin n), vertexCoefficient x S * squarefreeMonomial S y := by
    rw [Fintype.prod_add]
    apply sum_congr rfl
    intro S _
    simp only [vertexCoefficient, squarefreeMonomial, prod_mul_distrib]
    ring
  rw [← hexp]
  by_cases hxy : x = y
  · subst y
    rw [ite_eq_left rfl]
    apply prod_eq_one
    intro i _
    cases x i <;> norm_num [slope, intercept, boolToReal]
  · rw [ite_eq_right hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    apply prod_eq_zero (mem_univ i)
    cases hxi : x i <;> cases hyi : y i <;>
      simp_all [slope, intercept, boolToReal]

theorem cube_expansion {n : ℕ} (f : (Fin n → Bool) → Bool)
    (y : Fin n → Bool) :
    (∑ S : Finset (Fin n), cubeCoefficient f S * squarefreeMonomial S y) =
      signedLabel f y := by
  classical
  simp only [cubeCoefficient, sum_mul]
  rw [sum_comm]
  simp_rw [mul_assoc, ← mul_sum, vertex_expansion]
  simp

theorem vertex_coefficient_mass {n : ℕ} (x : Fin n → Bool) :
    (∑ S : Finset (Fin n), |vertexCoefficient x S|) =
      ∏ i, (|slope (x i)| + |intercept (x i)|) := by
  classical
  rw [Fintype.prod_add]
  apply sum_congr rfl
  intro S _
  simp [vertexCoefficient, abs_mul, abs_prod]

theorem cube_coefficient_mass {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (∑ S : Finset (Fin n), |cubeCoefficient f S|) ≤ (3 : ℝ) ^ n := by
  classical
  calc
    _ ≤ ∑ S : Finset (Fin n), ∑ x, |vertexCoefficient x S| := by
      apply sum_le_sum
      intro S _
      calc
        _ ≤ ∑ x, |signedLabel f x * vertexCoefficient x S| := abs_sum_le_sum_abs _ _
        _ = _ := by
          apply sum_congr rfl
          intro x _
          cases hf : f x <;> simp [signedLabel, hf]
    _ = ∑ x : Fin n → Bool, ∏ i, (|slope (x i)| + |intercept (x i)|) := by
      rw [sum_comm]
      simp_rw [vertex_coefficient_mass]
    _ = ∏ i : Fin n, ∑ b : Bool, (|slope b| + |intercept b|) := by
      exact (Fintype.prod_sum (fun (_i : Fin n) (b : Bool) ↦
        |slope b| + |intercept b|)).symm
    _ = (3 : ℝ) ^ n := by norm_num [slope, intercept, Fintype.sum_bool]

theorem hasRelativeMargin_universal (n : ℕ) (f : (Fin n → Bool) → Bool) :
    HasRelativeMargin n (2 ^ n) f (1 / (2 * (3 : ℝ) ^ n + 1)) := by
  classical
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp
  let e : Fin (2 ^ n) ≃ Finset (Fin n) :=
    (finCongr hcard.symm).trans (Fintype.equivFin (Finset (Fin n))).symm
  let g : Fin (2 ^ n) → (Fin n → Bool) → ℝ := fun h x ↦
    cubeCoefficient f (e h) * squarefreeMonomial (e h) x
  have hg : ∀ h, UniformlyOneAtomApproximable (g h) := by
    intro h epsilon hepsilon
    exact exists_fracAtom_approx_signedMonomial (e h) (cubeCoefficient f (e h))
      epsilon hepsilon
  have hbound : ∀ h x, |g h x| ≤ |cubeCoefficient f (e h)| := by
    intro h x
    dsimp [g]
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left
      (LowDegreeMarginRepair.abs_monomial_le_one (e h) x)
      (abs_nonneg (cubeCoefficient f (e h)))
  have hscore : ∀ x, 1 ≤ signedLabel f x * ((0 : ℝ) + ∑ h, g h x) := by
    intro x
    have heq : (∑ h, g h x) = signedLabel f x := by
      dsimp [g]
      rw [e.sum_comp (fun S ↦ cubeCoefficient f S * squarefreeMonomial S x)]
      exact cube_expansion f x
    rw [zero_add, heq]
    cases hf : f x <;> norm_num [signedLabel, hf]
  have h := hasRelativeMargin_of_uniformlyOneAtomApproximable g hg
    (fun h ↦ |cubeCoefficient f (e h)|) (fun _ ↦ abs_nonneg _) hbound 0 f hscore
  have hmass : (∑ h, |cubeCoefficient f (e h)|) ≤ (3 : ℝ) ^ n := by
    rw [e.sum_comp (fun S ↦ |cubeCoefficient f S|)]
    exact cube_coefficient_mass f
  apply hasRelativeMargin_mono _ h
  simp only [abs_zero, zero_add]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem hasRelativeMargin_universal_at_width (n K : ℕ)
    (hK : 2 ^ n ≤ K) (f : (Fin n → Bool) → Bool) :
    HasRelativeMargin n K f (1 / (2 * (3 : ℝ) ^ n + 1)) :=
  hasRelativeMargin_mono_width hK (hasRelativeMargin_universal n f)

/-- A `k`-coordinate junta has the same width and margin guarantee inside any
larger cube. Every approximating head is admissible on that entire larger cube.
-/
theorem hasRelativeMargin_of_junta (n k : ℕ) (ι : Fin k → Fin n)
    (hι : Function.Injective ι) (F : (Fin k → Bool) → Bool) :
    HasRelativeMargin n (2 ^ k) (fun x ↦ F (fun i ↦ x (ι i)))
      (1 / (2 * (3 : ℝ) ^ k + 1)) := by
  classical
  have hcard : Fintype.card (Finset (Fin k)) = 2 ^ k := by simp
  let e : Fin (2 ^ k) ≃ Finset (Fin k) :=
    (finCongr hcard.symm).trans (Fintype.equivFin (Finset (Fin k))).symm
  let g : Fin (2 ^ k) → (Fin n → Bool) → ℝ := fun h x ↦
    cubeCoefficient F (e h) * squarefreeMonomial ((e h).image ι) x
  have hmono (S : Finset (Fin k)) (x : Fin n → Bool) :
      squarefreeMonomial (S.image ι) x =
        squarefreeMonomial S (fun i ↦ x (ι i)) := by
    unfold squarefreeMonomial
    exact prod_image (fun _ _ _ _ hij ↦ hι hij)
  have hg : ∀ h, UniformlyOneAtomApproximable (g h) := by
    intro h epsilon hepsilon
    exact exists_fracAtom_approx_signedMonomial ((e h).image ι)
      (cubeCoefficient F (e h)) epsilon hepsilon
  have hbound : ∀ h x, |g h x| ≤ |cubeCoefficient F (e h)| := by
    intro h x
    dsimp [g]
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left
      (LowDegreeMarginRepair.abs_monomial_le_one ((e h).image ι) x)
      (abs_nonneg (cubeCoefficient F (e h)))
  have hscore : ∀ x, 1 ≤ signedLabel (fun x ↦ F (fun i ↦ x (ι i))) x *
      ((0 : ℝ) + ∑ h, g h x) := by
    intro x
    have heq : (∑ h, g h x) = signedLabel F (fun i ↦ x (ι i)) := by
      dsimp [g]
      simp_rw [hmono]
      rw [e.sum_comp (fun S ↦ cubeCoefficient F S *
        squarefreeMonomial S (fun i ↦ x (ι i)))]
      exact cube_expansion F _
    rw [zero_add, heq]
    cases hf : F (fun i ↦ x (ι i)) <;> norm_num [signedLabel, hf]
  have h := hasRelativeMargin_of_uniformlyOneAtomApproximable g hg
    (fun h ↦ |cubeCoefficient F (e h)|) (fun _ ↦ abs_nonneg _) hbound 0 _ hscore
  have hmass : (∑ h, |cubeCoefficient F (e h)|) ≤ (3 : ℝ) ^ k := by
    rw [e.sum_comp (fun S ↦ |cubeCoefficient F S|)]
    exact cube_coefficient_mass F
  apply hasRelativeMargin_mono _ h
  simp only [abs_zero, zero_add]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- At width `N` the universally low-margin exceptional class is empty. The
comparison width is essential: this does not assert emptiness at width `O(H)`.
-/
theorem allRepresentationsLowMargin_eq_empty_of_full_width (n H K : ℕ)
    (hK : 2 ^ n ≤ K) (gamma : ℝ)
    (hgamma : gamma ≤ 1 / (2 * (3 : ℝ) ^ n + 1)) :
    allRepresentationsLowMargin n H K gamma = ∅ := by
  classical
  ext f
  constructor
  · intro hf
    exact (hf.2 (hasRelativeMargin_mono hgamma
      (hasRelativeMargin_universal_at_width n K hK f))).elim
  · simp

end HeadComplexity.UniversalCubeMargin
