import HeadComplexity.Research.BooleanPolynomialSupport
import HeadComplexity.Atoms.Restriction
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.style.header false

/-!
A point indicator cannot be uniformly approximated by too few rational heads
when every common denominator is largest at that point. The hypothesis is
satisfied at the all-one vertex by heads with positive coherent orientation.
No numerator or cancellation bounds are imposed.
-/
noncomputable section
namespace HeadComplexity.MonotonePoleLocalization
open MvPolynomial Finset
open scoped BigOperators

variable {n H : ℕ}

def pointIndicator (v x : Fin n → Bool) : ℝ := if x = v then 1 else 0

def cubeEvalLinear : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ((Fin n → Bool) → ℝ) where
  toFun P x := eval (cubePoint x) P
  map_add' P Q := by ext x; exact map_add _ _ _
  map_smul' c P := by ext x; simp

def polynomialTables (d : ℕ) : Submodule ℝ ((Fin n → Bool) → ℝ) :=
  (restrictTotalDegree (Fin n) ℝ d).map cubeEvalLinear

lemma mem_polynomialTables (d : ℕ) (g : (Fin n → Bool) → ℝ) :
    g ∈ polynomialTables d ↔ ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ d ∧ ∀ x, eval (cubePoint x) P = g x := by
  simp only [polynomialTables, Submodule.mem_map, mem_restrictTotalDegree]
  constructor
  · rintro ⟨P,hP,he⟩
    exact ⟨P,hP,fun x => congrFun he x⟩
  · rintro ⟨P,hP,he⟩
    exact ⟨P,hP,funext he⟩

/-- The Boolean degree subspace is closed even when approximation polynomials
have unbounded coefficients. -/
theorem exact_of_uniform_polynomial_approximation (d : ℕ)
    (g : (Fin n → Bool) → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ d ∧ ∀ x, |eval (cubePoint x) P - g x| < ε) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ d ∧ ∀ x, eval (cubePoint x) P = g x := by
  have hc : IsClosed (polynomialTables (n := n) d : Set ((Fin n → Bool) → ℝ)) :=
    (polynomialTables d).closed_of_finiteDimensional
  apply (mem_polynomialTables d g).mp
  change g ∈ (polynomialTables (n := n) d : Set ((Fin n → Bool) → ℝ))
  rw [← hc.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨P,hP,herr⟩ := h ε hε
  refine ⟨cubeEvalLinear P, ?_, ?_⟩
  · exact (mem_polynomialTables d _).mpr ⟨P,hP,fun _ => rfl⟩
  · rw [dist_comm, dist_eq_norm]
    apply (pi_norm_lt_iff hε).mpr
    intro x
    simpa [cubeEvalLinear,Real.norm_eq_abs] using herr x

/-- A point indicator has Boolean polynomial degree exactly the ambient
number of bits, including as a limit of bounded-degree polynomial tables. -/
theorem dimension_le_of_point_polynomial_approximation (v : Fin n → Bool)
    (h : ∀ ε : ℝ, 0 < ε → ∃ P : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ H ∧ ∀ x, |eval (cubePoint x) P - pointIndicator v x| < ε) :
    n ≤ H := by
  classical
  obtain ⟨P,hP,he⟩ := exact_of_uniform_polynomial_approximation H (pointIndicator v) h
  have hs := BooleanPolynomialSupport.two_pow_le_degree_mul_support P hP
    ⟨v, by rw [he]; simp [pointIndicator]⟩
  have hsupport : BooleanPolynomialSupport.supportSize (fun x => eval (cubePoint x) P) = 1 := by
    simp only [BooleanPolynomialSupport.supportSize,he]
    simp [pointIndicator]
  rw [hsupport,mul_one] at hs
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hs

/-- Arbitrary numerator coefficients and cancellation do not overcome
monotone denominator normalization at a fixed vertex. -/
theorem dimension_le_of_maximal_denominator_approximation (v : Fin n → Bool)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (φ : Fin H → FracAtom n) (c : ℝ),
      (∀ x, eval (cubePoint x) (atomDenProduct φ) ≤
        eval (cubePoint v) (atomDenProduct φ)) ∧
      ∀ x, |(c + ∑ j, (φ j).eval x) - pointIndicator v x| < ε) :
    n ≤ H := by
  apply dimension_le_of_point_polynomial_approximation v
  intro ε hε
  obtain ⟨φ,c,hmax,herr⟩ := h ε hε
  let D := eval (cubePoint v) (atomDenProduct φ)
  have hD : 0 < D := atomDenProduct_eval_pos φ v
  refine ⟨C D⁻¹ * clearedAtomPoly φ c, ?_, ?_⟩
  · exact (totalDegree_mul _ _).trans (by
      simpa using clearedAtomPoly_totalDegree_le φ c)
  · intro x
    have hx : 0 < eval (cubePoint x) (atomDenProduct φ) := atomDenProduct_eval_pos φ x
    let r := eval (cubePoint x) (atomDenProduct φ) / D
    have hr : 0 ≤ r := (div_pos hx hD).le
    have hr1 : r ≤ 1 := (div_le_one hD).mpr (hmax x)
    have hid : eval (cubePoint x) (C D⁻¹ * clearedAtomPoly φ c) - pointIndicator v x =
        r * ((c + ∑ j, (φ j).eval x) - pointIndicator v x) := by
      simp only [map_mul,eval_C,clearedAtomPoly_eval]
      by_cases hv : x = v
      · subst x
        simp [pointIndicator,r,D,ne_of_gt hD]
      · simp [pointIndicator,hv,r,div_eq_mul_inv]
        ring
    rw [hid,abs_mul,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_right hr1 (abs_nonneg _)).trans_lt (by simpa using herr x)

/-- Positive coherent orientation makes each denominator largest at all ones. -/
lemma denPoly_le_at_top (φ : FracAtom n) (hφ : 1 ≤ φ.α) (x : Fin n → Bool) :
    eval (cubePoint x) φ.denPoly ≤ eval (cubePoint (fun _ => true)) φ.denPoly := by
  rw [φ.denPoly_eval,φ.denPoly_eval]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  unfold FracAtom.wt
  cases x i <;> simp only [Bool.false_eq_true,↓reduceIte]
  · simpa using le_mul_of_one_le_right (φ.hρ i).le hφ
  · rfl

/-- Arbitrary-precision approximation of an all-one point indicator by
positive-orientation original atoms requires at least one head per bit. -/
theorem dimension_le_of_positive_atom_approximation
    (h : ∀ ε : ℝ, 0 < ε → ∃ (φ : Fin H → FracAtom n) (c : ℝ),
      (∀ j, 1 ≤ (φ j).α) ∧
      ∀ x, |(c + ∑ j, (φ j).eval x) - pointIndicator (fun _ => true) x| < ε) :
    n ≤ H := by
  apply dimension_le_of_maximal_denominator_approximation (fun _ => true)
  intro ε hε
  obtain ⟨φ,c,hφ,herr⟩ := h ε hε
  refine ⟨φ,c,?_,herr⟩
  intro x
  simp only [atomDenProduct,map_prod]
  exact Finset.prod_le_prod₀ (fun j _ => (φ j).denPoly_pos x |>.le)
    (fun j _ => denPoly_le_at_top (φ j) (hφ j) x)

/-- The negative coherent orientation is maximal at all zeros. -/
lemma denPoly_le_at_bottom (φ : FracAtom n) (hφ : φ.α ≤ 1) (x : Fin n → Bool) :
    eval (cubePoint x) φ.denPoly ≤ eval (cubePoint (fun _ => false)) φ.denPoly := by
  rw [φ.denPoly_eval,φ.denPoly_eval]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  unfold FracAtom.wt
  cases x i <;> simp only [Bool.false_eq_true,↓reduceIte]
  · rfl
  · exact mul_le_mul_of_nonneg_left hφ (φ.hρ i).le

/-- The corresponding all-zero point lower bound for negative orientation. -/
theorem dimension_le_of_negative_atom_approximation
    (h : ∀ ε : ℝ, 0 < ε → ∃ (φ : Fin H → FracAtom n) (c : ℝ),
      (∀ j, (φ j).α ≤ 1) ∧
      ∀ x, |(c + ∑ j, (φ j).eval x) - pointIndicator (fun _ => false) x| < ε) :
    n ≤ H := by
  apply dimension_le_of_maximal_denominator_approximation (fun _ => false)
  intro ε hε
  obtain ⟨φ,c,hφ,herr⟩ := h ε hε
  refine ⟨φ,c,?_,herr⟩
  intro x
  simp only [atomDenProduct,map_prod]
  exact Finset.prod_le_prod₀ (fun j _ => (φ j).denPoly_pos x |>.le)
    (fun j _ => denPoly_le_at_bottom (φ j) (hφ j) x)

lemma pointIndicator_face {m : ℕ} (ρ : CoordFace m n)
    (v x : Fin m → Bool) :
    pointIndicator (ρ.apply v) (ρ.apply x) = pointIndicator v x := by
  have he : ρ.apply x = ρ.apply v ↔ x = v := by
    constructor
    · intro h
      ext i
      simpa only [CoordFace.apply_free] using congrFun h (ρ.free i)
    · exact congrArg ρ.apply
  simp only [pointIndicator,he]

/-- A positive-orientation family approximating a mixed point requires one
head per positive literal, by restricting to its lower coordinate face. -/
theorem face_dimension_le_of_positive_atom_approximation {m : ℕ}
    (ρ : CoordFace m n)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (φ : Fin H → FracAtom n) (c : ℝ),
      (∀ j, 1 ≤ (φ j).α) ∧
      ∀ x, |(c + ∑ j, (φ j).eval x) -
        pointIndicator (ρ.apply (fun _ => true)) x| < ε) :
    m ≤ H := by
  apply dimension_le_of_positive_atom_approximation
  intro ε hε
  obtain ⟨φ,c,hφ,herr⟩ := h ε hε
  refine ⟨fun j => (φ j).restrict ρ,c,hφ,?_⟩
  intro x
  simpa only [FracAtom.restrict_eval,pointIndicator_face] using herr (ρ.apply x)

/-- The analogous upper-face restriction for negative coherent orientation. -/
theorem face_dimension_le_of_negative_atom_approximation {m : ℕ}
    (ρ : CoordFace m n)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (φ : Fin H → FracAtom n) (c : ℝ),
      (∀ j, (φ j).α ≤ 1) ∧
      ∀ x, |(c + ∑ j, (φ j).eval x) -
        pointIndicator (ρ.apply (fun _ => false)) x| < ε) :
    m ≤ H := by
  apply dimension_le_of_negative_atom_approximation
  intro ε hε
  obtain ⟨φ,c,hφ,herr⟩ := h ε hε
  refine ⟨fun j => (φ j).restrict ρ,c,hφ,?_⟩
  intro x
  simpa only [FracAtom.restrict_eval,pointIndicator_face] using herr (ρ.apply x)

end HeadComplexity.MonotonePoleLocalization


