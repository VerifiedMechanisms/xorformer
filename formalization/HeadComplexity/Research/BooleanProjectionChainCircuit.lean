import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
A chain of anchored four-point projection ghosts has 2n+2 remaining points.
The scalar identity is universal in the test function, so it applies to every
projection moment and every reciprocal kernel. The coefficient lemma proves
that the zero and singleton projection rows already determine its residues up
to one common scale.
-/
noncomputable section
namespace HeadComplexity.BooleanProjectionChainCircuit
open Finset
open scoped BigOperators

def partialSum (x : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, boolToReal (x i)

lemma partialSum_zero (x : ℕ → Bool) : partialSum x 0 = 0 := by simp [partialSum]
lemma partialSum_succ (x : ℕ → Bool) (k : ℕ) :
    partialSum x (k + 1) = partialSum x k + boolToReal (x k) := by
  simp [partialSum,sum_range_succ]

/-- The chain identity holds for every scalar kernel and every Boolean input. -/
theorem scalar_function_identity (F : ℝ → ℝ) (B : ℝ) (x : ℕ → Bool) (n : ℕ) :
    F (B + partialSum x n) - F B +
      ∑ i ∈ range n, (F (B + 1 + partialSum x i - boolToReal (x i)) -
        F (B + 1 + partialSum x i)) = 0 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [partialSum_succ,sum_range_succ]
      cases hx : x n <;> simp only [hx,boolToReal,↓reduceIte] at *
      · simpa only [Bool.false_eq_true,↓reduceIte,add_zero,sub_zero,sub_self,add_zero] using ih
      · have he : B + 1 + partialSum x n - 1 = B + partialSum x n := by ring
        have he' : B + (partialSum x n + 1) = B + 1 + partialSum x n := by ring
        rw [he,he']
        linarith

/-- In particular, every order of anchored Boolean projection moments vanishes. -/
theorem all_projection_moments (q n : ℕ) (B : ℝ) (x : ℕ → Bool) :
    (B + partialSum x n)^q - B^q +
      ∑ i ∈ range n, ((B + 1 + partialSum x i - boolToReal (x i))^q -
        (B + 1 + partialSum x i)^q) = 0 :=
  scalar_function_identity (fun t => t^q) B x n

/-- Reciprocal kernels give exact identities among distinct affine poles. -/
theorem reciprocal_identity (n : ℕ) (B : ℝ) (x : ℕ → Bool) :
    (B + partialSum x n)⁻¹ - B⁻¹ +
      ∑ i ∈ range n, ((B + 1 + partialSum x i - boolToReal (x i))⁻¹ -
        (B + 1 + partialSum x i)⁻¹) = 0 :=
  scalar_function_identity (fun t => t⁻¹) B x n

/-- These equations are the coefficient sums on the zero query and the first
 two levels of each singleton query. They force the unique chain relation. -/
theorem coefficients_eq_of_zero_singleton_rows (n : ℕ) (a b : ℝ)
    (u v : ℕ → ℝ) (hzero : a + b = 0)
    (hlow : ∀ k < n, a + v k = 0)
    (hmid : ∀ k < n, b + u k + ∑ i ∈ range k, (u i + v i) = 0) :
    b = -a ∧ ∀ k < n, u k = a ∧ v k = -a := by
  have hb : b = -a := by linarith
  have hv : ∀ k < n, v k = -a := by intro k hk; linarith [hlow k hk]
  have hu : ∀ k < n, u k = a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hs : ∑ i ∈ range k, (u i + v i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hik : i < k := mem_range.mp hi
        rw [ih i hik (hik.trans hk),hv i (hik.trans hk)]
        ring
      have hm := hmid k hk
      rw [hs,hb] at hm
      linarith
  exact ⟨hb,fun k hk => ⟨hu k hk,hv k hk⟩⟩


lemma partialSum_singleton (k j : ℕ) :
    partialSum (fun i => decide (i = k)) j = if k < j then 1 else 0 := by
  simp [partialSum,boolToReal,Finset.sum_ite_eq',Finset.mem_range]

lemma zero_probe_singleton (k i : ℕ) (u v : ℝ) :
    u * (if 1 + partialSum (fun j => decide (j = k)) i = (0 : ℝ) then 1 else 0) +
      v * (if 1 + partialSum (fun j => decide (j = k)) i -
        boolToReal (decide (i = k)) = (0 : ℝ) then 1 else 0) =
      if i = k then v else 0 := by
  by_cases he : i = k
  · subst i
    norm_num [partialSum_singleton,boolToReal]
  · by_cases hki : k < i <;> norm_num [partialSum_singleton,boolToReal,he,hki]

lemma one_probe_singleton (k i : ℕ) (u v : ℝ) :
    u * (if 1 + partialSum (fun j => decide (j = k)) i = (1 : ℝ) then 1 else 0) +
      v * (if 1 + partialSum (fun j => decide (j = k)) i -
        boolToReal (decide (i = k)) = (1 : ℝ) then 1 else 0) =
      (if i < k then u + v else 0) + (if i = k then u else 0) := by
  by_cases he : i = k
  · subst i
    norm_num [partialSum_singleton,boolToReal]
  · by_cases hki : k < i
    · have hik : ¬ i < k := by omega
      norm_num [partialSum_singleton,boolToReal,he,hki,hik]
    · have hik : i < k := by omega
      norm_num [partialSum_singleton,boolToReal,he,hki,hik]

/-- Among these distinct support points, every constant-residue identity is a
scalar multiple of the displayed chain identity. No restriction on residues
or on the scalar test function is used. -/
theorem constant_residue_identity_unique (n : ℕ) (a b : ℝ) (u v : ℕ → ℝ)
    (h : ∀ (F : ℝ → ℝ) (x : ℕ → Bool),
      a * F 0 + b * F (partialSum x n) +
        ∑ i ∈ range n, (u i * F (1 + partialSum x i) +
          v i * F (1 + partialSum x i - boolToReal (x i))) = 0) :
    b = -a ∧ ∀ k < n, u k = a ∧ v k = -a := by
  apply coefficients_eq_of_zero_singleton_rows
  · have hz := h (fun t => if t = 0 then 1 else 0) (fun _ => false)
    simpa [partialSum,boolToReal] using hz
  · intro k hk
    have hz := h (fun t => if t = 0 then 1 else 0) (fun i => decide (i = k))
    simp only [partialSum_singleton,hk,↓reduceIte] at hz
    have hs : (∑ i ∈ range n,
        (u i * (if 1 + (if k < i then 1 else 0) = (0 : ℝ) then 1 else 0) +
        v i * (if 1 + (if k < i then 1 else 0) - boolToReal (decide (i = k)) =
          (0 : ℝ) then 1 else 0))) = v k := by
      have hh := fun i => zero_probe_singleton k i (u i) (v i)
      simp only [partialSum_singleton] at hh
      simp_rw [hh]
      simp [hk]
    rw [hs] at hz
    simpa using hz
  · intro k hk
    have hz := h (fun t => if t = 1 then 1 else 0) (fun i => decide (i = k))
    simp only [partialSum_singleton,hk,↓reduceIte] at hz
    have hs : (∑ i ∈ range n,
        (u i * (if 1 + (if k < i then 1 else 0) = (1 : ℝ) then 1 else 0) +
        v i * (if 1 + (if k < i then 1 else 0) - boolToReal (decide (i = k)) =
          (1 : ℝ) then 1 else 0))) =
        (∑ i ∈ range k, (u i + v i)) + u k := by
      have hh := fun i => one_probe_singleton k i (u i) (v i)
      simp only [partialSum_singleton] at hh
      simp_rw [hh,Finset.sum_add_distrib]
      have htr : (∑ i ∈ range n, if i < k then u i + v i else 0) =
          ∑ i ∈ range k, (u i + v i) := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [mem_filter,mem_range]
        omega
      rw [htr]
      simp [hk,Finset.sum_add_distrib]
    rw [hs] at hz
    norm_num at hz
    linarith

end HeadComplexity.BooleanProjectionChainCircuit

