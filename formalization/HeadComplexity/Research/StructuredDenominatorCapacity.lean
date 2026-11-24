import HeadComplexity.Research.DenominatorCapacity
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.style.header false

/-!
Margin-free capacity for denominator configurations on varying polynomial curves
and in a union of varying low dimensional affine subspaces.  These classes retain
arbitrary real numerator coefficients and signed cancellation.
-/

noncomputable section
namespace HeadComplexity.StructuredDenominatorCapacity
open Finset MvPolynomial DenominatorCapacity
open scoped BigOperators

variable {n H r d G : ℕ}

abbrev CurveParameter (n H r : ℕ) := (Fin n × Fin (r + 1)) ⊕ Fin H

@[simp] theorem card_curveParameter :
    Fintype.card (CurveParameter n H r) = n * (r + 1) + H := by
  simp [CurveParameter]

/-- Normalized denominator slopes on a varying polynomial curve of degree at most `r`. -/
def curveDen (h : Fin H) (x : Input n) : MvPolynomial (CurveParameter n H r) ℝ :=
  1 + ∑ i, C (boolToReal (x i)) * ∑ j : Fin (r + 1),
    X (Sum.inl (i,j)) * X (Sum.inr h) ^ j.val

theorem curveDen_totalDegree_le (h : Fin H) (x : Input n) :
    (curveDen (r := r) h x).totalDegree ≤ r + 1 := by
  unfold curveDen
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  apply totalDegree_finsetSum_le
  intro j _
  have hp := totalDegree_pow (X (Sum.inr h) : MvPolynomial (CurveParameter n H r) ℝ) j.val
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_X, mul_one] at hp ⊢
  omega

theorem card_curve_le (hK : n * (r + 1) + H + 1 ≤ 2 ^ n) :
    ((represented (curveDen (n := n) (H := H) (r := r))).ncard : ℝ) ≤
      ((2 ^ n + 2 * (n * H + 1)).choose (n * H + 1) : ℝ) *
      2 ^ (n * H + 1) *
      (4 * Real.exp 1 * (2 * ((r + 1) * H) * (n * H + 1) + 1) * (2 : ℝ) ^ n /
        (n * (r + 1) + H + 1)) ^ (n * (r + 1) + H + 1) := by
  have h := card_represented_le (curveDen (n := n) (H := H) (r := r))
    curveDen_totalDegree_le (by simpa only [card_curveParameter] using hK)
  simpa only [card_curveParameter, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h

abbrev ClusterParameter (n H d G : ℕ) :=
  (Fin G × (Fin n ⊕ (Fin d × Fin n))) ⊕ (Fin H × Fin d)

@[simp] theorem card_clusterParameter :
    Fintype.card (ClusterParameter n H d G) = G * n * (d + 1) + d * H := by
  simp [ClusterParameter]
  ring

/-- A fixed assignment of heads to varying affine `d`-planes. -/
def clusterDen (g : Fin H → Fin G) (h : Fin H) (x : Input n) :
    MvPolynomial (ClusterParameter n H d G) ℝ :=
  1 + ∑ i, C (boolToReal (x i)) *
    (X (Sum.inl (g h, Sum.inl i)) + ∑ j : Fin d,
      X (Sum.inl (g h, Sum.inr (j,i))) * X (Sum.inr (h,j)))

theorem clusterDen_totalDegree_le (g : Fin H → Fin G) (h : Fin H) (x : Input n) :
    (clusterDen (d := d) g h x).totalDegree ≤ 2 := by
  unfold clusterDen
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

theorem card_cluster_assignment_le (g : Fin H → Fin G)
    (hK : G * n * (d + 1) + d * H + 1 ≤ 2 ^ n) :
    ((represented (clusterDen (n := n) (d := d) g)).ncard : ℝ) ≤
      ((2 ^ n + 2 * (n * H + 1)).choose (n * H + 1) : ℝ) *
      2 ^ (n * H + 1) *
      (4 * Real.exp 1 * (4 * H * (n * H + 1) + 1) * (2 : ℝ) ^ n /
        (G * n * (d + 1) + d * H + 1)) ^ (G * n * (d + 1) + d * H + 1) := by
  have h := card_represented_le (clusterDen (n := n) (d := d) g)
    (clusterDen_totalDegree_le g) (by simpa only [card_clusterParameter] using hK)
  simpa only [card_clusterParameter, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num, ← mul_assoc] using h

/-- Allow the head-to-cluster assignment itself to vary. -/
def clustered : Set (Input n → Bool) :=
  ⋃ g : Fin H → Fin G, represented (clusterDen (n := n) (d := d) g)

theorem card_clustered_le (hK : G * n * (d + 1) + d * H + 1 ≤ 2 ^ n) :
    ((clustered (n := n) (H := H) (d := d) (G := G)).ncard : ℝ) ≤
      G ^ H * (((2 ^ n + 2 * (n * H + 1)).choose (n * H + 1) : ℝ) *
      2 ^ (n * H + 1) *
      (4 * Real.exp 1 * (4 * H * (n * H + 1) + 1) * (2 : ℝ) ^ n /
        (G * n * (d + 1) + d * H + 1)) ^ (G * n * (d + 1) + d * H + 1)) := by
  classical
  have hcard := Set.ncard_iUnion_le_of_fintype
    (fun g : Fin H → Fin G => represented (clusterDen (n := n) (d := d) g))
  have hcast : ((clustered (n := n) (H := H) (d := d) (G := G)).ncard : ℝ) ≤
      ∑ g : Fin H → Fin G, ((represented (clusterDen (n := n) (d := d) g)).ncard : ℝ) := by
    exact_mod_cast hcard
  refine hcast.trans ((sum_le_sum (fun g _ => card_cluster_assignment_le g hK)).trans_eq ?_)
  simp

end HeadComplexity.StructuredDenominatorCapacity
