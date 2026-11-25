import HeadComplexity.Research.FullCubeNormOptimization

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.CoherentEdgeVariation
open scoped BigOperators
open Finset

theorem sum_div_le {I : Type*} (s : Finset I) (a d : I → ℝ) (D C : ℝ)
    (hD : 0 < D) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hd : ∀ i ∈ s, D ≤ d i) (hbudget : ∑ i ∈ s, a i ≤ C*D) :
    ∑ i ∈ s, a i/d i ≤ C := by
  calc
    ∑ i ∈ s, a i/d i ≤ ∑ i ∈ s, a i/D := by
      exact sum_le_sum fun i hi => div_le_div_of_nonneg_left (ha i hi) hD (hd i hi)
    _ = (∑ i ∈ s, a i)/D := by rw [sum_div]
    _ ≤ C := (div_le_iff₀ hD).mpr hbudget

/-- The subset budget is the full-cube norm bound after deleting active bits. -/
theorem sum_abs_edge_le {I : Type*} [Fintype I] [DecidableEq I]
    (b c u : ℝ) (beta p : I → ℝ)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hpos : ∀ s : Finset I, 0 < b-∑ i ∈ s, beta i)
    (hbound : ∀ s : Finset I,
      -u*(b-∑ i ∈ s, beta i) ≤ c*(b-∑ i ∈ s, beta i)-∑ i ∈ s, p i ∧
      c*(b-∑ i ∈ s, beta i)-∑ i ∈ s, p i ≤ u*(b-∑ i ∈ s, beta i)) :
    ∑ i, |p i/(b-beta i)| ≤ 2*u := by
  classical
  let P : Finset I := univ.filter fun i => 0 ≤ p i
  let Q : Finset I := univ.filter fun i => ¬0 ≤ p i
  have hP (i : I) (hi : i ∈ P) : 0 ≤ p i := (mem_filter.mp hi).2
  have hQ (i : I) (hi : i ∈ Q) : p i < 0 := lt_of_not_ge (mem_filter.mp hi).2
  have hd (i : I) : 0 < b-beta i := by simpa using hpos {i}
  have hden (s : Finset I) (i : I) (hi : i ∈ s) :
      b-∑ j ∈ s, beta j ≤ b-beta i := by
    have hh := single_le_sum (fun j _ => hbeta j) hi
    linarith
  have hplus : ∑ i ∈ P, p i/(b-beta i) ≤ c+u := by
    apply sum_div_le P p (fun i => b-beta i) (b-∑ i ∈ P, beta i) (c+u)
      (hpos P) hP (hden P)
    have hh := (hbound P).1
    nlinarith
  have hminus : ∑ i ∈ Q, (-p i)/(b-beta i) ≤ u-c := by
    apply sum_div_le Q (fun i => -p i) (fun i => b-beta i)
      (b-∑ i ∈ Q, beta i) (u-c) (hpos Q)
      (fun i hi => le_of_lt (neg_pos.mpr (hQ i hi))) (hden Q)
    have hh := (hbound Q).2
    simp only [sum_neg_distrib]
    nlinarith
  have hs : (∑ i, |p i/(b-beta i)|) =
      (∑ i ∈ P, p i/(b-beta i))+(∑ i ∈ Q, (-p i)/(b-beta i)) := by
    rw [← sum_filter_add_sum_filter_not (s := univ) (p := fun i => 0 ≤ p i)]
    congr 1
    · apply sum_congr rfl
      intro i hi
      exact abs_of_nonneg (div_nonneg (hP i hi) (le_of_lt (hd i)))
    · apply sum_congr rfl
      intro i hi
      rw [abs_of_neg (div_neg_of_neg_of_pos (hQ i hi) (hd i)), neg_div]
  rw [hs]
  linarith

/-- Top-corner downward variation of a positive affine ratio. -/
theorem affine_ratio_corner_variation {I : Type*} [Fintype I] [DecidableEq I]
    (a₀ b₀ u : ℝ) (a beta : I → ℝ) (hb₀ : 0 < b₀)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hnorm : ∀ s : Finset I, |(a₀+∑ i ∈ s, a i)/(b₀+∑ i ∈ s, beta i)| ≤ u) :
    ∑ i, |(a₀+∑ j, a j)/(b₀+∑ j, beta j)-
      (a₀+∑ j ∈ univ.erase i, a j)/(b₀+∑ j ∈ univ.erase i, beta j)| ≤ 2*u := by
  classical
  let B := b₀+∑ i, beta i
  let A := a₀+∑ i, a i
  have hB : 0 < B := add_pos_of_pos_of_nonneg hb₀ (sum_nonneg fun i _ => hbeta i)
  let c := A/B
  have hc : c*B=A := div_mul_cancel₀ A (ne_of_gt hB)
  have hcomp (s : Finset I) (v : I → ℝ) :
      ∑ i ∈ univ\s, v i = (∑ i, v i)-∑ i ∈ s, v i :=
    (eq_sub_iff_add_eq).mpr (sum_sdiff (subset_univ s))
  have hpos (s : Finset I) : 0 < B-∑ i ∈ s, beta i := by
    have hh : 0 ≤ ∑ i ∈ univ\s, beta i := sum_nonneg fun i _ => hbeta i
    rw [hcomp] at hh
    dsimp [B]
    linarith
  have hbudget (s : Finset I) :
      -u*(B-∑ i ∈ s, beta i) ≤
          c*(B-∑ i ∈ s, beta i)-∑ i ∈ s, (a i-c*beta i) ∧
      c*(B-∑ i ∈ s, beta i)-∑ i ∈ s, (a i-c*beta i) ≤
          u*(B-∑ i ∈ s, beta i) := by
    have hh := hnorm (univ\s)
    have heB : b₀+∑ i ∈ univ\s, beta i = B-∑ i ∈ s, beta i := by
      rw [hcomp]; dsimp [B]; ring
    have heA : a₀+∑ i ∈ univ\s, a i =
        c*(B-∑ i ∈ s, beta i)-∑ i ∈ s, (a i-c*beta i) := by
      rw [hcomp, sum_sub_distrib, ← mul_sum]
      dsimp [A] at hc
      nlinarith
    rw [heB, abs_div, abs_of_pos (hpos s), div_le_iff₀ (hpos s), abs_le, heA] at hh
    simpa only [neg_mul] using hh
  have hv := sum_abs_edge_le B c u beta (fun i => a i-c*beta i) hbeta hpos hbudget
  have he (i : I) : c-(a₀+∑ j ∈ univ.erase i, a j)/(b₀+∑ j ∈ univ.erase i, beta j) =
      (a i-c*beta i)/(B-beta i) := by
    have ha := sum_erase_add univ a (mem_univ i)
    have hb := sum_erase_add univ beta (mem_univ i)
    have hd : 0 < B-beta i := by simpa using hpos {i}
    have hea : a₀+∑ j ∈ univ.erase i, a j = A-a i := by dsimp [A]; linarith
    have heb : b₀+∑ j ∈ univ.erase i, beta j = B-beta i := by dsimp [B]; linarith
    rw [hea,heb]
    field_simp [ne_of_gt hd]
    nlinarith [hc]
  simpa only [← he] using hv

/-- A mixed-star contrast, normalized over both edge families. -/
def mixedContrast {I J : Type*} [Fintype I] [Fintype J]
    (v : ℝ) (down : I → ℝ) (up : J → ℝ) (cross : I → J → ℝ) : ℝ :=
  (∑ j, ∑ i, ((v-down i)-(up j-cross i j)))/(Fintype.card I)/(Fintype.card J)

theorem mixedContrast_bound_of_down {I J : Type*} [Fintype I] [Fintype J]
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J)
    (v a : ℝ) (down : I → ℝ) (up : J → ℝ) (cross : I → J → ℝ)
    (hbase : ∑ i, |v-down i| ≤ 2*a)
    (hfaces : ∀ j, ∑ i, |up j-cross i j| ≤ 2*a) :
    |mixedContrast v down up cross| ≤ 4*a/(Fintype.card I) := by
  have hIr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have hJr : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
  have hrow (j : J) : |∑ i, ((v-down i)-(up j-cross i j))| ≤ 4*a := by
    calc
      _ ≤ ∑ i, |(v-down i)-(up j-cross i j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (|v-down i|+|up j-cross i j|) :=
        sum_le_sum fun i _ => abs_sub _ _
      _ = (∑ i, |v-down i|)+(∑ i, |up j-cross i j|) := sum_add_distrib
      _ ≤ 4*a := by linarith [hfaces j]
  have htotal : |∑ j, ∑ i, ((v-down i)-(up j-cross i j))| ≤
      (Fintype.card J : ℝ)*(4*a) := by
    exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hrow j).trans_eq (by simp))
  unfold mixedContrast
  rw [abs_div, abs_div, abs_of_pos hIr, abs_of_pos hJr]
  apply (div_le_iff₀ hJr).mpr
  apply (div_le_iff₀ hIr).mpr
  have he : 4*a/(Fintype.card I)*(Fintype.card J)*(Fintype.card I) =
      (Fintype.card J : ℝ)*(4*a) := by field_simp
  rw [he]
  exact htotal

theorem mixedContrast_swap {I J : Type*} [Fintype I] [Fintype J]
    (v : ℝ) (down : I → ℝ) (up : J → ℝ) (cross : I → J → ℝ) :
    mixedContrast v down up cross = mixedContrast v up down (fun j i => cross i j) := by
  unfold mixedContrast
  rw [sum_comm]
  have he : (∑ i, ∑ j, ((v-down i)-(up j-cross i j))) =
      ∑ i, ∑ j, ((v-up j)-(down i-cross i j)) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

theorem mixedContrast_bound_of_up {I J : Type*} [Fintype I] [Fintype J]
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J)
    (v a : ℝ) (down : I → ℝ) (up : J → ℝ) (cross : I → J → ℝ)
    (hbase : ∑ j, |v-up j| ≤ 2*a)
    (hfaces : ∀ i, ∑ j, |down i-cross i j| ≤ 2*a) :
    |mixedContrast v down up cross| ≤ 4*a/(Fintype.card J) := by
  rw [mixedContrast_swap]
  exact mixedContrast_bound_of_down hJ hI v a up down (fun j i => cross i j) hbase hfaces

end HeadComplexity.CoherentEdgeVariation
