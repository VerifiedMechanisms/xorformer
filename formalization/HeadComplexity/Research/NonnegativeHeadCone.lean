import HeadComplexity.Research.CoherentEdgeVariation

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.NonnegativeHeadCone
open Finset
open scoped BigOperators

/-- The affine corner identity and denominator monotonicity suffice. -/
theorem corner_ratio_le {I : Type*} [Fintype I]
    (A B A₀ : ℝ) (a b : I → ℝ) (hB : 0 < B) (hA₀ : 0 ≤ A₀)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i ∧ b i ≤ B)
    (hcard : 2 ≤ Fintype.card I)
    (hsum : ∑ i, a i = ((Fintype.card I : ℝ)-1)*A+A₀) :
    A/B ≤ (∑ i, a i/b i)/((Fintype.card I : ℝ)-1) := by
  have hr : (0 : ℝ) < (Fintype.card I : ℝ)-1 := by
    have hh : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hcard
    linarith
  apply (le_div_iff₀ hr).mpr
  have hh : (∑ i, a i)/B ≤ ∑ i, a i/b i := by
    rw [sum_div]
    exact sum_le_sum fun i _ => div_le_div_of_nonneg_left (ha i) (hb i).1 (hb i).2
  rw [hsum] at hh
  have hn : 0 ≤ A₀/B := div_nonneg hA₀ (le_of_lt hB)
  have he : (((Fintype.card I : ℝ)-1)*A+A₀)/B =
      A/B*((Fintype.card I : ℝ)-1)+A₀/B := by ring
  rw [he] at hh
  linarith

/-- A nonnegative coherent ratio cannot isolate its monotone top corner. -/
theorem affine_corner_ratio_le {I : Type*} [Fintype I] [DecidableEq I]
    (a₀ b₀ : ℝ) (a beta : I → ℝ) (hb₀ : 0 < b₀)
    (hbeta : ∀ i, 0 ≤ beta i) (ha₀ : 0 ≤ a₀)
    (ha : ∀ s : Finset I, 0 ≤ a₀+∑ i ∈ s, a i)
    (hcard : 2 ≤ Fintype.card I) :
    (a₀+∑ i, a i)/(b₀+∑ i, beta i) ≤
      (∑ i, (a₀+∑ j ∈ univ.erase i, a j)/(b₀+∑ j ∈ univ.erase i, beta j))/
        ((Fintype.card I : ℝ)-1) := by
  classical
  apply corner_ratio_le (a₀+∑ i, a i) (b₀+∑ i, beta i) a₀
    (fun i => a₀+∑ j ∈ univ.erase i, a j)
    (fun i => b₀+∑ j ∈ univ.erase i, beta j)
  · exact add_pos_of_pos_of_nonneg hb₀ (sum_nonneg fun i _ => hbeta i)
  · exact ha₀
  · exact fun i => ha _
  · intro i
    constructor
    · exact add_pos_of_pos_of_nonneg hb₀ (sum_nonneg fun j _ => hbeta j)
    · have hh := sum_erase_add univ beta (mem_univ i)
      have hi := hbeta i
      linarith
  · exact hcard
  · have he (i : I) : a₀+∑ j ∈ univ.erase i, a j = (a₀+∑ j, a j)-a i := by
      have hh := sum_erase_add univ a (mem_univ i)
      linarith
    simp_rw [he]
    rw [sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    ring

/-- Combining the two orientations gives a dimension-independent error gap.
Here all heads, and any bias represented as an extra constant head, are
nonnegative. The rows are the target, its down-neighbors and up-neighbors. -/
theorem approximation_error_ge {H I J : Type*} [Fintype H] [Fintype I] [Fintype J]
    (v : H → ℝ) (down : H → I → ℝ) (up : H → J → ℝ) (e : ℝ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    (hd : ∀ h i, 0 ≤ down h i) (hu : ∀ h j, 0 ≤ up h j)
    (hhead : ∀ h, v h ≤ (∑ i, down h i)/((Fintype.card I : ℝ)-1) ∨
      v h ≤ (∑ j, up h j)/((Fintype.card J : ℝ)-1))
    (htarget : 1-e ≤ ∑ h, v h)
    (hdown : ∀ i, ∑ h, down h i ≤ e)
    (hup : ∀ j, ∑ h, up h j ≤ e) : (1 : ℝ)/5 ≤ e := by
  have hIr : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hI
  have hJr : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hIp : (0 : ℝ) < (Fintype.card I : ℝ)-1 := by linarith
  have hJp : (0 : ℝ) < (Fintype.card J : ℝ)-1 := by linarith
  have he : 0 ≤ e := by
    have hi : Nonempty I := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i⟩ := hi
    exact (sum_nonneg fun h _ => hd h i).trans (hdown i)
  have htotal : ∑ h, v h ≤
      (∑ h, ∑ i, down h i)/((Fintype.card I : ℝ)-1)+
      (∑ h, ∑ j, up h j)/((Fintype.card J : ℝ)-1) := by
    rw [sum_div, sum_div, ← sum_add_distrib]
    apply sum_le_sum
    intro h _
    have hd0 : 0 ≤ (∑ i, down h i)/((Fintype.card I : ℝ)-1) :=
      div_nonneg (sum_nonneg fun i _ => hd h i) hIp.le
    have hu0 : 0 ≤ (∑ j, up h j)/((Fintype.card J : ℝ)-1) :=
      div_nonneg (sum_nonneg fun j _ => hu h j) hJp.le
    rcases hhead h with hh|hh <;> linarith
  have hds : (∑ h, ∑ i, down h i) ≤ (Fintype.card I : ℝ)*e := by
    rw [sum_comm]
    exact (sum_le_sum fun i _ => hdown i).trans_eq (by simp)
  have hus : (∑ h, ∑ j, up h j) ≤ (Fintype.card J : ℝ)*e := by
    rw [sum_comm]
    exact (sum_le_sum fun j _ => hup j).trans_eq (by simp)
  have hd2 : (∑ h, ∑ i, down h i)/((Fintype.card I : ℝ)-1) ≤ 2*e := by
    apply (div_le_iff₀ hIp).mpr
    exact hds.trans (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (Fintype.card I:ℝ)-2) he])
  have hu2 : (∑ h, ∑ j, up h j)/((Fintype.card J : ℝ)-1) ≤ 2*e := by
    apply (div_le_iff₀ hJp).mpr
    exact hus.trans (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (Fintype.card J:ℝ)-2) he])
  linarith

end HeadComplexity.NonnegativeHeadCone
