import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Finset.Sort

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.ScalarTokenDecoder
open Finset Polynomial
open scoped BigOperators

/-- Distinct strict polynomial sign words at ordered scalar tokens require at
least one polynomial root in every gap. -/
theorem ordered_words_le_sum_degrees {r m : ℕ}
    (p : Fin r → Polynomial ℝ) (t : Fin (m + 1) → ℝ)
    (ht : StrictMono t) (word : Fin (m + 1) → Fin r → Bool)
    (hw : Function.Injective word)
    (hs : ∀ j i, if word j i then 0 < (p i).eval (t j)
      else (p i).eval (t j) < 0) :
    m ≤ ∑ i, (p i).natDegree := by
  classical
  have hp (i : Fin r) : p i ≠ 0 := by
    intro hz
    have h := hs 0 i
    rw [hz] at h
    cases word 0 i <;> simp at h
  let Q : Polynomial ℝ := ∏ i, p i
  have hQ : Q ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgap (j : Fin m) : ∃ z : ℝ,
      t j.castSucc < z ∧ z < t j.succ ∧ Q.eval z = 0 := by
    have hword : word j.castSucc ≠ word j.succ := by
      intro h
      have := hw h
      exact (ne_of_lt j.castSucc_lt_succ) this
    have hi : ∃ i, word j.castSucc i ≠ word j.succ i := by
      by_contra hn
      push Not at hn
      exact hword (funext hn)
    obtain ⟨i, hi⟩ := hi
    have hleft := hs j.castSucc i
    have hright := hs j.succ i
    have hab := (ht j.castSucc_lt_succ).le
    have hz : ∃ z ∈ Set.Ioo (t j.castSucc) (t j.succ), (p i).eval z = 0 := by
      cases h0 : word j.castSucc i <;> cases h1 : word j.succ i
      · exact (hi (h0.trans h1.symm)).elim
      · have hl : (p i).eval (t j.castSucc) < 0 := by simpa [h0] using hleft
        have hr : 0 < (p i).eval (t j.succ) := by simpa [h1] using hright
        exact intermediate_value_Ioo hab (p i).continuous.continuousOn ⟨hl,hr⟩
      · have hl : 0 < (p i).eval (t j.castSucc) := by simpa [h0] using hleft
        have hr : (p i).eval (t j.succ) < 0 := by simpa [h1] using hright
        exact intermediate_value_Ioo' hab (p i).continuous.continuousOn ⟨hr,hl⟩
      · exact (hi (h0.trans h1.symm)).elim
    obtain ⟨z,hz,hzero⟩ := hz
    refine ⟨z,hz.1,hz.2,?_⟩
    simp only [Q, eval_prod]
    exact prod_eq_zero (mem_univ i) hzero
  choose z hzleft hzright hz using hgap
  have hzmono : StrictMono z := by
    intro i j hij
    have hle : i.succ ≤ j.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt hij
    exact (hzright i).trans_le ((ht.monotone hle).trans (hzleft j).le)
  have hdeg : m ≤ Q.natDegree := by
    by_contra hn
    have heq := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      Q hzmono.injective hz (by simpa using Nat.lt_of_not_ge hn)
    exact hQ heq
  exact hdeg.trans (Polynomial.natDegree_prod_le _ _)

/-- A scalar token that decodes every Boolean word in `r` bits requires total
numerator degree at least `2^r-1`, regardless of the token ordering. -/
theorem all_words_le_sum_degrees {r : ℕ} (p : Fin r → Polynomial ℝ)
    (hdecode : ∀ word : Fin r → Bool, ∃ t : ℝ, ∀ i,
      if word i then 0 < (p i).eval t else (p i).eval t < 0) :
    2 ^ r - 1 ≤ ∑ i, (p i).natDegree := by
  classical
  choose token htoken using hdecode
  have hinj : Function.Injective token := by
    intro f g hfg
    funext i
    have hf := htoken f i
    have hg := htoken g i
    rw [hfg] at hf
    cases hf' : f i <;> cases hg' : g i <;> simp_all
    all_goals linarith
  let s : Finset ℝ := univ.image token
  have hcard : s.card = 2 ^ r - 1 + 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by omega) _
    simp only [s, card_image_of_injective _ hinj, card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega
  let e := s.orderIsoOfFin hcard
  let t : Fin (2 ^ r - 1 + 1) → ℝ := fun j => (e j).val
  have ht : StrictMono t := by
    intro i j hij
    exact e.strictMono hij
  have hm (j : Fin (2 ^ r - 1 + 1)) : ∃ f : Fin r → Bool, token f = t j := by
    have := (e j).property
    rcases mem_image.mp this with ⟨f,_,hf⟩
    exact ⟨f,hf⟩
  choose word hword using hm
  have hw : Function.Injective word := by
    intro i j hij
    apply ht.injective
    rw [← hword i, ← hword j, hij]
  apply ordered_words_le_sum_degrees p t ht word hw
  intro j i
  simpa only [hword j] using htoken (word j) i

/-- If every bit decoder has degree at most `D`, at least `2^r-1` transitions
must fit into the `r*D` available roots. -/
theorem all_words_degree_bound {r D : ℕ} (p : Fin r → Polynomial ℝ)
    (hp : ∀ i, (p i).natDegree ≤ D)
    (hdecode : ∀ word : Fin r → Bool, ∃ t : ℝ, ∀ i,
      if word i then 0 < (p i).eval t else (p i).eval t < 0) :
    2 ^ r - 1 ≤ r * D := by
  exact (all_words_le_sum_degrees p hdecode).trans
    (by simpa using (sum_le_sum (s := Finset.univ) fun i _ => hp i))

/-- Clear the common positive affine poles of a scalar rational bit decoder. -/
def cleared {r H : ℕ} (den : Fin H → Polynomial ℝ)
    (num : Fin r → Fin H → Polynomial ℝ) (bias : Fin r → ℝ)
    (i : Fin r) : Polynomial ℝ :=
  C (bias i) * ∏ h, den h +
    ∑ h, num i h * ∏ g ∈ univ.erase h, den g

private theorem prod_degree_le_card {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial ℝ) (hp : ∀ i, (p i).natDegree ≤ 1) :
    (∏ i ∈ s, p i).natDegree ≤ s.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  simpa using (sum_le_sum (s := s) fun i _ => hp i)

theorem cleared_natDegree_le {r H : ℕ} (den : Fin H → Polynomial ℝ)
    (num : Fin r → Fin H → Polynomial ℝ) (bias : Fin r → ℝ)
    (hden : ∀ h, (den h).natDegree ≤ 1)
    (hnum : ∀ i h, (num i h).natDegree ≤ 1) (i : Fin r) :
    (cleared den num bias i).natDegree ≤ H := by
  classical
  unfold cleared
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    simp only [natDegree_C, zero_add]
    simpa using prod_degree_le_card univ den hden
  · apply natDegree_sum_le_of_forall_le
    intro h _
    refine natDegree_mul_le.trans ?_
    have hh := hnum i h
    have hp : (∏ g ∈ univ.erase h, den g).natDegree ≤ H - 1 := by
      simpa only [card_erase_of_mem (mem_univ h), card_fin] using
        prod_degree_le_card (univ.erase h) den hden
    have hH : 0 < H := Nat.zero_lt_of_lt h.isLt
    omega

theorem eval_cleared {r H : ℕ} (den : Fin H → Polynomial ℝ)
    (num : Fin r → Fin H → Polynomial ℝ) (bias : Fin r → ℝ)
    (t : ℝ) (hd : ∀ h, (den h).eval t ≠ 0) (i : Fin r) :
    (cleared den num bias i).eval t =
      (∏ h, (den h).eval t) *
        (bias i + ∑ h, (num i h).eval t / (den h).eval t) := by
  classical
  simp only [cleared, eval_add, eval_mul, eval_C, eval_prod, eval_finsetSum]
  rw [mul_add, mul_sum]
  congr 1
  · ring
  · apply sum_congr rfl
    intro h _
    rw [← mul_prod_erase univ (fun g => (den g).eval t) (mem_univ h)]
    field_simp [hd h]

/-- Arbitrary signed sums of `H` reciprocal affine poles cannot read all `r`-bit
words from one real token unless `r*H ≥ 2^r-1`. Only positivity at the selected
tokens is required; poles and affine numerators are otherwise arbitrary. -/
theorem reciprocal_decoder_bound {r H : ℕ} (den : Fin H → Polynomial ℝ)
    (num : Fin r → Fin H → Polynomial ℝ) (bias : Fin r → ℝ)
    (hden : ∀ h, (den h).natDegree ≤ 1)
    (hnum : ∀ i h, (num i h).natDegree ≤ 1)
    (hdecode : ∀ word : Fin r → Bool, ∃ t : ℝ,
      (∀ h, 0 < (den h).eval t) ∧ ∀ i,
      if word i then 0 < bias i + ∑ h, (num i h).eval t / (den h).eval t
      else bias i + ∑ h, (num i h).eval t / (den h).eval t < 0) :
    2 ^ r - 1 ≤ r * H := by
  apply all_words_degree_bound (cleared den num bias)
    (cleared_natDegree_le den num bias hden hnum)
  intro word
  obtain ⟨t,hd,hs⟩ := hdecode word
  refine ⟨t,fun i => ?_⟩
  rw [eval_cleared den num bias t (fun h => (hd h).ne') i]
  have hprod : 0 < ∏ h, (den h).eval t := prod_pos (fun h _ => hd h)
  have hi := hs i
  cases hw : word i <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at hi ⊢
  · exact mul_neg_of_pos_of_neg hprod hi
  · exact mul_pos hprod hi

/-- With selector-independent poles, affine selector numerators stay affine
regardless of how many reciprocal terms or signed cancellations are used. -/
def binarySelectorScore {H : ℕ} (den a u v : Fin H → ℝ) (bias : ℝ)
    (s t : ℝ) : ℝ := bias + ∑ h, (a h + u h * s + v h * t) / den h

theorem binarySelector_rectangle {H : ℕ} (den a u v : Fin H → ℝ) (bias : ℝ) :
    binarySelectorScore den a u v bias 0 0 +
      binarySelectorScore den a u v bias 1 1 =
    binarySelectorScore den a u v bias 0 1 +
      binarySelectorScore den a u v bias 1 0 := by
  unfold binarySelectorScore
  have hsum : (∑ h, (a h + u h * 0 + v h * 0) / den h) +
      (∑ h, (a h + u h * 1 + v h * 1) / den h) =
      (∑ h, (a h + u h * 0 + v h * 1) / den h) +
      (∑ h, (a h + u h * 1 + v h * 0) / den h) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    ring
  linarith

/-- Even two binary selector bits cannot read an arbitrary four-bit word when
all denominator values are selector independent. -/
theorem binarySelector_cannot_xor {H : ℕ} (den a u v : Fin H → ℝ) (bias : ℝ) :
    ¬ (binarySelectorScore den a u v bias 0 0 < 0 ∧
      0 < binarySelectorScore den a u v bias 0 1 ∧
      0 < binarySelectorScore den a u v bias 1 0 ∧
      binarySelectorScore den a u v bias 1 1 < 0) := by
  intro ⟨h00,h01,h10,h11⟩
  have h := binarySelector_rectangle den a u v bias
  linarith

end HeadComplexity.ScalarTokenDecoder
