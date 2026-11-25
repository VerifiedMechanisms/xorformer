import HeadComplexity.Atoms.RoPEGeneralRank
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie

/-!
# Formal directional derivatives of the arbitrary-head source

The source here uses independent denominator and numerator variables. This file
connects its formal second directional derivative to the pair-equation rank
criterion.
-/

noncomputable section

namespace HeadComplexity.RoPEGeneralDerivative

open MvPolynomial
open scoped BigOperators

variable {σ : Type*}

def directional (v : σ → ℝ) :
    Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ) :=
  MvPolynomial.mkDerivation ℝ (fun i => C (v i))

@[simp] theorem directional_X (v : σ → ℝ) (i : σ) :
    directional v (X i) = C (v i) := by
  simp [directional]

@[simp] theorem directional_C (v : σ → ℝ) (r : ℝ) :
    directional v (C r) = 0 := by
  exact derivation_C (directional v) r

theorem derivation_prod {ι : Type*} [DecidableEq ι]
    (δ : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    δ (∏ i ∈ s, f i) = ∑ i ∈ s, δ (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha]
    simp only [smul_eq_mul]
    rw [add_comm, mul_comm (∏ i ∈ s, f i), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := Ne.symm (ne_of_mem_of_not_mem hi ha)
    rw [Finset.erase_insert_of_ne hai, Finset.prod_insert]
    · ring
    · exact fun h => ha (Finset.mem_of_mem_erase h)

abbrev Var (H : ℕ) := Fin H ⊕ Fin H
abbrev Poly (H : ℕ) := MvPolynomial (Var H) ℝ

def D {H : ℕ} (i : Fin H) : Var H := Sum.inl i
def N {H : ℕ} (i : Fin H) : Var H := Sum.inr i

def denomProduct {H : ℕ} (s : Finset (Fin H)) : Poly H :=
  ∏ i ∈ s, X (D i)

def source (H : ℕ) : Poly H :=
  ∑ i : Fin H, X (N i) * denomProduct (Finset.univ.erase i)

def direction {H : ℕ} (d a : Fin H → ℝ) : Var H → ℝ :=
  Sum.elim d a

theorem directional_denomProduct {H : ℕ} (d a : Fin H → ℝ)
    (s : Finset (Fin H)) :
    directional (direction d a) (denomProduct s) =
      ∑ i ∈ s, C (d i) * denomProduct (s.erase i) := by
  unfold denomProduct
  rw [derivation_prod]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [directional_X, direction, D, Sum.elim_inl]

theorem directional_commute (v w : σ → ℝ) (P : MvPolynomial σ ℝ) :
    directional v (directional w P) = directional w (directional v P) := by
  have h : ⁅directional v, directional w⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp [Derivation.commutator_apply]
  have hP := congrArg (fun δ : Derivation ℝ (MvPolynomial σ ℝ)
    (MvPolynomial σ ℝ) => δ P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using hP

theorem directional_source {H : ℕ} (d a : Fin H → ℝ) :
    directional (direction d a) (source H) =
      ∑ i : Fin H, (X (N i) *
        (∑ k ∈ Finset.univ.erase i, C (d k) *
          denomProduct ((Finset.univ.erase i).erase k)) +
        denomProduct (Finset.univ.erase i) * C (a i)) := by
  unfold source
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Derivation.leibniz, directional_denomProduct]
  simp [direction, N]

theorem directional_num_source {H : ℕ} (b : Fin H → ℝ) :
    directional (direction 0 b) (source H) =
      ∑ i : Fin H, C (b i) * denomProduct (Finset.univ.erase i) := by
  rw [directional_source]
  simp [mul_comm]

theorem directional_single_num_source {H : ℕ} (i : Fin H) :
    directional (direction 0 (Pi.single i 1)) (source H) =
      denomProduct (Finset.univ.erase i) := by
  rw [directional_num_source]
  simp [Pi.single_apply]

def zeroPair {H : ℕ} (k l : Fin H) : Var H → ℝ :=
  Sum.elim (fun j => if j = k ∨ j = l then 0 else 1) (fun _ => 0)

theorem eval_zeroPair_denomProduct {H : ℕ} (k l : Fin H)
    (s : Finset (Fin H)) :
    eval (zeroPair k l) (denomProduct s) =
      if k ∉ s ∧ l ∉ s then 1 else 0 := by
  classical
  simp only [denomProduct, map_prod, eval_X, zeroPair, D, Sum.elim_inl]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro j hj
    split_ifs with hjkl
    · rcases hjkl with rfl | rfl
      · exact (h.1 hj).elim
      · exact (h.2 hj).elim
    · rfl
  · simp only [not_and_or, not_not] at h
    rcases h with hk | hl
    · exact Finset.prod_eq_zero hk (by simp)
    · exact Finset.prod_eq_zero hl (by simp)

theorem erased_pair_sum {H : ℕ} (e : Fin H → ℝ) (s : Finset (Fin H))
    {k l : Fin H} (hk : k ∈ s) (hl : l ∈ s) (hkl : k ≠ l)
    (j : Fin H) (hj : j ∈ s) :
    (∑ t ∈ s.erase j, e t *
      (if k ∉ (s.erase j).erase t ∧ l ∉ (s.erase j).erase t then 1 else 0)) =
      if j = k then e l else if j = l then e k else 0 := by
  by_cases hjk : j = k
  · subst j
    simp [Finset.mem_erase, hk, hl, Ne.symm hkl, mul_ite]
  · by_cases hjl : j = l
    · subst j
      simp [Finset.mem_erase, hk, hl, hkl, Ne.symm hkl, mul_ite]
    · rw [if_neg hjk, if_neg hjl]
      apply Finset.sum_eq_zero
      intro t ht
      have htest :
          ¬ (k ∉ (s.erase j).erase t ∧ l ∉ (s.erase j).erase t) := by
        intro h
        have hkt : k = t := by
          by_contra hkt
          exact h.1 (by simp [Finset.mem_erase, hkt, Ne.symm hjk, hk])
        have hlt : l = t := by
          by_contra hlt
          exact h.2 (by simp [Finset.mem_erase, hlt, Ne.symm hjl, hl])
        exact hkl (hkt.trans hlt.symm)
      rw [if_neg htest, mul_zero]

theorem eval_second_denomProduct {H : ℕ}
    (d a e b : Fin H → ℝ) (s : Finset (Fin H))
    {k l : Fin H} (hk : k ∈ s) (hl : l ∈ s) (hkl : k ≠ l) :
    eval (zeroPair k l)
      (directional (direction e b)
        (directional (direction d a) (denomProduct s))) =
      d k * e l + d l * e k := by
  rw [directional_denomProduct]
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, directional_C,
    mul_zero, add_zero, directional_denomProduct, map_mul, eval_C]
  simp only [eval_zeroPair_denomProduct]
  have inner := erased_pair_sum e s hk hl hkl
  have hsum :
      (∑ j ∈ s, d j *
        ∑ t ∈ s.erase j, e t *
          (if k ∉ (s.erase j).erase t ∧ l ∉ (s.erase j).erase t then 1 else 0)) =
      ∑ j ∈ s, d j * (if j = k then e l else if j = l then e k else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner j hj]
  rw [hsum]
  have hpoint (j : Fin H) :
      d j * (if j = k then e l else if j = l then e k else 0) =
        (if j = k then d k * e l else 0) +
          (if j = l then d l * e k else 0) := by
    by_cases hjk : j = k
    · subst j; simp [hkl]
    · by_cases hjl : j = l
      · subst j; simp [Ne.symm hkl]
      · simp [hjk, hjl]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp [hk, hl]

theorem pair_equations_first_of_second_zero {H : ℕ}
    (hH : 3 ≤ H) (d a e b : Fin H → ℝ)
    (hzero : directional (direction e b)
      (directional (direction d a) (source H)) = 0) :
    RoPEGeneralRank.PairEquations d e := by
  intro k l hkl
  have hex : ∃ i : Fin H, i ≠ k ∧ i ≠ l := by
    by_contra! h
    have hs : (Finset.univ : Finset (Fin H)) ⊆ {k, l} := by
      intro i hi
      by_cases hik : i = k
      · simp [hik]
      · simp [h i hik]
    have hc := Finset.card_le_card hs
    simp [Finset.card_pair hkl] at hc
    omega
  obtain ⟨i, hik, hil⟩ := hex
  have hi :
      directional (direction e b)
        (directional (direction d a)
          (denomProduct (Finset.univ.erase i))) = 0 := by
    rw [← directional_single_num_source i]
    rw [directional_commute (direction d a) (direction 0 (Pi.single i 1))]
    rw [directional_commute (direction e b) (direction 0 (Pi.single i 1))]
    rw [hzero, map_zero]
  have hev := congrArg (eval (zeroPair k l)) hi
  rw [eval_second_denomProduct d a e b (Finset.univ.erase i)
    (by simp [Ne.symm hik]) (by simp [Ne.symm hil]) hkl] at hev
  simpa using hev

theorem eval_first_erased_denomProduct {H : ℕ}
    (d a : Fin H → ℝ) (i : Fin H) {k l : Fin H} (hkl : k ≠ l) :
    eval (zeroPair k l)
      (directional (direction d a) (denomProduct (Finset.univ.erase i))) =
      if i = k then d l else if i = l then d k else 0 := by
  rw [directional_denomProduct]
  simp only [map_sum, map_mul, eval_C, eval_zeroPair_denomProduct]
  exact erased_pair_sum d Finset.univ (Finset.mem_univ k)
    (Finset.mem_univ l) hkl i (Finset.mem_univ i)

theorem pair_equations_second_of_second_zero {H : ℕ}
    (d a b : Fin H → ℝ)
    (hzero : directional (direction 0 b)
      (directional (direction d a) (source H)) = 0) :
    RoPEGeneralRank.PairEquations d b := by
  intro k l hkl
  rw [directional_commute (direction 0 b) (direction d a),
    directional_num_source] at hzero
  have hev := congrArg (eval (zeroPair k l)) hzero
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, directional_C,
    mul_zero, add_zero, map_mul, eval_C, map_zero] at hev
  simp_rw [eval_first_erased_denomProduct d a _ hkl] at hev
  have hpoint (j : Fin H) :
      b j * (if j = k then d l else if j = l then d k else 0) =
        (if j = k then b k * d l else 0) +
          (if j = l then b l * d k else 0) := by
    by_cases hjk : j = k
    · subst j; simp [hkl]
    · by_cases hjl : j = l
      · subst j; simp [Ne.symm hkl]
      · simp [hjk, hjl]
  simp_rw [hpoint] at hev
  rw [Finset.sum_add_distrib] at hev
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hev
  nlinarith

theorem directional_add (v w : σ → ℝ) :
    directional (v + w) = directional v + directional w := by
  apply MvPolynomial.derivation_ext
  intro i
  simp

theorem directional_smul (c : ℝ) (v : σ → ℝ) :
    directional (c • v) = c • directional v := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [MvPolynomial.C_mul']

theorem direction_add {H : ℕ} (e b e' b' : Fin H → ℝ) :
    direction (e + e') (b + b') = direction e b + direction e' b' := by
  funext i
  cases i <;> rfl

theorem direction_smul {H : ℕ} (c : ℝ) (e b : Fin H → ℝ) :
    direction (c • e) (c • b) = c • direction e b := by
  funext i
  cases i <;> rfl

/-- The flattening of the first formal directional derivative. -/
def secondMap {H : ℕ} (d a : Fin H → ℝ) :
    ((Fin H → ℝ) × (Fin H → ℝ)) →ₗ[ℝ] Poly H where
  toFun w := directional (direction w.1 w.2)
    (directional (direction d a) (source H))
  map_add' := by
    intro x y
    change directional (direction (x.1 + y.1) (x.2 + y.2)) _ = _
    rw [direction_add, directional_add]
    rfl
  map_smul' := by
    intro c x
    change directional (direction (c • x.1) (c • x.2)) _ = _
    rw [direction_smul, directional_smul]
    rfl

theorem secondMap_rank_lower_bound {H : ℕ} (hH : 3 ≤ H)
    (d a : Fin H → ℝ) {s : Fin H} (hs : d s ≠ 0) :
    2 * H ≤ Module.finrank ℝ (secondMap d a).range + 2 := by
  have he : ∀ w ∈ (secondMap d a).ker, RoPEGeneralRank.PairEquations d w.1 := by
    intro w hw
    exact pair_equations_first_of_second_zero hH d a w.1 w.2 hw
  have hb : ∀ w ∈ (secondMap d a).ker, w.1 = 0 →
      RoPEGeneralRank.PairEquations d w.2 := by
    intro w hw hfst
    apply pair_equations_second_of_second_zero d a w.2
    change directional (direction w.1 w.2)
      (directional (direction d a) (source H)) = 0 at hw
    simpa [hfst] using hw
  simpa using RoPEGeneralRank.twice_card_le_rank_add_two (secondMap d a) hs he hb

theorem secondMap_rank_gt_heads {H : ℕ} (hH : 3 ≤ H)
    (d a : Fin H → ℝ) {s : Fin H} (hs : d s ≠ 0) :
    H < Module.finrank ℝ (secondMap d a).range := by
  have h := secondMap_rank_lower_bound hH d a hs
  omega

theorem secondMap_zero_apply {H : ℕ} (a e b : Fin H → ℝ) :
    secondMap 0 a (e, b) = secondMap 0 a (e, 0) := by
  change directional (direction e b)
      (directional (direction 0 a) (source H)) =
    directional (direction e 0)
      (directional (direction 0 a) (source H))
  rw [directional_num_source]
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, directional_C,
    mul_zero, add_zero, directional_denomProduct]

theorem secondMap_zero_rank_le {H : ℕ} (a : Fin H → ℝ) :
    Module.finrank ℝ (secondMap 0 a).range ≤ H := by
  let T : (Fin H → ℝ) →ₗ[ℝ] Poly H :=
    (secondMap 0 a).comp (LinearMap.inl ℝ (Fin H → ℝ) (Fin H → ℝ))
  have hrange : (secondMap 0 a).range ≤ T.range := by
    rintro P ⟨⟨e, b⟩, rfl⟩
    refine ⟨e, ?_⟩
    exact (secondMap_zero_apply a e b).symm
  calc
    Module.finrank ℝ (secondMap 0 a).range ≤ Module.finrank ℝ T.range :=
      Submodule.finrank_mono hrange
    _ ≤ H := by simpa using T.finrank_range_le

/-- The low-rank locus of the source contraction is exactly its denominator kernel. -/
theorem secondMap_rank_le_iff {H : ℕ} (hH : 3 ≤ H)
    (d a : Fin H → ℝ) :
    Module.finrank ℝ (secondMap d a).range ≤ H ↔ d = 0 := by
  constructor
  · intro hle
    by_contra hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra! h
      exact hd (funext h)
    exact (not_lt_of_ge hle) (secondMap_rank_gt_heads hH d a hs)
  · rintro rfl
    exact secondMap_zero_rank_le a

end HeadComplexity.RoPEGeneralDerivative
