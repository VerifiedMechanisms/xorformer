import HeadComplexity.Results.AffineStatisticSignChanges
import HeadComplexity.Results.PositiveProjection
import Mathlib.Order.Fin.Tuple

set_option linter.style.header false

/-!
# Positive lexicographic multigrids

Finite positive block-statistic grids have a scale-separated positive
projection whose increasing image has exactly the lexicographic grid order.
This module packages that construction, its restriction lower bounds, and the
minimum multigrid cost for a fixed unordered coordinate partition.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

private theorem exists_positive_lex_weights :
    ∀ d : ℕ, ∀ {α : Type*} [Fintype α]
      (v : α → Fin d → ℝ) (R : α → α → Prop),
      (∀ x y, R x y → Pi.Lex (· < ·) (· < ·) (v x) (v y)) →
      ∃ K : Fin d → ℝ, (∀ j, 0 < K j) ∧
        ∀ x y, R x y → (∑ j, K j * v x j) < ∑ j, K j * v y j := by
  intro d
  induction d with
  | zero =>
      intro α _ v R hlex
      refine ⟨(Fin.elim0 : Fin 0 → ℝ), (fun j ↦ Fin.elim0 j), ?_⟩
      intro x y hxy
      obtain ⟨j, -⟩ := hlex x y hxy
      exact Fin.elim0 j
  | succ d ih =>
      intro α _ v R hlex
      classical
      let tail : α → Fin d → ℝ := fun x j ↦ v x j.succ
      let Rtail : α → α → Prop := fun x y ↦ R x y ∧ v x 0 = v y 0
      have htaillex : ∀ x y, Rtail x y →
          Pi.Lex (· < ·) (· < ·) (tail x) (tail y) := by
        intro x y hxy
        have h := hlex x y hxy.1
        rw [← Fin.cons_self_tail (v x), ← Fin.cons_self_tail (v y),
          Fin.pi_lex_lt_cons_cons] at h
        obtain ⟨j, hprev, hj⟩ :=
          (h.resolve_left (fun hlt ↦ (ne_of_lt hlt) hxy.2)).2
        exact ⟨j, hprev, hj⟩
      obtain ⟨Ktail, hKtail, htail⟩ := ih tail Rtail htaillex
      let tailScore : α → ℝ := fun x ↦ ∑ j, Ktail j * tail x j
      let S : Finset (α × α) := Finset.univ.filter fun p ↦
        R p.1 p.2 ∧ v p.1 0 < v p.2 0
      let ratio : α × α → ℝ := fun p ↦
        (tailScore p.1 - tailScore p.2) / (v p.2 0 - v p.1 0)
      let Kzero : ℝ := 1 + ∑ p ∈ S, max 0 (ratio p)
      let K : Fin (d + 1) → ℝ := Fin.cons Kzero Ktail
      have hKzero : 0 < Kzero := by
        dsimp [Kzero]
        have hnonneg : 0 ≤ ∑ p ∈ S, max 0 (ratio p) := by positivity
        linarith
      refine ⟨K, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · simpa [K] using hKzero
        · simpa [K] using hKtail k
      · intro x y hxy
        have hlexxy := hlex x y hxy
        rw [← Fin.cons_self_tail (v x), ← Fin.cons_self_tail (v y),
          Fin.pi_lex_lt_cons_cons] at hlexxy
        have hsumx : (∑ j, K j * v x j) = Kzero * v x 0 + tailScore x := by
          rw [Fin.sum_univ_succ]
          rfl
        have hsumy : (∑ j, K j * v y j) = Kzero * v y 0 + tailScore y := by
          rw [Fin.sum_univ_succ]
          rfl
        rw [hsumx, hsumy]
        rcases hlexxy with hfirst | ⟨hfirst, htailxy⟩
        · have hmem : (x, y) ∈ S := by
            simp [S, hxy, hfirst]
          have hterm_nonneg : ∀ p ∈ S, 0 ≤ max 0 (ratio p) := by
            intro p hp
            exact le_max_left _ _
          have hratio_le_sum : ratio (x, y) ≤ ∑ p ∈ S, max 0 (ratio p) := by
            calc
              ratio (x, y) ≤ max 0 (ratio (x, y)) := le_max_right _ _
              _ ≤ ∑ p ∈ S, max 0 (ratio p) :=
                Finset.single_le_sum hterm_nonneg hmem
          have hratio_lt : ratio (x, y) < Kzero := by
            dsimp [Kzero]
            linarith
          have hgap : 0 < v y 0 - v x 0 := sub_pos.mpr hfirst
          have hdom : tailScore x - tailScore y <
              Kzero * (v y 0 - v x 0) := by
            rw [show tailScore x - tailScore y =
              ratio (x, y) * (v y 0 - v x 0) by
                dsimp [ratio]
                field_simp]
            exact mul_lt_mul_of_pos_right hratio_lt hgap
          linarith
        · have htailstrict : tailScore x < tailScore y :=
            htail x y ⟨hxy, hfirst⟩
          rw [hfirst]
          linarith

/-- The vector of positive block statistics determined by a coordinate
partition map. -/
noncomputable def positiveBlockStatistic {n b : ℕ}
    (block : Fin n → Fin b) (lam : Fin n → ℝ)
    (bits : Fin n → Bool) (j : Fin b) : ℝ :=
  ∑ i, if block i = j then lam i * boolToReal (bits i) else 0

theorem positiveBlockStatistic_permute {n b : ℕ}
    (block : Fin n → Fin b) (lam : Fin n → ℝ)
    (sigma : Equiv.Perm (Fin n)) (bits : Fin n → Bool) :
    positiveBlockStatistic (fun i ↦ block (sigma.symm i))
        (fun i ↦ lam (sigma.symm i)) bits =
      positiveBlockStatistic block lam (permuteBits sigma bits) := by
  funext j
  unfold positiveBlockStatistic
  simpa [permuteBits] using
    (Equiv.sum_comp sigma.symm (fun i ↦
      if block i = j then lam i * boolToReal (bits (sigma i)) else 0))

private theorem weighted_blockStatistic_sum {n b : ℕ}
    (block : Fin n → Fin b) (lam : Fin n → ℝ)
    (K : Fin b → ℝ) (bits : Fin n → Bool) :
    (∑ j, K j * positiveBlockStatistic block lam bits j) =
      wT (fun i ↦ K (block i) * lam i) bits := by
  classical
  unfold positiveBlockStatistic wT
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_ite, mul_zero]
  cases bits i <;> simp [boolToReal]

/-- A positive multigrid together with its complete lexicographically ordered
finite image and Boolean labels. -/
structure PositiveLexMultigrid {n b : ℕ}
    (f : (Fin n → Bool) → Bool) where
  block : Fin n → Fin b
  lam : Fin n → ℝ
  lam_pos : ∀ i, 0 < lam i
  steps : ℕ
  node : Fin (steps + 1) → Fin b → ℝ
  node_strictLex : StrictMono (fun i ↦ toLex (node i))
  label : Fin (steps + 1) → Bool
  realized : ∀ i, ∃ bits, node i = positiveBlockStatistic block lam bits
  covers : ∀ bits, ∃ i, node i = positiveBlockStatistic block lam bits
  agrees : ∀ bits i,
    node i = positiveBlockStatistic block lam bits → f bits = label i

namespace PositiveLexMultigrid

variable {n b : ℕ} {f : (Fin n → Bool) → Bool}

def profile (C : PositiveLexMultigrid (b := b) f) : ℕ → Bool := fun k ↦
  if hk : k ≤ C.steps then C.label (orderedNodeIndex C.steps k hk) else false

@[simp] theorem profile_at (C : PositiveLexMultigrid (b := b) f)
    (i : Fin (C.steps + 1)) : C.profile i = C.label i := by
  rw [profile, dif_pos (Nat.lt_succ_iff.mp i.isLt)]
  congr

def alternations (C : PositiveLexMultigrid (b := b) f) : ℕ :=
  signChanges C.steps C.profile

/-- A factorization through positive block statistics has a canonical
lexicographically ordered multigrid certificate. -/
theorem exists_of_factorization
    (block : Fin n → Fin b) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (G : (Fin b → ℝ) → Bool)
    (hf : ∀ bits, f bits = G (positiveBlockStatistic block lam bits)) :
    ∃ C : PositiveLexMultigrid (b := b) f,
      C.block = block ∧ C.lam = lam := by
  classical
  let S : Finset (Lex (Fin b → ℝ)) :=
    Finset.univ.image (fun bits ↦ toLex (positiveBlockStatistic block lam bits))
  have hS : S.Nonempty := by
    exact ⟨toLex (positiveBlockStatistic block lam (fun _ ↦ false)),
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hcard : S.card - 1 + 1 = S.card :=
    Nat.sub_add_cancel (Finset.card_pos.mpr hS)
  let e : Fin (S.card - 1 + 1) ≃o Fin S.card := Fin.castOrderIso hcard
  let nodes : Fin (S.card - 1 + 1) → Fin b → ℝ :=
    fun i ↦ ofLex (S.orderEmbOfFin rfl (e i))
  let C : PositiveLexMultigrid (b := b) f :=
    { block := block
      lam := lam
      lam_pos := hlam
      steps := S.card - 1
      node := nodes
      node_strictLex := by
        intro i j hij
        change S.orderEmbOfFin rfl (e i) < S.orderEmbOfFin rfl (e j)
        exact (S.orderEmbOfFin rfl).strictMono (e.strictMono hij)
      label := fun i ↦ G (nodes i)
      realized := by
        intro i
        have hiS : toLex (nodes i) ∈ S := by
          change S.orderEmbOfFin rfl (e i) ∈ S
          exact S.orderEmbOfFin_mem rfl (e i)
        change toLex (nodes i) ∈
          Finset.univ.image
            (fun bits ↦ toLex (positiveBlockStatistic block lam bits)) at hiS
        rw [Finset.mem_image] at hiS
        obtain ⟨bits, -, hbits⟩ := hiS
        exact ⟨bits, congrArg ofLex hbits.symm⟩
      covers := by
        intro bits
        have hmem : toLex (positiveBlockStatistic block lam bits) ∈ S :=
          Finset.mem_image_of_mem _ (Finset.mem_univ bits)
        let j : Fin S.card :=
          (S.orderIsoOfFin rfl).symm
            ⟨toLex (positiveBlockStatistic block lam bits), hmem⟩
        refine ⟨e.symm j, ?_⟩
        apply funext
        intro k
        change ofLex (S.orderEmbOfFin rfl (e (e.symm j))) k = _
        rw [e.apply_symm_apply]
        have hj := congrArg Subtype.val
          ((S.orderIsoOfFin rfl).apply_symm_apply
            ⟨toLex (positiveBlockStatistic block lam bits), hmem⟩)
        exact congrFun (congrArg ofLex hj) k
      agrees := by
        intro bits i hi
        rw [hf bits, hi] }
  exact ⟨C, rfl, rfl⟩

/-- The scale-separation argument: every finite lexicographic multigrid path
is the increasing image of one positive statistic on all input variables. -/
noncomputable def toPositiveProjection
    (C : PositiveLexMultigrid (b := b) f) : PositiveProjection f := by
  classical
  let hscale := exists_positive_lex_weights b C.node (· < ·)
    (fun x y hxy ↦ C.node_strictLex hxy)
  let K : Fin b → ℝ := Classical.choose hscale
  have hKpos : ∀ j, 0 < K j := (Classical.choose_spec hscale).1
  have hKmono : ∀ x y, x < y →
      (∑ j, K j * C.node x j) < ∑ j, K j * C.node y j :=
    (Classical.choose_spec hscale).2
  let combinedLam : Fin n → ℝ := fun i ↦ K (C.block i) * C.lam i
  let combinedNode : Fin (C.steps + 1) → ℝ :=
    fun q ↦ ∑ j, K j * C.node q j
  exact
    { lam := combinedLam
      lam_pos := fun i ↦ mul_pos (hKpos (C.block i)) (C.lam_pos i)
      steps := C.steps
      node := combinedNode
      node_strictMono := fun _ _ hxy ↦ hKmono _ _ hxy
      label := C.label
      realized := by
        intro q
        obtain ⟨bits, hbits⟩ := C.realized q
        refine ⟨bits, ?_⟩
        dsimp [combinedNode, combinedLam]
        rw [hbits, weighted_blockStatistic_sum]
      covers := by
        intro bits
        obtain ⟨q, hq⟩ := C.covers bits
        refine ⟨q, ?_⟩
        dsimp [combinedNode, combinedLam]
        rw [hq, weighted_blockStatistic_sum]
      agrees := by
        intro bits q hq
        -- Both vectors occur in the complete path, while the combined scalar
        -- equality forces their path indices to coincide.
        obtain ⟨r, hr⟩ := C.covers bits
        have hscalar : (∑ j, K j * C.node q j) =
            ∑ j, K j * C.node r j := by
          rw [hr, weighted_blockStatistic_sum]
          exact hq
        have hqr : q = r := by
          rcases lt_trichotomy q r with hlt | heq | hgt
          · exact (ne_of_lt (hKmono q r hlt) hscalar).elim
          · exact heq
          · exact (ne_of_lt (hKmono r q hgt) hscalar.symm).elim
        subst r
        exact C.agrees bits q hr }

theorem toPositiveProjection_alternations
    (C : PositiveLexMultigrid (b := b) f) :
    C.toPositiveProjection.alternations = C.alternations := by
  rfl

/-- **Positive lexicographic multigrid upper bound.** -/
theorem HStar_le_alternations (C : PositiveLexMultigrid (b := b) f) :
    HStar n f ≤ C.alternations := by
  rw [← C.toPositiveProjection_alternations]
  exact HStar_le_of_computableWithHeadsN
    (PositiveWeightedSignDegLE.computable
      ⟨C.toPositiveProjection.lam, C.toPositiveProjection.lam_pos,
        C.toPositiveProjection.univariateThresholdDegLE⟩)

/-- Every lexicographic multigrid certificate also upper-bounds the optimized
positive-projection change count. -/
theorem positiveProjectionSignChanges_le_alternations
    (C : PositiveLexMultigrid (b := b) f) :
    positiveProjectionSignChanges f ≤ C.alternations := by
  apply positiveProjectionSignChanges_le
  exact ⟨C.toPositiveProjection, C.toPositiveProjection_alternations.le⟩

/-- Matching threshold degree and lexicographic multigrid cost determine head
complexity exactly. -/
theorem HStar_eq_of_thresholdDeg_eq_alternations
    (C : PositiveLexMultigrid (b := b) f)
    (h : thresholdDeg f = C.alternations) :
    HStar n f = thresholdDeg f := by
  apply le_antisymm
  · rw [h]
    exact C.HStar_le_alternations
  · exact thresholdDeg_le_HStar f

/-- Coordinates belonging to one block of a multigrid certificate. -/
noncomputable def blockSet (C : PositiveLexMultigrid (b := b) f)
    (j : Fin b) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ C.block i = j

/-- The canonical enumeration of the coordinates in one block. -/
noncomputable def blockEmbedding (C : PositiveLexMultigrid (b := b) f)
    (j : Fin b) : Fin (C.blockSet j).card ↪ Fin n where
  toFun i := ((C.blockSet j).equivFin.symm i).1
  inj' := by
    intro i k hik
    apply (C.blockSet j).equivFin.symm.injective
    exact Subtype.ext hik

/-- The coordinate face obtained by freeing one block and fixing all other
coordinates to a supplied assignment. -/
noncomputable def blockFace (C : PositiveLexMultigrid (b := b) f)
    (j : Fin b) (base : Fin n → Bool) : CoordFace (C.blockSet j).card n where
  free := C.blockEmbedding j
  base := base

/-- A one-block fiber of a multigrid-factorized Boolean function. -/
noncomputable def fiber (C : PositiveLexMultigrid (b := b) f)
    (j : Fin b) (base : Fin n → Bool) :
    (Fin (C.blockSet j).card → Bool) → Bool :=
  fun bits ↦ f ((C.blockFace j base).apply bits)

/-- Every one-block fiber supplies a restriction lower bound. -/
theorem HStar_fiber_le (C : PositiveLexMultigrid (b := b) f)
    (j : Fin b) (base : Fin n → Bool) :
    HStar (C.blockSet j).card (C.fiber j base) ≤ HStar n f := by
  exact HStar_restrict_le (C.blockFace j base) f

/-- Every ordered partition map admits a multigrid certificate for every
Boolean function. Binary weights make the vector of block statistics
injective. -/
theorem exists_for_block (block : Fin n → Fin b) :
    ∃ C : PositiveLexMultigrid (b := b) f, C.block = block := by
  classical
  let lam : Fin n → ℝ := fun i ↦ (2 : ℝ) ^ (i : ℕ)
  have hlam : ∀ i, 0 < lam i := by
    intro i
    dsimp [lam]
    positivity
  let stats : (Fin n → Bool) → (Fin b → ℝ) :=
    positiveBlockStatistic block lam
  have hinj : Function.Injective stats := by
    intro x y hxy
    apply wT_two_pow_injective
    have hx := weighted_blockStatistic_sum block lam (fun _ ↦ 1) x
    have hy := weighted_blockStatistic_sum block lam (fun _ ↦ 1) y
    have hsums : (∑ j, stats x j) = ∑ j, stats y j := by rw [hxy]
    have hx' : (∑ j, stats x j) = wT lam x := by
      simpa [stats] using hx
    have hy' : (∑ j, stats y j) = wT lam y := by
      simpa [stats] using hy
    exact hx'.symm.trans (hsums.trans hy')
  let G : (Fin b → ℝ) → Bool := f ∘ Function.invFun stats
  have hf : ∀ bits, f bits = G (stats bits) := by
    intro bits
    change f bits = f (Function.invFun stats (stats bits))
    rw [Function.leftInverse_invFun hinj bits]
  obtain ⟨C, hblock, -⟩ :=
    exists_of_factorization block lam hlam G (by simpa [stats] using hf)
  exact ⟨C, hblock⟩

/-- Complement a multigrid certificate without changing its geometry. -/
def complement (C : PositiveLexMultigrid (b := b) f) :
    PositiveLexMultigrid (b := b) (complementFn f) where
  block := C.block
  lam := C.lam
  lam_pos := C.lam_pos
  steps := C.steps
  node := C.node
  node_strictLex := C.node_strictLex
  label := fun i ↦ !(C.label i)
  realized := C.realized
  covers := C.covers
  agrees := by
    intro bits i hi
    simp only [complementFn]
    rw [C.agrees bits i hi]

@[simp] theorem complement_alternations
    (C : PositiveLexMultigrid (b := b) f) :
    C.complement.alternations = C.alternations := by
  unfold alternations signChanges
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases ht : t < C.steps
  · have ht0 : t ≤ C.steps := Nat.le_of_lt ht
    have ht1 : t + 1 ≤ C.steps := by omega
    simp [complement, profile, ht, ht0, ht1]
  · constructor
    · intro h
      exact (ht h.1).elim
    · intro h
      exact (ht h.1).elim

/-- Transport a multigrid certificate through a permutation of input
coordinates. -/
def permute (C : PositiveLexMultigrid (b := b) f)
    (sigma : Equiv.Perm (Fin n)) :
    PositiveLexMultigrid (b := b) (fun bits ↦ f (permuteBits sigma bits)) where
  block := fun i ↦ C.block (sigma.symm i)
  lam := fun i ↦ C.lam (sigma.symm i)
  lam_pos := fun i ↦ C.lam_pos (sigma.symm i)
  steps := C.steps
  node := C.node
  node_strictLex := C.node_strictLex
  label := C.label
  realized := by
    intro i
    obtain ⟨bits, hbits⟩ := C.realized i
    refine ⟨permuteBits sigma.symm bits, ?_⟩
    rw [positiveBlockStatistic_permute]
    rw [show permuteBits sigma (permuteBits sigma.symm bits) = bits by
      funext k
      simp [permuteBits]]
    exact hbits
  covers := by
    intro bits
    obtain ⟨i, hi⟩ := C.covers (permuteBits sigma bits)
    exact ⟨i, by rwa [positiveBlockStatistic_permute]⟩
  agrees := by
    intro bits i hi
    apply C.agrees (permuteBits sigma bits) i
    rwa [positiveBlockStatistic_permute] at hi

@[simp] theorem permute_alternations
    (C : PositiveLexMultigrid (b := b) f)
    (sigma : Equiv.Perm (Fin n)) :
    (C.permute sigma).alternations = C.alternations := rfl

end PositiveLexMultigrid

/-- Two ordered block maps represent the same partition when they differ only
by a relabeling of blocks. Thus minimizing over this relation also minimizes
over all block orders. -/
def SameBlockPartition {n b : ℕ} (block block' : Fin n → Fin b) : Prop :=
  ∃ pi : Equiv.Perm (Fin b), ∀ i, block' i = pi (block i)

theorem sameBlockPartition_refl {n b : ℕ} (block : Fin n → Fin b) :
    SameBlockPartition block block := by
  exact ⟨Equiv.refl _, fun _ ↦ rfl⟩

theorem sameBlockPartition_symm {n b : ℕ}
    {block block' : Fin n → Fin b}
    (h : SameBlockPartition block block') :
    SameBlockPartition block' block := by
  obtain ⟨pi, hpi⟩ := h
  refine ⟨pi.symm, fun i ↦ ?_⟩
  rw [hpi i, pi.symm_apply_apply]

theorem sameBlockPartition_trans {n b : ℕ}
    {block₁ block₂ block₃ : Fin n → Fin b}
    (h₁₂ : SameBlockPartition block₁ block₂)
    (h₂₃ : SameBlockPartition block₂ block₃) :
    SameBlockPartition block₁ block₃ := by
  obtain ⟨pi, hpi⟩ := h₁₂
  obtain ⟨tau, htau⟩ := h₂₃
  refine ⟨pi.trans tau, fun i ↦ ?_⟩
  rw [htau i, hpi i]
  rfl

/-- Bounded positive multigrid cost for a fixed unordered partition. -/
def PositiveMultigridCostLE {n b : ℕ} (block : Fin n → Fin b)
    (f : (Fin n → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ C : PositiveLexMultigrid (b := b) f,
    SameBlockPartition block C.block ∧ C.alternations ≤ K

theorem exists_positiveMultigridCostLE {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) :
    ∃ K, PositiveMultigridCostLE block f K := by
  obtain ⟨C, hC⟩ := PositiveLexMultigrid.exists_for_block (f := f) block
  exact ⟨C.alternations, C, hC ▸ sameBlockPartition_refl block, le_rfl⟩

/-- The minimum lexicographic positive multigrid cost over all positive block
statistics and all orders of the fixed partition. -/
noncomputable def positiveMultigridCost {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_positiveMultigridCostLE block f)

theorem positiveMultigridCost_spec {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) :
    PositiveMultigridCostLE block f (positiveMultigridCost block f) := by
  classical
  exact Nat.find_spec (exists_positiveMultigridCostLE block f)

theorem positiveMultigridCost_le {n b K : ℕ}
    {block : Fin n → Fin b} {f : (Fin n → Bool) → Bool}
    (h : PositiveMultigridCostLE block f K) :
    positiveMultigridCost block f ≤ K := by
  classical
  exact Nat.find_min' (exists_positiveMultigridCostLE block f) h

/-- The bounded cost predicate depends only on the unordered partition. -/
theorem positiveMultigridCostLE_congr_partition {n b K : ℕ}
    {block block' : Fin n → Fin b} {f : (Fin n → Bool) → Bool}
    (hpart : SameBlockPartition block block') :
    PositiveMultigridCostLE block f K ↔
      PositiveMultigridCostLE block' f K := by
  constructor
  · rintro ⟨C, hC, hcost⟩
    exact ⟨C, sameBlockPartition_trans (sameBlockPartition_symm hpart) hC, hcost⟩
  · rintro ⟨C, hC, hcost⟩
    exact ⟨C, sameBlockPartition_trans hpart hC, hcost⟩

/-- Relabeling the blocks leaves positive multigrid cost unchanged. -/
theorem positiveMultigridCost_congr_partition {n b : ℕ}
    {block block' : Fin n → Fin b} {f : (Fin n → Bool) → Bool}
    (hpart : SameBlockPartition block block') :
    positiveMultigridCost block f = positiveMultigridCost block' f := by
  apply Nat.le_antisymm
  · apply positiveMultigridCost_le
    exact (positiveMultigridCostLE_congr_partition hpart).2
      (positiveMultigridCost_spec block' f)
  · apply positiveMultigridCost_le
    exact (positiveMultigridCostLE_congr_partition hpart).1
      (positiveMultigridCost_spec block f)

/-- Coordinate permutation transports every feasible multigrid certificate
and its cost. -/
theorem positiveMultigridCostLE_permute {n b K : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool)
    (sigma : Equiv.Perm (Fin n))
    (h : PositiveMultigridCostLE block f K) :
    PositiveMultigridCostLE (fun i ↦ block (sigma.symm i))
      (fun bits ↦ f (permuteBits sigma bits)) K := by
  obtain ⟨C, ⟨pi, hpi⟩, hcost⟩ := h
  refine ⟨C.permute sigma, ⟨pi, fun i ↦ ?_⟩, ?_⟩
  · exact hpi (sigma.symm i)
  · simpa using hcost

theorem positiveMultigridCostLE_permute_iff {n b K : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool)
    (sigma : Equiv.Perm (Fin n)) :
    PositiveMultigridCostLE (fun i ↦ block (sigma.symm i))
        (fun bits ↦ f (permuteBits sigma bits)) K ↔
      PositiveMultigridCostLE block f K := by
  constructor
  · intro h
    have h' := positiveMultigridCostLE_permute
      (fun i ↦ block (sigma.symm i))
      (fun bits ↦ f (permuteBits sigma bits)) sigma.symm h
    have hblock :
        (fun i ↦ block (sigma.symm (sigma.symm.symm i))) = block := by
      funext i
      simp
    have hfun :
        (fun bits ↦ f
          (permuteBits sigma (permuteBits sigma.symm bits))) = f := by
      funext bits
      congr 1
      funext i
      simp [permuteBits]
    rw [hblock, hfun] at h'
    exact h'
  · exact positiveMultigridCostLE_permute block f sigma

/-- Positive multigrid cost is invariant under simultaneous coordinate
permutation of the function and its partition. -/
theorem positiveMultigridCost_permute {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool)
    (sigma : Equiv.Perm (Fin n)) :
    positiveMultigridCost (fun i ↦ block (sigma.symm i))
        (fun bits ↦ f (permuteBits sigma bits)) =
      positiveMultigridCost block f := by
  apply Nat.le_antisymm
  · apply positiveMultigridCost_le
    exact (positiveMultigridCostLE_permute_iff block f sigma).2
      (positiveMultigridCost_spec block f)
  · apply positiveMultigridCost_le
    exact (positiveMultigridCostLE_permute_iff block f sigma).1
      (positiveMultigridCost_spec
        (fun i ↦ block (sigma.symm i))
        (fun bits ↦ f (permuteBits sigma bits)))

/-- **Positive multigrid cost upper bound.** -/
theorem HStar_le_positiveMultigridCost {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ positiveMultigridCost block f := by
  obtain ⟨C, -, hcost⟩ := positiveMultigridCost_spec block f
  exact C.HStar_le_alternations.trans hcost

/-- The optimized positive-projection change count is bounded by multigrid
cost. -/
theorem positiveProjectionSignChanges_le_positiveMultigridCost {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) :
    positiveProjectionSignChanges f ≤ positiveMultigridCost block f := by
  obtain ⟨C, -, hcost⟩ := positiveMultigridCost_spec block f
  exact C.positiveProjectionSignChanges_le_alternations.trans hcost

/-- Matching threshold degree and multigrid cost determine head complexity
exactly. -/
theorem HStar_eq_of_thresholdDeg_eq_positiveMultigridCost {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool)
    (h : thresholdDeg f = positiveMultigridCost block f) :
    HStar n f = thresholdDeg f := by
  apply Nat.le_antisymm
  · rw [h]
    exact HStar_le_positiveMultigridCost block f
  · exact thresholdDeg_le_HStar f

/-- Output complement preserves every feasible multigrid cost bound. -/
theorem positiveMultigridCostLE_complement_iff {n b K : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) :
    PositiveMultigridCostLE block (complementFn f) K ↔
      PositiveMultigridCostLE block f K := by
  constructor
  · rintro ⟨C, hpart, hcost⟩
    rw [← complementFn_complementFn f]
    exact ⟨C.complement, hpart, by simpa using hcost⟩
  · rintro ⟨C, hpart, hcost⟩
    exact ⟨C.complement, hpart, by simpa using hcost⟩

/-- Positive multigrid cost is invariant under output complement. -/
theorem positiveMultigridCost_complement {n b : ℕ}
    (block : Fin n → Fin b) (f : (Fin n → Bool) → Bool) :
    positiveMultigridCost block (complementFn f) =
      positiveMultigridCost block f := by
  apply Nat.le_antisymm
  · apply positiveMultigridCost_le
    exact (positiveMultigridCostLE_complement_iff block f).2
      (positiveMultigridCost_spec block f)
  · apply positiveMultigridCost_le
    have h := (positiveMultigridCostLE_complement_iff block (complementFn f)).2
      (positiveMultigridCost_spec block (complementFn f))
    simpa using h

end HeadComplexity
