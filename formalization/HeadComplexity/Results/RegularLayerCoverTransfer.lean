import HeadComplexity.Results.SupportedGradedShellTransfer

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- Reindexing an approximating head family preserves its full-cube limit. -/
theorem HeadScoreClosure.reindex {n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {F : (Fin n → Bool) → ℝ} (hF : HeadScoreClosure n I F) (e : I ≃ J) :
    HeadScoreClosure n J F := by
  apply closure_mono (s := headScoreRange n I) (t := headScoreRange n J) ?_ hF
  rintro G ⟨φ, rfl⟩
  refine ⟨fun j ↦ φ (e.symm j), ?_⟩
  funext x
  exact e.symm.sum_comp (fun i ↦ (φ i).eval x)

theorem HeadScoreClosure.to_fin {n : ℕ} {I : Type*} [Fintype I]
    {F : (Fin n → Bool) → ℝ} (hF : HeadScoreClosure n I F) :
    HeadScoreClosure n (Fin (Fintype.card I)) F :=
  hF.reindex (Fintype.equivFin I)

theorem gradedSupport_injective {n : ℕ} :
    Function.Injective (gradedSupport (n := n)) := by
  intro x y h
  funext i
  have hm : x i = true ↔ y i = true := by
    simpa only [gradedSupport, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.ext_iff.mp h i)
  cases hx : x i <;> cases hy : y i <;> simp_all

theorem gradedSupport_mem_downset_self {n : ℕ} (x : Fin n → Bool) :
    x ∈ gradedDownset (gradedSupport x) := by
  simp [gradedDownset]

/-- A singleton exception on one layer needs one head. It can have nonzero
values below that layer, where subsequent modules will correct the score. -/
theorem exists_singleton_layer_closure {n : ℕ} (x : Fin n → Bool)
    (label : Bool) :
    ∃ F : (Fin n → Bool) → ℝ,
      HeadScoreClosure n (Fin 1) F ∧
      0 < outputSign label * F x ∧
      (∀ y, (gradedSupport x).card < (gradedSupport y).card → F y = 0) ∧
      (∀ y, (gradedSupport y).card = (gradedSupport x).card → y ≠ x → F y = 0) := by
  classical
  obtain ⟨L, hL⟩ := exists_reverseGradedData_depth_zero n label
  let F (y : Fin n → Bool) := if y ∈ gradedDownset (gradedSupport x) then
    L.score (centerDeletion (gradedCenter (gradedSupport x)) y) else 0
  refine ⟨F, L.centered_closure _, ?_, ?_, ?_⟩
  · simpa only [F, gradedSupport_mem_downset_self, ite_true] using
      hL (centerDeletion (gradedCenter (gradedSupport x)) x)
  · intro y hy
    have hn : y ∉ gradedDownset (gradedSupport x) := by
      intro h
      have hs := (Finset.mem_filter.mp h).2
      exact (not_le_of_gt hy) (Finset.card_le_card hs)
    simp [F, hn]
  · intro y hy hne
    have hn : y ∉ gradedDownset (gradedSupport x) := by
      intro h
      have hs := (Finset.mem_filter.mp h).2
      exact hne (gradedSupport_injective (Finset.eq_of_subset_of_card_le hs hy.ge))
    simp [F, hn]

/-- The Boolean points in a single weight layer. -/
def BoolWeightLayer (n k : ℕ) := {x : Fin n → Bool // (gradedSupport x).card = k}

instance (n k : ℕ) : Fintype (BoolWeightLayer n k) :=
  inferInstanceAs (Fintype {x : Fin n → Bool // (gradedSupport x).card = k})

/-- A layer compiler includes the support conditions needed by descending
assembly, in addition to strict signs on its intended cells. -/
def HasSupportedLayerCompiler (n k H : ℕ) (J : Type*) [Fintype J]
    (neighbors : BoolWeightLayer n k → Finset J) : Prop :=
  ∀ f : (Fin n → Bool) → Bool, ∃ F : J → (Fin n → Bool) → ℝ,
    (∀ j, HeadScoreClosure n (Fin H) (F j)) ∧
    (∀ j x, k < (gradedSupport x).card → F j x = 0) ∧
    (∀ j, ∀ x : BoolWeightLayer n k, j ∈ neighbors x →
      0 < outputSign (f x.val) * F j x.val) ∧
    (∀ j, ∀ x : BoolWeightLayer n k, j ∉ neighbors x → F j x.val = 0)

/-- Select a regular family of cells and pay one head for each exception.
No decoder capacity or support property is inferred from the cover itself. -/
theorem exists_supported_layer_score_log_gain {n k H d e : ℕ}
    {J : Type*} [Fintype J]
    (neighbors : BoolWeightLayer n k → Finset J)
    (hd : 0 < d) (he : 0 < e) (hH : 0 < H) (hgain : H ≤ e)
    (hdegree : ∀ x, (neighbors x).card = d)
    (hincidence : Fintype.card J * e = Fintype.card (BoolWeightLayer n k) * d)
    (hcompiler : HasSupportedLayerCompiler n k H J neighbors)
    (f : (Fin n → Bool) → Bool) :
    ∃ (L : ℕ) (F : (Fin n → Bool) → ℝ),
      HeadScoreClosure n (Fin L) F ∧
      (∀ x : BoolWeightLayer n k, 0 < outputSign (f x.val) * F x.val) ∧
      (∀ x, k < (gradedSupport x).card → F x = 0) ∧
      (L : ℝ) ≤ Fintype.card (BoolWeightLayer n k) * ((H : ℝ) / e) *
        (1 + Real.log ((e : ℝ) / H)) := by
  classical
  obtain ⟨S, T, hcover, hcost⟩ := jointCell_exists_regular_partial_cover_log_gain
    neighbors d e hd he hdegree hincidence H (Nat.cast_pos.mpr hH)
      (by exact_mod_cast hgain)
  obtain ⟨F, hF, hFhigh, hFpos, hFzero⟩ := hcompiler f
  have hex (x : ↥T) := exists_singleton_layer_closure x.val.val (f x.val.val)
  choose G hG hGpos hGhigh hGzero using hex
  let B := ↥S ⊕ ↥T
  let I : B → Type := fun j ↦ Fin (Sum.elim (fun _ ↦ H) (fun _ ↦ 1) j)
  let Q : B → (Fin n → Bool) → ℝ := Sum.elim (fun j ↦ F j.val) G
  let W (x : Fin n → Bool) := ∑ j : B, Q j x
  have hQ : ∀ j : B, HeadScoreClosure n (I j) (Q j) := by
    intro j
    cases j with
    | inl j => exact hF j.val
    | inr j => exact hG j
  have hW : HeadScoreClosure n ((j : B) × I j) W := by
    simpa only [one_mul] using HeadScoreClosure.sum Q (fun _ ↦ 1) hQ
  have hcount : Fintype.card ((j : B) × I j) = H * S.card + T.card := by
    simp [B, I, Fintype.card_sigma, Fintype.sum_sum_type, mul_comm]
  refine ⟨Fintype.card ((j : B) × I j), W, hW.to_fin, ?_, ?_, ?_⟩
  · intro x
    have hnonneg : ∀ j : B, 0 ≤ outputSign (f x.val) * Q j x.val := by
      intro j
      cases j with
      | inl j =>
          by_cases hj : j.val ∈ neighbors x
          · exact (hFpos j.val x hj).le
          · rw [show Q (Sum.inl j) x.val = 0 from hFzero j.val x hj]
            simp
      | inr j =>
          by_cases heq : x.val = j.val.val
          · simpa only [Q, Sum.elim_inr, heq] using (hGpos j).le
          · rw [show Q (Sum.inr j) x.val = 0 from
              hGzero j x.val (x.property.trans j.val.property.symm) heq]
            simp
    have hexpos : ∃ j : B, 0 < outputSign (f x.val) * Q j x.val := by
      by_cases hx : x ∈ T
      · exact ⟨Sum.inr ⟨x, hx⟩, hGpos ⟨x, hx⟩⟩
      · obtain ⟨j, hj, hnj⟩ := hcover x hx
        exact ⟨Sum.inl ⟨j, hj⟩, hFpos j x hnj⟩
    rw [show outputSign (f x.val) * W x.val =
      ∑ j : B, outputSign (f x.val) * Q j x.val by simp [W, Finset.mul_sum]]
    obtain ⟨j, hj⟩ := hexpos
    exact Finset.sum_pos' (fun j _ ↦ hnonneg j) ⟨j, Finset.mem_univ _, hj⟩
  · intro x hx
    apply Finset.sum_eq_zero
    intro j _
    cases j with
    | inl j => exact hFhigh j.val x hx
    | inr j => exact hGhigh j x (by simpa only [j.val.property] using hx)
  · rw [hcount]
    exact_mod_cast hcost

/-- Scores for all weight layers assemble in descending order. Each layer
may have arbitrary lower-layer values; vanishing on higher layers protects
every previously established strict sign. -/
theorem HStar_le_of_supported_layer_closures {n : ℕ}
    (H : Fin (n + 1) → ℕ) (F : Fin (n + 1) → (Fin n → Bool) → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hF : ∀ k, HeadScoreClosure n (Fin (H k)) (F k))
    (hpos : ∀ k, ∀ x : BoolWeightLayer n k.val,
      0 < outputSign (f x.val) * F k x.val)
    (hhigh : ∀ k x, k.val < (gradedSupport x).card → F k x = 0) :
    HStar n f ≤ ∑ k, H k := by
  classical
  let r (i : ℕ) : Fin (n + 1) := ⟨n - i, by omega⟩
  let P (i : ℕ) := Finset.univ.filter
    (fun x : Fin n → Bool ↦ (gradedSupport x).card = (r i).val)
  obtain ⟨φ, hφ⟩ := glue_headScoreClosure (n + 1) (fun i ↦ H (r i)) P
    (fun i ↦ F (r i)) (fun x ↦ outputSign (f x)) (fun i _ ↦ hF (r i))
    (by
      intro i hi x hx
      exact hpos (r i) ⟨x, (Finset.mem_filter.mp hx).2⟩)
    (by
      intro i hi j hj x hx
      have hrank := (Finset.mem_filter.mp hx).2
      have hlt : (r i).val < (gradedSupport x).card := by
        dsimp [r] at hrank ⊢
        omega
      rw [hhigh (r i) x hlt]
      simp)
  have hcover (x : Fin n → Bool) : ∃ i < n + 1, x ∈ P i := by
    have hx : (gradedSupport x).card ≤ n := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    refine ⟨n - (gradedSupport x).card, by omega, ?_⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [r]
    omega
  let I := ((i : Fin (n + 1)) × Fin (H (r i.val)))
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfrac : fracComputable n (Fintype.card I) f := by
    refine ⟨fun h ↦ φ (e h), 0, fun x ↦ ?_⟩
    have heq := e.sum_comp (fun h ↦ (φ h).eval x)
    have hs := (strict_of_outputSign (hφ x (hcover x))).1
    simpa only [zero_add, heq] using hs
  have hbound := HStar_le_of_computableWithHeadsN (computable_of_fracComputable hfrac)
  have hr (i : Fin (n + 1)) : r i.val = i.rev := by
    apply Fin.ext
    simp [r, Fin.rev]
  have hcount : Fintype.card I = ∑ k, H k := by
    simp only [I, Fintype.card_sigma, Fintype.card_fin, hr]
    exact Equiv.sum_comp Fin.revPerm H
  rwa [hcount] at hbound

/-- A complete conditional global bound from regular supported layer
compilers. Cell selection, all overlaps, singleton exceptions, and prior
signs are charged in the displayed sum. -/
theorem worstCaseHeadComplexity_real_le_regular_layer_log_gain {n : ℕ}
    (J : Fin (n + 1) → Type*) [∀ k, Fintype (J k)]
    (H d e : Fin (n + 1) → ℕ)
    (neighbors : (k : Fin (n + 1)) → BoolWeightLayer n k.val → Finset (J k))
    (hd : ∀ k, 0 < d k) (he : ∀ k, 0 < e k) (hH : ∀ k, 0 < H k)
    (hgain : ∀ k, H k ≤ e k)
    (hdegree : ∀ k x, (neighbors k x).card = d k)
    (hincidence : ∀ k, Fintype.card (J k) * e k =
      Fintype.card (BoolWeightLayer n k.val) * d k)
    (hcompiler : ∀ k, HasSupportedLayerCompiler n k.val (H k) (J k) (neighbors k)) :
    (worstCaseHeadComplexity n : ℝ) ≤
      ∑ k : Fin (n + 1), Fintype.card (BoolWeightLayer n k.val) *
        ((H k : ℝ) / e k) * (1 + Real.log ((e k : ℝ) / H k)) := by
  classical
  obtain ⟨f, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (HStar n)
  change ((Finset.univ.sup (HStar n) : ℕ) : ℝ) ≤ _
  rw [hmax]
  have hex (k : Fin (n + 1)) := exists_supported_layer_score_log_gain
    (neighbors k) (hd k) (he k) (hH k) (hgain k) (hdegree k) (hincidence k)
      (hcompiler k) f
  choose L F hF hpos hhigh hcost using hex
  have hb := HStar_le_of_supported_layer_closures L F f hF hpos hhigh
  calc
    (HStar n f : ℝ) ≤ (∑ k, L k : ℕ) := by exact_mod_cast hb
    _ = ∑ k, (L k : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun k _ ↦ hcost k)

end HeadComplexity.AxisZeroGluing
