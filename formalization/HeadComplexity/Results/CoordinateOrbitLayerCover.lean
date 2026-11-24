import HeadComplexity.Results.RegularLayerCoverTransfer
import HeadComplexity.Atoms.FracAtomSymmetry

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators Topology

/-- Coordinate relabeling preserves the closure of the original head class. -/
theorem HeadScoreClosure.permute {n : ℕ} {I : Type*} [Fintype I]
    {F : (Fin n → Bool) → ℝ} (hF : HeadScoreClosure n I F)
    (σ : Equiv.Perm (Fin n)) :
    HeadScoreClosure n I (fun x ↦ F (permuteBits σ x)) := by
  let T : ((Fin n → Bool) → ℝ) → (Fin n → Bool) → ℝ :=
    fun G x ↦ G (permuteBits σ x)
  have hT : Continuous T := by unfold T; fun_prop
  have hm := mem_closure_image hT.continuousAt hF
  apply closure_mono (s := T '' headScoreRange n I) (t := headScoreRange n I) ?_ hm
  rintro _ ⟨G, ⟨φ, rfl⟩, rfl⟩
  exact ⟨fun h ↦ (φ h).permute σ, by funext x; simp [T]⟩

theorem gradedSupport_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → Bool) :
    gradedSupport (permuteBits σ x) = (gradedSupport x).map σ.symm.toEmbedding := by
  classical
  ext i
  simp only [gradedSupport, permuteBits, Finset.mem_map_equiv,
    Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_symm]
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem gradedSupport_card_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → Bool) :
    (gradedSupport (permuteBits σ x)).card = (gradedSupport x).card := by
  rw [gradedSupport_permute, Finset.card_map]

noncomputable def layerCoordinateEquiv {n k : ℕ} (σ : Equiv.Perm (Fin n)) :
    BoolWeightLayer n k ≃ BoolWeightLayer n k where
  toFun x := ⟨permuteBits σ x.val, (gradedSupport_card_permute σ x.val).trans x.property⟩
  invFun x := ⟨permuteBits σ.symm x.val,
    (gradedSupport_card_permute σ.symm x.val).trans x.property⟩
  left_inv x := by apply Subtype.ext; exact permuteBits_symm σ _
  right_inv x := by apply Subtype.ext; simpa using permuteBits_symm σ.symm x.val

theorem layerCoordinate_transitive {n k : ℕ} (x y : BoolWeightLayer n k) :
    ∃ σ : Equiv.Perm (Fin n), layerCoordinateEquiv σ x = y := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (gradedSupport y.val) (gradedSupport x.val) (y.property.trans x.property.symm)
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  apply gradedSupport_injective
  change gradedSupport (permuteBits σ x.val) = gradedSupport y.val
  rw [gradedSupport_permute, ← hσ, Finset.map_map]
  simp

noncomputable def coordinateOrbitNeighbors {n k : ℕ}
    (Q : Finset (BoolWeightLayer n k)) (x : BoolWeightLayer n k) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun σ ↦ layerCoordinateEquiv σ x ∈ Q)

theorem coordinateOrbitNeighbors_card_eq {n k : ℕ}
    (Q : Finset (BoolWeightLayer n k)) (x y : BoolWeightLayer n k) :
    (coordinateOrbitNeighbors Q x).card = (coordinateOrbitNeighbors Q y).card := by
  classical
  obtain ⟨τ, hτ⟩ := layerCoordinate_transitive y x
  apply Finset.card_bij (fun σ _ ↦ σ.trans τ)
  · intro σ hσ
    simp only [coordinateOrbitNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hσ ⊢
    have heq : layerCoordinateEquiv (σ.trans τ) y = layerCoordinateEquiv σ x := by
      apply Subtype.ext
      change permuteBits (σ.trans τ) y.val = permuteBits σ x.val
      rw [permuteBits_trans]
      exact congrArg (permuteBits σ) (congrArg Subtype.val hτ)
    rwa [heq]
  · intro σ hσ ρ hρ heq
    apply Equiv.ext
    intro i
    exact τ.injective (congrArg (fun e : Equiv.Perm (Fin n) ↦ e i) heq)
  · intro ρ hρ
    refine ⟨ρ.trans τ.symm, ?_, by ext i; simp⟩
    simp only [coordinateOrbitNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hρ ⊢
    have heq : layerCoordinateEquiv (ρ.trans τ.symm) x = layerCoordinateEquiv ρ y := by
      apply Subtype.ext
      change permuteBits (ρ.trans τ.symm) x.val = permuteBits ρ y.val
      rw [permuteBits_trans, ← congrArg Subtype.val hτ]
      change permuteBits ρ (permuteBits τ.symm (permuteBits τ y.val)) = _
      rw [permuteBits_symm]
    rwa [heq]

/-- Every coordinate orbit is regular; its cell size is exactly the size of
its base cell, with repetitions indexed and charged as separate cells. -/
theorem coordinateOrbit_regular {n k : ℕ} (Q : Finset (BoolWeightLayer n k))
    (hq : Q.Nonempty) :
    ∃ d : ℕ, 0 < d ∧
      (∀ x, (coordinateOrbitNeighbors Q x).card = d) ∧
      Fintype.card (Equiv.Perm (Fin n)) * Q.card =
        Fintype.card (BoolWeightLayer n k) * d := by
  classical
  obtain ⟨x₀, hx₀⟩ := hq
  let d := (coordinateOrbitNeighbors Q x₀).card
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    refine ⟨Equiv.refl _, ?_⟩
    change Equiv.refl _ ∈ Finset.univ.filter _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    convert hx₀ using 1
    apply Subtype.ext
    rfl
  have hdegree (x : BoolWeightLayer n k) :
      (coordinateOrbitNeighbors Q x).card = d := coordinateOrbitNeighbors_card_eq Q x x₀
  refine ⟨d, hd, hdegree, ?_⟩
  have hcol (σ : Equiv.Perm (Fin n)) :
      ∑ x : BoolWeightLayer n k, (if layerCoordinateEquiv σ x ∈ Q then 1 else 0 : ℕ) =
        Q.card := by
    rw [(layerCoordinateEquiv σ).sum_comp (fun x ↦ if x ∈ Q then 1 else 0)]
    simp
  calc
    Fintype.card (Equiv.Perm (Fin n)) * Q.card =
        ∑ σ : Equiv.Perm (Fin n), ∑ x : BoolWeightLayer n k,
          (if layerCoordinateEquiv σ x ∈ Q then 1 else 0 : ℕ) := by simp [hcol]
    _ = ∑ x : BoolWeightLayer n k, (coordinateOrbitNeighbors Q x).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [coordinateOrbitNeighbors, Finset.card_filter]
    _ = Fintype.card (BoolWeightLayer n k) * d := by simp [hdegree]

/-- A single supported cell compiler yields the complete coordinate-orbit
compiler. Labels are pulled back separately for every orbit member. -/
theorem supported_cell_coordinate_orbit {n k H : ℕ}
    (Q : Finset (BoolWeightLayer n k))
    (hcell : ∀ f : (Fin n → Bool) → Bool, ∃ F : (Fin n → Bool) → ℝ,
      HeadScoreClosure n (Fin H) F ∧
      (∀ x, k < (gradedSupport x).card → F x = 0) ∧
      (∀ x : BoolWeightLayer n k, x ∈ Q → 0 < outputSign (f x.val) * F x.val) ∧
      (∀ x : BoolWeightLayer n k, x ∉ Q → F x.val = 0)) :
    HasSupportedLayerCompiler n k H (Equiv.Perm (Fin n)) (coordinateOrbitNeighbors Q) := by
  classical
  intro f
  have hex (σ : Equiv.Perm (Fin n)) := hcell (fun x ↦ f (permuteBits σ.symm x))
  choose F hF hhigh hpos hzero using hex
  refine ⟨fun σ x ↦ F σ (permuteBits σ x), fun σ ↦ (hF σ).permute σ, ?_, ?_, ?_⟩
  · intro σ x hx
    apply hhigh σ
    rwa [gradedSupport_card_permute]
  · intro σ x hx
    have hm : layerCoordinateEquiv σ x ∈ Q := by
      simpa [coordinateOrbitNeighbors] using hx
    have hp := hpos σ (layerCoordinateEquiv σ x) hm
    change 0 < outputSign (f (permuteBits σ.symm (permuteBits σ x.val))) *
      F σ (permuteBits σ x.val) at hp
    simpa only [permuteBits_symm] using hp
  · intro σ x hx
    have hm : layerCoordinateEquiv σ x ∉ Q := by
      simpa [coordinateOrbitNeighbors] using hx
    exact hzero σ (layerCoordinateEquiv σ x) hm

/-- Explicit orbit cover and exception count from one arbitrary-label
supported cell. No external combinatorial covering design is required. -/
theorem exists_layer_score_of_supported_cell {n k H : ℕ}
    (Q : Finset (BoolWeightLayer n k)) (hH : 0 < H) (hgain : H ≤ Q.card)
    (hcell : ∀ f : (Fin n → Bool) → Bool, ∃ F : (Fin n → Bool) → ℝ,
      HeadScoreClosure n (Fin H) F ∧
      (∀ x, k < (gradedSupport x).card → F x = 0) ∧
      (∀ x : BoolWeightLayer n k, x ∈ Q → 0 < outputSign (f x.val) * F x.val) ∧
      (∀ x : BoolWeightLayer n k, x ∉ Q → F x.val = 0))
    (f : (Fin n → Bool) → Bool) :
    ∃ (L : ℕ) (F : (Fin n → Bool) → ℝ),
      HeadScoreClosure n (Fin L) F ∧
      (∀ x : BoolWeightLayer n k, 0 < outputSign (f x.val) * F x.val) ∧
      (∀ x, k < (gradedSupport x).card → F x = 0) ∧
      (L : ℝ) ≤ Fintype.card (BoolWeightLayer n k) * ((H : ℝ) / Q.card) *
        (1 + Real.log ((Q.card : ℝ) / H)) := by
  have he : 0 < Q.card := lt_of_lt_of_le hH hgain
  obtain ⟨d, hd, hdegree, hincidence⟩ := coordinateOrbit_regular Q (Finset.card_pos.mp he)
  exact exists_supported_layer_score_log_gain (coordinateOrbitNeighbors Q) hd he hH hgain
    hdegree hincidence (supported_cell_coordinate_orbit Q hcell) f

end HeadComplexity.AxisZeroGluing
