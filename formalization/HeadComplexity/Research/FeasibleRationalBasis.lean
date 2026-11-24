import HeadComplexity.Research.RationalBasisCapacity

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
The exact active certificate cover, retaining both full-cube unit slack and the
coordinate box. These conditions are stronger than two-level interpolation alone.
-/

noncomputable section
namespace HeadComplexity.FeasibleRationalBasis
open Finset Matrix MvPolynomial
open scoped BigOperators
open PartialLinearCapacity DenominatorCapacity

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Retain the coordinate box in the compact-polyhedron active basis theorem. -/
theorem exists_bounded_active_basis (A : Matrix ι κ ℝ) (b : ι → ℝ)
    (hne : (PartialLinearCertificate.feasible A b).Nonempty) :
    ∃ T : ℝ, ∃ x : κ → ℝ,
      x ∈ PartialLinearCertificate.feasible A b ∧ (∀ k, |x k| ≤ T) ∧
      ∃ j : κ → Row ι κ, Function.Injective j ∧
      (∀ k, PartialLinearCertificate.boundedRows A (j k) ⬝ᵥ x =
        PartialLinearCertificate.boundedRhs b T (j k)) ∧
      ((PartialLinearCertificate.boundedRows A).submatrix j id).det ≠ 0 := by
  classical
  obtain ⟨a,ha⟩ := hne
  let T : ℝ := ∑ k, |a k|
  have hab : a ∈ Set.Icc (fun _ => -T) (fun _ => T) := by
    constructor
    · intro k
      have hk : |a k| ≤ T := single_le_sum (fun i _ => abs_nonneg (a i)) (mem_univ k)
      linarith [neg_abs_le (a k)]
    · intro k
      have hk : |a k| ≤ T := single_le_sum (fun i _ => abs_nonneg (a i)) (mem_univ k)
      exact (le_abs_self _).trans hk
  have hnb : (PartialLinearCertificate.feasible
      (PartialLinearCertificate.boundedRows A)
      (PartialLinearCertificate.boundedRhs b T)).Nonempty := by
    rw [PartialLinearCertificate.feasible_bounded]
    exact ⟨a,ha,hab⟩
  obtain ⟨x,hx,j,hj,hact,hdet⟩ := PartialLinearCertificate.exists_active_basis
    (PartialLinearCertificate.boundedRows A) (PartialLinearCertificate.boundedRhs b T)
      (PartialLinearCertificate.isCompact_feasible_bounded A b T) hnb
  rw [PartialLinearCertificate.feasible_bounded] at hx
  refine ⟨T,x,hx.1,?_,j,hj,hact,hdet⟩
  intro k
  exact abs_le.mpr ⟨hx.2.1 k,hx.2.2 k⟩

/-- Active unsigned rows retain unit signed slack everywhere and the whole box. -/
theorem exists_unsigned_basis (A : Matrix ι κ ℝ) (f : ι → Bool) (a : κ → ℝ)
    (hstrict : ∀ i, if f i then 0 < A i ⬝ᵥ a else A i ⬝ᵥ a < 0) :
    ∃ T : ℝ, ∃ x : κ → ℝ, ∃ j : κ → Row ι κ,
      Function.Injective j ∧
      (∀ i, 1 ≤ labelSign (f i) * (A i ⬝ᵥ x)) ∧
      (∀ k, |x k| ≤ T) ∧
      (∀ k, PartialLinearCertificate.boundedRows A (j k) ⬝ᵥ x =
        match j k with
        | Sum.inl i => labelSign (f i)
        | Sum.inr _ => -T) ∧
      ((PartialLinearCertificate.boundedRows A).submatrix j id).det ≠ 0 := by
  classical
  let B : Matrix ι κ ℝ := fun i => labelSign (f i) • A i
  have hB : ∀ i, 0 < B i ⬝ᵥ a := by
    intro i
    have hi := hstrict i
    cases hf : f i <;> simpa [B, labelSign, hf] using hi
  obtain ⟨T,x,hx,hbox,j,hj,hact,hdet⟩ :=
    exists_bounded_active_basis B (fun _ => 1) (feasible_unit_of_strict B a hB)
  let w : Row ι κ → ℝ := Sum.elim (fun i => labelSign (f i)) (fun _ => 1)
  have hrows (i : Row ι κ) (k : κ) :
      PartialLinearCertificate.boundedRows B i k =
        w i * PartialLinearCertificate.boundedRows A i k := by
    rcases i with i | (i | i)
    · rfl
    · simp [PartialLinearCertificate.boundedRows, w]
    · simp [PartialLinearCertificate.boundedRows, w]
  have hdet' : ((PartialLinearCertificate.boundedRows A).submatrix j id).det ≠ 0 := by
    have hm : (PartialLinearCertificate.boundedRows B).submatrix j id =
        fun i k => w (j i) * (PartialLinearCertificate.boundedRows A).submatrix j id i k := by
      ext i k
      exact hrows (j i) k
    intro hz
    apply hdet
    calc
      _ = Matrix.det (fun i k => w (j i) *
          (PartialLinearCertificate.boundedRows A).submatrix j id i k) := congrArg Matrix.det hm
      _ = (∏ i, w (j i)) * ((PartialLinearCertificate.boundedRows A).submatrix j id).det :=
        Matrix.det_mul_column _ _
      _ = 0 := by rw [hz, mul_zero]
  refine ⟨T,x,j,hj,?_,hbox,?_,hdet'⟩
  · intro i
    simpa only [B, smul_dotProduct, smul_eq_mul] using hx i
  · intro k
    have hk := hact k
    cases he : j k with
    | inl i =>
      change PartialLinearCertificate.boundedRows B (j k) ⬝ᵥ x =
        PartialLinearCertificate.boundedRhs (fun _ => 1) T (j k) at hk
      rw [he] at hk
      change (labelSign (f i) • A i) ⬝ᵥ x = 1 at hk
      change A i ⬝ᵥ x = labelSign (f i)
      cases hf : f i <;> simp [hf, labelSign] at hk ⊢ <;> linarith
    | inr i =>
      rw [he] at hk
      rcases i with i | i <;> exact hk

variable {n H : ℕ} {K : Type*}
open RationalBasisCapacity

/-- The uniquely reconstructed numerator coefficients. -/
def coefficients (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) (b : K → ℝ) (T : ℝ) :
    LinearParameter n H → ℝ :=
  let bp := Sum.elim b (fun _ => T)
  let M := (certificateMatrix (clearedFeatures B) c).map (eval bp)
  M.det⁻¹ • M.cramer (fun k => eval bp (RationalBasisCapacity.certificateRhs B c k))

/-- Exact feasible active charts: denominator positivity, nonsingular basis,
full-cube unit signed slack, and the coordinate box all remain in scope. -/
def patterns (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) : Set (Input n → Bool) :=
  {f | ∃ b : K → ℝ, ∃ T : ℝ,
    (∀ h x, 0 < eval b (B h x)) ∧
    ((certificateMatrix (clearedFeatures B) c).map
      (eval (Sum.elim b (fun _ => T)))).det ≠ 0 ∧
    (∀ x, 1 ≤ labelSign (f x) * score B b (coefficients B c b T) x) ∧
    ∀ k, |coefficients B c b T k| ≤ T}

/-- The canonical Cramer coefficients equal any solution to the nonsingular basis. -/
theorem coefficients_eq (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) (b : K → ℝ) (T : ℝ)
    (a : LinearParameter n H → ℝ)
    (hd : ((certificateMatrix (clearedFeatures B) c).map
      (eval (Sum.elim b (fun _ => T)))).det ≠ 0)
    (hsolve : (certificateMatrix (clearedFeatures B) c).map
      (eval (Sum.elim b (fun _ => T))) *ᵥ a =
      fun k => eval (Sum.elim b (fun _ => T)) (RationalBasisCapacity.certificateRhs B c k)) :
    coefficients B c b T = a := by
  dsimp only [coefficients]
  rw [PartialLinearCertificate.cramer_eq_det_smul hd hsolve, smul_smul,
    inv_mul_cancel₀ hd, one_smul]

/-- Every strict represented table belongs to a globally feasible active chart. -/
theorem exists_certificate (B : Fin H → Input n → MvPolynomial K ℝ)
    {f : Input n → Bool} (hf : f ∈ represented B) :
    ∃ c : Certificate (Input n) (LinearParameter n H), f ∈ patterns B c := by
  classical
  obtain ⟨b,a,hB,ha⟩ := hf
  let A := rationalFeatures B b
  obtain ⟨T,x,j,hj,hx,hbox,hact,hdet⟩ := exists_unsigned_basis A f a
    (by simpa only [A, rationalFeatures_dot] using ha)
  have hcard : (univ.image j).card = Fintype.card (LinearParameter n H) := by
    rw [card_image_of_injective _ hj, card_univ]
  let s : RowSet (Input n) (LinearParameter n H) := ⟨univ.image j,hcard⟩
  let g : s.val → Bool := fun i => match i.val with
    | Sum.inl i => f i
    | Sum.inr _ => false
  let c : Certificate (Input n) (LinearParameter n H) := ⟨s,g⟩
  let bp : K ⊕ Unit → ℝ := Sum.elim b (fun _ => T)
  let U := PartialLinearCertificate.boundedRows A
  let V := PartialLinearCertificate.boundedRows
    (fun i k => eval b (clearedFeatures B i k))
  have hscale (i : Row (Input n) (LinearParameter n H)) (k : LinearParameter n H) :
      V i k = rowScale B b i * U i k := by
    rcases i with i | (i | i)
    · exact eval_clearedFeatures_eq B b i (fun h => (hB h i).ne') k
    · simp [V, U, PartialLinearCertificate.boundedRows, rowScale]
    · simp [V, U, PartialLinearCertificate.boundedRows, rowScale]
  have hscale_pos (i : Row (Input n) (LinearParameter n H)) : 0 < rowScale B b i := by
    rcases i with i | i
    · simpa [rowScale, commonDen] using prod_pos (fun h _ => hB h i)
    · simp [rowScale]
  have hrange : Set.range j = Set.range (rowIndex s) := by
    rw [range_rowIndex]
    ext i
    simp [s]
  have hdetU : (U.submatrix (rowIndex s) id).det ≠ 0 :=
    PartialLinearCertificate.det_ne_zero_of_same_range U hdet hrange
  have hM : (certificateMatrix (clearedFeatures B) c).map (eval bp) =
      V.submatrix (rowIndex s) id := by
    ext i k
    exact eval_featureRows (clearedFeatures B) b T (rowIndex s i) k
  have hdetV : (V.submatrix (rowIndex s) id).det ≠ 0 := by
    have hm : V.submatrix (rowIndex s) id = fun i k =>
        rowScale B b (rowIndex s i) * U.submatrix (rowIndex s) id i k := by
      ext i k
      exact hscale (rowIndex s i) k
    rw [hm]
    change Matrix.det (Matrix.of (fun i k =>
      rowScale B b (rowIndex s i) * U.submatrix (rowIndex s) id i k)) ≠ 0
    rw [Matrix.det_mul_column]
    exact mul_ne_zero (prod_ne_zero_iff.mpr (fun i _ => (hscale_pos _).ne')) hdetU
  have hR (k : LinearParameter n H) :
      eval bp (RationalBasisCapacity.certificateRhs B c k) =
      rowScale B b (rowIndex s k) *
      (match rowIndex s k with
      | Sum.inl i => labelSign (f i)
      | Sum.inr _ => -T) := by
    change eval bp (match rowIndex s k with
      | Sum.inl i => C (labelSign (g (rowEquiv s k))) * rename Sum.inl (commonDen B i)
      | Sum.inr _ => -X (Sum.inr ())) = _
    cases he : rowIndex s k with
    | inl i =>
      have he' : (rowEquiv s k).val = Sum.inl i := he
      simp [g, he', bp, rowScale, eval_rename, mul_comm]
    | inr i => simp [bp, rowScale]
  have hsolve : (certificateMatrix (clearedFeatures B) c).map (eval bp) *ᵥ x =
      fun k => eval bp (RationalBasisCapacity.certificateRhs B c k) := by
    rw [hM]
    ext k
    rw [hR]
    have hi := (rowEquiv s k).property
    obtain ⟨l,_,hl⟩ := mem_image.mp hi
    change V (rowIndex s k) ⬝ᵥ x = _
    have hl' : j l = rowIndex s k := hl
    have he : V (rowIndex s k) = rowScale B b (rowIndex s k) • U (rowIndex s k) := by
      ext q
      exact hscale (rowIndex s k) q
    rw [he, smul_dotProduct, smul_eq_mul]
    congr 1
    rw [← hl']
    have hh := hact l
    cases he : j l <;> simpa only [he, U] using hh
  have hd : ((certificateMatrix (clearedFeatures B) c).map (eval bp)).det ≠ 0 := by
    rw [hM]
    exact hdetV
  have hc : coefficients B c b T = x := coefficients_eq B c b T x hd hsolve
  refine ⟨c,b,T,hB,hd,?_,?_⟩
  · intro i
    rw [hc]
    simpa only [A, rationalFeatures_dot] using hx i
  · simpa only [hc] using hbox

/-- Feasible active charts are subclasses of the original represented class. -/
theorem patterns_subset_represented (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) :
    patterns B c ⊆ represented B := by
  rintro f ⟨b,T,hB,_,hf,_⟩
  refine ⟨b,coefficients B c b T,hB,fun i => ?_⟩
  have hi := hf i
  cases hfi : f i <;> simp only [hfi, Bool.false_eq_true, ↓reduceIte, labelSign] at hi ⊢ <;>
    linarith

/-- Exact union after retaining every global active-polyhedron inequality. -/
theorem represented_eq_iUnion (B : Fin H → Input n → MvPolynomial K ℝ) :
    represented B = ⋃ c, patterns B c := by
  ext f
  constructor
  · intro hf
    obtain ⟨c,hc⟩ := exists_certificate B hf
    exact Set.mem_iUnion.mpr ⟨c,hc⟩
  · intro hf
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hf
    exact patterns_subset_represented B c hc

/-- The number of globally feasible extension tables is the remaining finite
quantity needed by the active certificate approach. -/
theorem card_represented_le_sum (B : Fin H → Input n → MvPolynomial K ℝ) :
    (represented B).ncard ≤ (by classical exact
      (∑ c : Certificate (Input n) (LinearParameter n H), (patterns B c).ncard)) := by
  classical
  rw [represented_eq_iUnion]
  exact Set.ncard_iUnion_le_of_fintype (patterns B)


/-- Exactly one nonlinear slope variable per head and input coordinate. -/
abbrev Parameter (n H : ℕ) := Fin H × Fin n

/-- The normalized affine denominator chart used by the original-model embedding. -/
def affineDen (h : Fin H) (x : Input n) : MvPolynomial (Parameter n H) ℝ :=
  1 + ∑ i, C (boolToReal (x i)) * X (h,i)

@[simp] theorem card_parameter : Fintype.card (Parameter n H) = n * H := by
  simp [Parameter, mul_comm]

/-- Every unchanged original-model truth table enters the normalized positive
rational chart. This is an upper-count embedding, not an inverse head compiler. -/
theorem represented_of_computable {f : Input n → Bool}
    (hf : computableWithHeadsN n H f) :
    f ∈ represented (affineDen (n := n) (H := H)) := by
  obtain ⟨φ,c,hstrict⟩ := exists_strict_fracCertificate (fracComputable_of_computable hf)
  let A := FracAtom.affineFamily φ
  let b : Parameter n H → ℝ := fun hi =>
    NormalizedCounting.parameterPoint A 1 (hi.1,true,hi.2)
  apply DenominatorCapacity.represented_of_affine affineDen A c f b
  · intro h x
    simp [affineDen, NormalizedCounting.denPoly, NormalizedCounting.linearPoly, b]
  · intro x
    simpa only [A, FracAtom.affineFamily, ← FracAtom.eval_eq_numPoly_div_denPoly] using hstrict x

/-- Full global feasibility is retained when starting from the original head model. -/
theorem exists_certificate_of_computable {f : Input n → Bool}
    (hf : computableWithHeadsN n H f) :
    ∃ c : Certificate (Input n) (LinearParameter n H),
      f ∈ patterns (affineDen (n := n) (H := H)) c :=
  exists_certificate affineDen (represented_of_computable hf)

/-- Exact finite upper-count interface for the unchanged original model, with
one chart for each unordered active row set and its selected labels. -/
theorem card_headComputableFunctions_le_sum :
    (headComputableFunctions n H).ncard ≤ (by classical exact
      (∑ c : Certificate (Input n) (LinearParameter n H),
        (patterns (affineDen (n := n) (H := H)) c).ncard)) := by
  classical
  have hsub : headComputableFunctions n H ⊆ represented (affineDen (n := n) (H := H)) :=
    fun _ hf => represented_of_computable hf
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (card_represented_le_sum affineDen)

end HeadComplexity.FeasibleRationalBasis
