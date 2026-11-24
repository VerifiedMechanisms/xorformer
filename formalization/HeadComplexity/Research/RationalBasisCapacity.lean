import HeadComplexity.Research.DenominatorCapacity

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
Exact unit-level active certificates for positive rational features.
The active basis is chosen before clearing the positive denominators. Thus actual
sample rows interpolate their Boolean labels at the two levels -1 and 1.
-/

noncomputable section
namespace HeadComplexity.RationalBasisCapacity
open Finset Matrix MvPolynomial
open scoped BigOperators
open PartialLinearCapacity DenominatorCapacity
variable {n H : ℕ} {K : Type*}

/-- The common positive denominator on one Boolean row. -/
def commonDen (B : Fin H → Input n → MvPolynomial K ℝ) (x : Input n) :
    MvPolynomial K ℝ := ∏ h, B h x

/-- Numeric score features before clearing denominators. -/
def rationalFeatures (B : Fin H → Input n → MvPolynomial K ℝ) (b : K → ℝ)
    (x : Input n) : LinearParameter n H → ℝ
  | Sum.inl _ => 1
  | Sum.inr (h,i) => boolToReal (x i) / eval b (B h x)

@[simp] theorem rationalFeatures_dot (B : Fin H → Input n → MvPolynomial K ℝ)
    (b : K → ℝ) (a : LinearParameter n H → ℝ) (x : Input n) :
    rationalFeatures B b x ⬝ᵥ a = score B b a x := by
  simp only [rationalFeatures, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Finset.univ_unique, Finset.sum_singleton, one_mul, score]
  congr 1
  apply sum_congr rfl
  intro h _
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro i _
  ring

/-- Clearing one row multiplies each rational feature by the same positive scalar. -/
theorem eval_clearedFeatures_eq (B : Fin H → Input n → MvPolynomial K ℝ)
    (b : K → ℝ) (x : Input n) (hB : ∀ h, eval b (B h x) ≠ 0)
    (k : LinearParameter n H) :
    eval b (clearedFeatures B x k) =
      eval b (commonDen B x) * rationalFeatures B b x k := by
  classical
  rcases k with k | ⟨h,i⟩
  · simp [clearedFeatures, commonDen, rationalFeatures]
  · simp only [clearedFeatures, rationalFeatures, commonDen, map_mul, eval_C, map_prod]
    rw [← Finset.mul_prod_erase univ (fun g => eval b (B g x)) (mem_univ h)]
    field_simp [hB h]

def rowScale (B : Fin H → Input n → MvPolynomial K ℝ) (b : K → ℝ) :
    Row (Input n) (LinearParameter n H) → ℝ :=
  Sum.elim (fun x => eval b (commonDen B x)) (fun _ => 1)

/-- The right side is scaled together with the selected rational sample row. -/
def certificateRhs (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) :
    LinearParameter n H → MvPolynomial (K ⊕ Unit) ℝ :=
  fun k => match rowIndex c.1 k with
    | Sum.inl x => C (labelSign (c.2 (rowEquiv c.1 k))) *
        rename Sum.inl (commonDen B x)
    | Sum.inr _ => -X (Sum.inr ())

/-- Positive-square Cramer reconstruction from the original two score levels. -/
def certificateScore (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) (x : Input n) :
    MvPolynomial (K ⊕ Unit) ℝ :=
  reconstructedScore (certificateMatrix (clearedFeatures B) c) (certificateRhs B c)
    (fun k => rename Sum.inl (clearedFeatures B x k))

/-- A chart retains denominator positivity and the nonsingular active basis. -/
def certificatePatterns (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) : Set (Input n → Bool) :=
  {f | ∃ b : K → ℝ, ∃ T : ℝ,
    (∀ h x, 0 < eval b (B h x)) ∧
    ((certificateMatrix (clearedFeatures B) c).map
      (eval (Sum.elim b (fun _ => T)))).det ≠ 0 ∧
    ∀ x, if f x then
      0 < eval (Sum.elim b (fun _ => T)) (certificateScore B c x)
      else eval (Sum.elim b (fun _ => T)) (certificateScore B c x) < 0}

/-- Every represented table has a unit-level rational certificate, with no width
increase and no lower bound on its relative margin. -/
theorem exists_certificate (B : Fin H → Input n → MvPolynomial K ℝ)
    {f : Input n → Bool} (hf : f ∈ represented B) :
    ∃ c : Certificate (Input n) (LinearParameter n H), f ∈ certificatePatterns B c := by
  classical
  obtain ⟨b,a,hB,ha⟩ := hf
  let A := rationalFeatures B b
  obtain ⟨T,x,j,hj,hx,hact,hdet⟩ := exists_unsigned_basis A f a
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
  have hR (k : LinearParameter n H) : eval bp (certificateRhs B c k) =
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
      fun k => eval bp (certificateRhs B c k) := by
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
  refine ⟨c,b,T,hB,hd,fun i => ?_⟩
  have he := eval_reconstructedScore_eq (certificateMatrix (clearedFeatures B) c)
    (certificateRhs B c) (fun k => rename Sum.inl (clearedFeatures B i k)) bp x hd hsolve
  have he' : eval bp (certificateScore B c i) =
      ((certificateMatrix (clearedFeatures B) c).map (eval bp)).det ^ 2 *
        ((∏ h, eval b (B h i)) * (A i ⬝ᵥ x)) := by
    simpa [certificateScore, bp, eval_rename,
      eval_clearedFeatures B b x i (fun h => (hB h i).ne'), A] using he
  have hp : 0 < ((certificateMatrix (clearedFeatures B) c).map (eval bp)).det ^ 2 :=
    sq_pos_of_ne_zero hd
  have hprod : 0 < ∏ h, eval b (B h i) := prod_pos (fun h _ => hB h i)
  change if f i then 0 < eval bp (certificateScore B c i)
    else eval bp (certificateScore B c i) < 0
  rw [he']
  have hi := hx i
  cases hfi : f i <;> simp only [hfi, Bool.false_eq_true, ↓reduceIte] at hi ⊢
  · exact mul_neg_of_pos_of_neg hp (mul_neg_of_pos_of_neg hprod hi)
  · exact mul_pos hp (mul_pos hprod hi)


/-- Every nonsingular positive chart still consists of actual rational scores. -/
theorem certificatePatterns_subset_represented
    (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) :
    certificatePatterns B c ⊆ represented B := by
  classical
  rintro f ⟨b,T,hB,hd,hf⟩
  let bp : K ⊕ Unit → ℝ := Sum.elim b (fun _ => T)
  let M := (certificateMatrix (clearedFeatures B) c).map (eval bp)
  let r := fun k => eval bp (certificateRhs B c k)
  let a := M.det⁻¹ • M.cramer r
  have hsolve : M *ᵥ a = r := by
    simp only [a, mulVec_smul, mulVec_cramer, smul_smul]
    rw [inv_mul_cancel₀ hd, one_smul]
  refine ⟨b,a,hB,fun i => ?_⟩
  have he := eval_reconstructedScore_eq (certificateMatrix (clearedFeatures B) c)
    (certificateRhs B c) (fun k => rename Sum.inl (clearedFeatures B i k)) bp a hd hsolve
  have he' : eval bp (certificateScore B c i) =
      M.det ^ 2 * ((∏ h, eval b (B h i)) * score B b a i) := by
    simpa [certificateScore, bp, eval_rename,
      eval_clearedFeatures B b a i (fun h => (hB h i).ne'), M] using he
  have hp : 0 < M.det ^ 2 := sq_pos_of_ne_zero hd
  have hprod : 0 < ∏ h, eval b (B h i) := prod_pos (fun h _ => hB h i)
  have hi := hf i
  change if f i then 0 < eval bp (certificateScore B c i)
    else eval bp (certificateScore B c i) < 0 at hi
  rw [he'] at hi
  cases hfi : f i <;> simp only [hfi, Bool.false_eq_true, ↓reduceIte] at hi ⊢
  · by_contra hs
    have hn := mul_nonneg hp.le (mul_nonneg hprod.le (le_of_not_gt hs))
    linarith
  · exact (mul_pos_iff_of_pos_left hprod).mp ((mul_pos_iff_of_pos_left hp).mp hi)

/-- The active rational charts give an exact union, not merely an arbitrary
polynomial enlargement. -/
theorem represented_eq_iUnion (B : Fin H → Input n → MvPolynomial K ℝ) :
    represented B = ⋃ c, certificatePatterns B c := by
  ext f
  constructor
  · intro hf
    obtain ⟨c,hc⟩ := exists_certificate B hf
    exact Set.mem_iUnion.mpr ⟨c,hc⟩
  · intro hf
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hf
    exact certificatePatterns_subset_represented B c hc

/-- With only actual sample rows and a constant selected label, the unique
interpolated score has that constant sign on the entire cube. -/
theorem eq_constant_of_constant_sample_labels
    (B : Fin H → Input n → MvPolynomial K ℝ)
    (c : Certificate (Input n) (LinearParameter n H)) (t : Bool)
    (hrows : ∀ k, ∃ x, rowIndex c.1 k = Sum.inl x)
    (hlabels : ∀ k, c.2 (rowEquiv c.1 k) = t)
    {f : Input n → Bool} (hf : f ∈ certificatePatterns B c) : f = fun _ => t := by
  classical
  obtain ⟨b,T,hB,hd,hf⟩ := hf
  let bp : K ⊕ Unit → ℝ := Sum.elim b (fun _ => T)
  let a : LinearParameter n H → ℝ := Pi.single (Sum.inl ()) (labelSign t)
  have ha (i : Input n) :
      (fun k => eval b (clearedFeatures B i k)) ⬝ᵥ a =
        eval b (commonDen B i) * labelSign t := by
    simp [a, dotProduct_single, clearedFeatures, commonDen]
  have hsolve : (certificateMatrix (clearedFeatures B) c).map (eval bp) *ᵥ a =
      fun k => eval bp (certificateRhs B c k) := by
    ext k
    obtain ⟨i,hi⟩ := hrows k
    change (fun q => eval bp (featureRows (clearedFeatures B) (rowIndex c.1 k) q)) ⬝ᵥ a = _
    rw [hi]
    simp only [featureRows, Sum.elim_inl, eval_rename, bp, Function.comp_def, Sum.elim_inl]
    rw [ha]
    simp [certificateRhs, hi, hlabels, eval_rename, mul_comm]
  have hp : 0 < ((certificateMatrix (clearedFeatures B) c).map (eval bp)).det ^ 2 :=
    sq_pos_of_ne_zero hd
  ext i
  have he := eval_reconstructedScore_eq (certificateMatrix (clearedFeatures B) c)
    (certificateRhs B c) (fun k => rename Sum.inl (clearedFeatures B i k)) bp a hd hsolve
  have he' : eval bp (certificateScore B c i) =
      ((certificateMatrix (clearedFeatures B) c).map (eval bp)).det ^ 2 *
        (eval b (commonDen B i) * labelSign t) := by
    simpa only [certificateScore, eval_rename, bp, Function.comp_def, Sum.elim_inl, ha] using he
  have hD : 0 < eval b (commonDen B i) := by
    simpa [commonDen] using prod_pos (fun h _ => hB h i)
  have hi := hf i
  change if f i then 0 < eval bp (certificateScore B c i)
    else eval bp (certificateScore B c i) < 0 at hi
  rw [he'] at hi
  have hpos := mul_pos hp hD
  cases ht : t <;> cases hfi : f i <;> simp_all [labelSign] <;> nlinarith


/-- The finite certificate count isolates exactly the remaining positive rational
interpolation problem, without enlarging each chart to arbitrary polynomial signs. -/
theorem card_represented_le_sum (B : Fin H → Input n → MvPolynomial K ℝ) :
    (represented B).ncard ≤ (by classical exact
      (∑ c : Certificate (Input n) (LinearParameter n H), (certificatePatterns B c).ncard)) := by
  classical
  have hcover : represented B ⊆ ⋃ c, certificatePatterns B c := by
    intro f hf
    obtain ⟨c,hc⟩ := exists_certificate B hf
    exact Set.mem_iUnion.mpr ⟨c,hc⟩
  exact (Set.ncard_le_ncard hcover (Set.toFinite _)).trans
    (Set.ncard_iUnion_le_of_fintype (certificatePatterns B))

end HeadComplexity.RationalBasisCapacity
