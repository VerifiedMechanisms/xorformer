import HeadComplexity.Research.PartialLinearCertificate
import HeadComplexity.Results.WarrenBound
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option backward.isDefEq.respectTransparency false

/-!
Polynomial degree bounds and finite sign capacity after active-row elimination
of arbitrary linear coefficients.
-/

noncomputable section
namespace HeadComplexity.PartialLinearCapacity
open Finset Matrix MvPolynomial
open scoped BigOperators

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The degree of a polynomial determinant is bounded by the sum of its column bounds. -/
theorem det_totalDegree_le (M : Matrix κ κ (MvPolynomial ν ℝ)) (d : κ → ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ d j) :
    M.det.totalDegree ≤ ∑ j, d j := by
  classical
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  exact sum_le_sum (fun j _ => hM (σ j) j)

/-- Uniform-entry version of the determinant degree bound. -/
theorem det_totalDegree_le_uniform (M : Matrix κ κ (MvPolynomial ν ℝ)) {D : ℕ}
    (hM : ∀ i j, (M i j).totalDegree ≤ D) :
    M.det.totalDegree ≤ Fintype.card κ * D := by
  simpa using det_totalDegree_le M (fun _ => D) hM

/-- Replacing one determinant column by linear polynomials saves one factor of `D`. -/
theorem cramer_totalDegree_le (M : Matrix κ κ (MvPolynomial ν ℝ))
    (r : κ → MvPolynomial ν ℝ) {D : ℕ}
    (hM : ∀ i j, (M i j).totalDegree ≤ D) (hr : ∀ i, (r i).totalDegree ≤ 1)
    (k : κ) :
    (Matrix.cramer M r k).totalDegree ≤ (Fintype.card κ - 1) * D + 1 := by
  classical
  rw [Matrix.cramer_apply]
  have hm : ∀ i j, (M.updateCol k r i j).totalDegree ≤ if j = k then 1 else D := by
    intro i j
    by_cases hj : j = k
    · subst j
      simpa using hr i
    · simpa [Matrix.updateCol, hj] using hM i j
  refine (det_totalDegree_le _ _ hm).trans ?_
  rw [← sum_erase_add _ _ (mem_univ k)]
  have he : (∑ j ∈ univ.erase k, if j = k then 1 else D) =
      (Fintype.card κ - 1) * D := by
    calc
      _ = ∑ j ∈ univ.erase k, D := by
        apply sum_congr rfl
        intro j hj
        simp [(mem_erase.mp hj).1]
      _ = _ := by simp
  simp [he]

/-- The polynomial representing a score after Cramer reconstruction and positive-square
clearing. -/
def reconstructedScore (M : Matrix κ κ (MvPolynomial ν ℝ))
    (r a : κ → MvPolynomial ν ℝ) : MvPolynomial ν ℝ :=
  M.det * (a ⬝ᵥ Matrix.cramer M r)

theorem reconstructedScore_totalDegree_le
    (M : Matrix κ κ (MvPolynomial ν ℝ)) (r a : κ → MvPolynomial ν ℝ)
    {D : ℕ} (hM : ∀ i j, (M i j).totalDegree ≤ D)
    (hr : ∀ i, (r i).totalDegree ≤ 1) (ha : ∀ i, (a i).totalDegree ≤ D)
    (hκ : 0 < Fintype.card κ) :
    (reconstructedScore M r a).totalDegree ≤ 2 * D * Fintype.card κ + 1 := by
  unfold reconstructedScore
  refine (totalDegree_mul _ _).trans ?_
  have hdet := det_totalDegree_le_uniform M hM
  have hdot : (a ⬝ᵥ Matrix.cramer M r).totalDegree ≤
      D + (Fintype.card κ - 1) * D + 1 := by
    apply totalDegree_finsetSum_le
    intro k _
    have hc := cramer_totalDegree_le M r hM hr k
    exact (totalDegree_mul _ _).trans (by have hk := ha k; omega)
  have he : (Fintype.card κ - 1) * D + D = Fintype.card κ * D := by
    have hk : Fintype.card κ - 1 + 1 = Fintype.card κ := by omega
    nlinarith
  nlinarith

/-- Evaluation commutes with Cramer's polynomial numerators. -/
theorem eval_cramer (M : Matrix κ κ (MvPolynomial ν ℝ))
    (r : κ → MvPolynomial ν ℝ) (b : ν → ℝ) (k : κ) :
    eval b (Matrix.cramer M r k) =
      Matrix.cramer (M.map (eval b)) (fun i => eval b (r i)) k := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, (eval b).map_det]
  congr 1
  ext i j
  by_cases hj : j = k
  · subst j
    simp
  · simp [Matrix.updateCol, hj]

/-- The reconstructed polynomial preserves every strict score sign at a certificate. -/
theorem eval_reconstructedScore_pos_iff
    (M : Matrix κ κ (MvPolynomial ν ℝ)) (r a : κ → MvPolynomial ν ℝ)
    (b : ν → ℝ) (x : κ → ℝ)
    (hdet : (M.map (eval b)).det ≠ 0)
    (hsolve : (M.map (eval b)) *ᵥ x = fun i => eval b (r i)) :
    0 < eval b (reconstructedScore M r a) ↔ 0 < (fun i => eval b (a i)) ⬝ᵥ x := by
  simpa only [reconstructedScore, map_mul, (eval b).map_det, dotProduct,
    map_sum, eval_cramer, RingHom.mapMatrix_apply] using
    PartialLinearCertificate.sign_cramer hdet hsolve (fun i => eval b (a i))


/-- The two real signs indexed by Boolean labels. -/
def labelSign (t : Bool) : ℝ := if t then 1 else -1

@[simp] theorem labelSign_sq (t : Bool) : labelSign t * labelSign t = 1 := by
  cases t <;> norm_num [labelSign]

@[simp] theorem labelSign_ne_zero (t : Bool) : labelSign t ≠ 0 := by
  cases t <;> norm_num [labelSign]

omit [DecidableEq κ] in
/-- Strict linear feasibility can always be scaled to unit signed slack. -/
theorem feasible_unit_of_strict (A : Matrix ι κ ℝ) (a : κ → ℝ)
    (hA : ∀ i, 0 < A i ⬝ᵥ a) :
    (PartialLinearCertificate.feasible A (fun _ => 1)).Nonempty := by
  let s : ℝ := ∑ i, (A i ⬝ᵥ a)⁻¹
  refine ⟨s • a, fun i => ?_⟩
  have hs : (A i ⬝ᵥ a)⁻¹ ≤ s :=
    single_le_sum (fun j _ => inv_nonneg.mpr (hA j).le) (mem_univ i)
  have hm := mul_le_mul_of_nonneg_right hs (hA i).le
  simpa [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ (hA i).ne'] using hm

abbrev Row (ι κ : Type*) := ι ⊕ (κ ⊕ κ)
abbrev RowSet (ι κ : Type*) [Fintype κ] :=
  {s : Finset (Row ι κ) // s.card = Fintype.card κ}

/-- Only labels on the selected rows are recorded; box labels are harmless unused bits. -/
abbrev Certificate (ι κ : Type*) [Fintype κ] :=
  (s : RowSet ι κ) × (s.val → Bool)

noncomputable def rowEquiv (s : RowSet ι κ) : κ ≃ s.val :=
  Fintype.equivOfCardEq (by simp [s.property])

noncomputable def rowIndex (s : RowSet ι κ) : κ → Row ι κ :=
  fun k => rowEquiv s k

omit [Fintype ι] [DecidableEq κ] in
@[simp] theorem range_rowIndex (s : RowSet ι κ) :
    Set.range (rowIndex s) = s.val := by
  ext i
  constructor
  · rintro ⟨k,rfl⟩
    exact (rowEquiv s k).property
  · intro hi
    obtain ⟨k,hk⟩ := (rowEquiv s).surjective ⟨i,hi⟩
    exact ⟨k, congrArg Subtype.val hk⟩

@[simp] theorem card_certificate [DecidableEq ι] :
    Fintype.card (Certificate ι κ) =
      (Fintype.card ι + 2 * Fintype.card κ).choose (Fintype.card κ) *
        2 ^ Fintype.card κ := by
  classical
  simp only [Certificate, Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, RowSet]
  have he (s : {s : Finset (Row ι κ) // s.card = Fintype.card κ}) :
      2 ^ s.val.card = 2 ^ Fintype.card κ := by rw [s.property]
  simp_rw [he]
  simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset_len]
  simp [Row, two_mul]

/-- Polynomial rows, after adjoining one variable for the coordinate box radius. -/
def featureRows (P : Matrix ι κ (MvPolynomial ν ℝ)) :
    Matrix (Row ι κ) κ (MvPolynomial (ν ⊕ Unit) ℝ) :=
  Sum.elim (fun i j => rename Sum.inl (P i j))
    (Sum.elim (fun k => Pi.single k 1) (fun k => Pi.single k (-1)))

def certificateMatrix (P : Matrix ι κ (MvPolynomial ν ℝ)) (c : Certificate ι κ) :
    Matrix κ κ (MvPolynomial (ν ⊕ Unit) ℝ) :=
  (featureRows P).submatrix (rowIndex c.1) id

def certificateRhs (c : Certificate ι κ) : κ → MvPolynomial (ν ⊕ Unit) ℝ :=
  fun k => match rowIndex c.1 k with
    | Sum.inl _ => C (labelSign (c.2 (rowEquiv c.1 k)))
    | Sum.inr _ => -X (Sum.inr ())

def certificateScore (P : Matrix ι κ (MvPolynomial ν ℝ)) (c : Certificate ι κ)
    (i : ι) : MvPolynomial (ν ⊕ Unit) ℝ :=
  reconstructedScore (certificateMatrix P c) (certificateRhs c)
    (fun k => rename Sum.inl (P i k))

omit [Fintype ι] [Fintype κ] in
theorem featureRows_totalDegree_le (P : Matrix ι κ (MvPolynomial ν ℝ))
    {D : ℕ} (hP : ∀ i j, (P i j).totalDegree ≤ D) (i : Row ι κ) (j : κ) :
    (featureRows P i j).totalDegree ≤ D := by
  classical
  rcases i with i | (k | k)
  · exact (totalDegree_rename_le _ _).trans (hP i j)
  · simp [featureRows, Pi.single_apply]
    split_ifs <;> simp
  · simp [featureRows, Pi.single_apply]
    split_ifs <;> simp

omit [Fintype ι] [DecidableEq κ] in
theorem certificateRhs_totalDegree_le (c : Certificate ι κ) (k : κ) :
    (certificateRhs (ν := ν) c k).totalDegree ≤ 1 := by
  unfold certificateRhs
  split <;> simp

omit [Fintype ι] in
theorem certificateScore_totalDegree_le (P : Matrix ι κ (MvPolynomial ν ℝ))
    {D : ℕ} (hP : ∀ i j, (P i j).totalDegree ≤ D)
    (hκ : 0 < Fintype.card κ) (c : Certificate ι κ) (i : ι) :
    (certificateScore P c i).totalDegree ≤ 2 * D * Fintype.card κ + 1 := by
  apply reconstructedScore_totalDegree_le
  · exact fun j k => featureRows_totalDegree_le P hP (rowIndex c.1 j) k
  · exact certificateRhs_totalDegree_le c
  · exact fun k => (totalDegree_rename_le _ _).trans (hP i k)
  · exact hκ


/-- A strict pattern has a basis certificate using unsigned sample rows; labels occur
only in the right-hand side. -/
theorem exists_unsigned_basis (A : Matrix ι κ ℝ) (f : ι → Bool) (a : κ → ℝ)
    (hstrict : ∀ i, if f i then 0 < A i ⬝ᵥ a else A i ⬝ᵥ a < 0) :
    ∃ T : ℝ, ∃ x : κ → ℝ, ∃ j : κ → Row ι κ,
      Function.Injective j ∧
      (∀ i, if f i then 0 < A i ⬝ᵥ x else A i ⬝ᵥ x < 0) ∧
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
  obtain ⟨T,x,hx,j,hj,hact,hdet⟩ :=
    PartialLinearCertificate.exists_bounded_active_basis B (fun _ => 1)
      (feasible_unit_of_strict B a hB)
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
  refine ⟨T,x,j,hj,?_,?_,hdet'⟩
  · intro i
    have hi := hx i
    change 1 ≤ (labelSign (f i) • A i) ⬝ᵥ x at hi
    cases hf : f i <;> simp [hf, labelSign] at hi ⊢ <;> linarith
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

/-- Polynomial feature signs with arbitrary nonlinear parameters and linear coefficients. -/
def patterns (P : Matrix ι κ (MvPolynomial ν ℝ)) : Set (ι → Bool) :=
  {f | ∃ b : ν → ℝ, ∃ a : κ → ℝ,
    ∀ i, if f i then 0 < (fun k => eval b (P i k)) ⬝ᵥ a
      else (fun k => eval b (P i k)) ⬝ᵥ a < 0}

omit [Fintype ι] [Fintype κ] in
/-- Evaluating the augmented rows gives exactly the numeric sample and box rows. -/
theorem eval_featureRows (P : Matrix ι κ (MvPolynomial ν ℝ)) (b : ν → ℝ) (T : ℝ)
    (i : Row ι κ) (k : κ) :
    eval (Sum.elim b (fun _ => T)) (featureRows P i k) =
      PartialLinearCertificate.boundedRows (fun i k => eval b (P i k)) i k := by
  rcases i with i | (j | j)
  · simp [featureRows, PartialLinearCertificate.boundedRows, eval_rename]
  · simp [featureRows, PartialLinearCertificate.boundedRows, Pi.single_apply]
  · simp [featureRows, PartialLinearCertificate.boundedRows, Pi.single_apply]
    split_ifs <;> simp


/-- Exact positive-square identity behind sign reconstruction. -/
theorem eval_reconstructedScore_eq
    (M : Matrix κ κ (MvPolynomial ν ℝ)) (r a : κ → MvPolynomial ν ℝ)
    (b : ν → ℝ) (x : κ → ℝ)
    (hdet : (M.map (eval b)).det ≠ 0)
    (hsolve : (M.map (eval b)) *ᵥ x = fun i => eval b (r i)) :
    eval b (reconstructedScore M r a) =
      (M.map (eval b)).det ^ 2 * ((fun i => eval b (a i)) ⬝ᵥ x) := by
  simp only [reconstructedScore, map_mul, (eval b).map_det, RingHom.mapMatrix_apply,
    dotProduct, map_sum, eval_cramer]
  rw [PartialLinearCertificate.cramer_eq_det_smul hdet hsolve]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hs : (∑ k, eval b (a k) * ((M.map (eval b)).det * x k)) =
      (M.map (eval b)).det * ∑ k, eval b (a k) * x k := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  rw [hs]
  ring

/-- Every partially linear sign pattern belongs to a polynomial chart indexed by an
unordered row subset and its selected labels. -/
theorem exists_certificate_pattern (P : Matrix ι κ (MvPolynomial ν ℝ))
    {f : ι → Bool} (hf : f ∈ patterns P) :
    ∃ c : Certificate ι κ, f ∈ strictPolynomialSignPatterns (certificateScore P c) := by
  classical
  obtain ⟨b,a,ha⟩ := hf
  let A : Matrix ι κ ℝ := fun i k => eval b (P i k)
  obtain ⟨T,x,j,hj,hx,hact,hdet⟩ := exists_unsigned_basis A f a ha
  have hcard : (univ.image j).card = Fintype.card κ := by
    rw [card_image_of_injective _ hj, card_univ]
  let s : RowSet ι κ := ⟨univ.image j,hcard⟩
  let g : s.val → Bool := fun i => match i.val with
    | Sum.inl i => f i
    | Sum.inr _ => false
  let c : Certificate ι κ := ⟨s,g⟩
  let bp : ν ⊕ Unit → ℝ := Sum.elim b (fun _ => T)
  let U : Matrix (Row ι κ) κ ℝ := PartialLinearCertificate.boundedRows A
  have hrange : Set.range j = Set.range (rowIndex s) := by
    rw [range_rowIndex]
    ext i
    simp [s]
  have hdetU : (U.submatrix (rowIndex s) id).det ≠ 0 :=
    PartialLinearCertificate.det_ne_zero_of_same_range U hdet hrange
  have hM : (certificateMatrix P c).map (eval bp) =
      U.submatrix (rowIndex s) id := by
    ext i k
    exact eval_featureRows P b T (rowIndex s i) k
  have hR (k : κ) : eval bp (certificateRhs c k) =
      match rowIndex s k with
      | Sum.inl i => labelSign (f i)
      | Sum.inr _ => -T := by
    change eval bp (match rowIndex s k with
      | Sum.inl _ => C (labelSign (g (rowEquiv s k)))
      | Sum.inr _ => -X (Sum.inr ())) = _
    cases he : rowIndex s k with
    | inl i =>
      have he' : (rowEquiv s k).val = Sum.inl i := he
      simp [g,he']
    | inr i => simp [bp]
  have hsolve : (certificateMatrix P c).map (eval bp) *ᵥ x =
      fun k => eval bp (certificateRhs c k) := by
    rw [hM]
    ext k
    rw [hR]
    have hi := (rowEquiv s k).property
    obtain ⟨l,_,hl⟩ := mem_image.mp hi
    change U (rowIndex s k) ⬝ᵥ x = _
    have hl' : j l = rowIndex s k := hl
    simpa only [hl'] using hact l
  refine ⟨c,bp,fun i => ?_⟩
  have hd : ((certificateMatrix P c).map (eval bp)).det ≠ 0 := by
    rw [hM]
    exact hdetU
  have he := eval_reconstructedScore_eq (certificateMatrix P c) (certificateRhs c)
    (fun k => rename Sum.inl (P i k)) bp x hd hsolve
  have he' : eval bp (certificateScore P c i) =
      ((certificateMatrix P c).map (eval bp)).det ^ 2 * (A i ⬝ᵥ x) := by
    simpa [certificateScore, bp, eval_rename, A] using he
  have hp : 0 < ((certificateMatrix P c).map (eval bp)).det ^ 2 := sq_pos_of_ne_zero hd
  rw [he']
  have hi := hx i
  cases hfi : f i <;> simp only [hfi, Bool.false_eq_true, ↓reduceIte] at hi ⊢
  · exact mul_neg_of_pos_of_neg hp hi
  · exact mul_pos hp hi


omit [DecidableEq κ] in
/-- The finite partially linear polynomial capacity bound. Arbitrary linear coefficients
are replaced by an unordered active-row subset, selected labels, and one box variable. -/
theorem card_patterns_le [Fintype ν] (P : Matrix ι κ (MvPolynomial ν ℝ))
    {D : ℕ} (hP : ∀ i j, (P i j).totalDegree ≤ D)
    (hκ : 0 < Fintype.card κ) (hν : Fintype.card ν + 1 ≤ Fintype.card ι) :
    ((patterns P).ncard : ℝ) ≤
      ((Fintype.card ι + 2 * Fintype.card κ).choose (Fintype.card κ) : ℝ) *
      2 ^ Fintype.card κ *
      (4 * Real.exp 1 * (2 * D * Fintype.card κ + 1) * Fintype.card ι /
        (Fintype.card ν + 1)) ^ (Fintype.card ν + 1) := by
  classical
  let F (c : Certificate ι κ) := strictPolynomialSignPatterns (certificateScore P c)
  have hcover : patterns P ⊆ ⋃ c, F c := by
    intro f hf
    obtain ⟨c,hc⟩ := exists_certificate_pattern P hf
    exact Set.mem_iUnion.mpr ⟨c,hc⟩
  have hc : (patterns P).ncard ≤ ∑ c : Certificate ι κ, (F c).ncard :=
    (Set.ncard_le_ncard hcover (Set.toFinite _)).trans (Set.ncard_iUnion_le_of_fintype F)
  have hwr (c : Certificate ι κ) :
      ((F c).ncard : ℝ) ≤
        (4 * Real.exp 1 * (2 * D * Fintype.card κ + 1) * Fintype.card ι /
          (Fintype.card ν + 1)) ^ (Fintype.card ν + 1) := by
    have h := strictPolynomialSignPatterns_card_le
      (show 0 < 2 * D * Fintype.card κ + 1 by omega)
      (show 0 < Fintype.card (ν ⊕ Unit) by simp)
      (show Fintype.card (ν ⊕ Unit) ≤ Fintype.card ι by simpa using hν)
      (certificateScore P c) (certificateScore_totalDegree_le P hP hκ c)
    simpa [F] using h
  have hcr : ((patterns P).ncard : ℝ) ≤ ∑ c : Certificate ι κ, ((F c).ncard : ℝ) := by
    exact_mod_cast hc
  refine hcr.trans ((sum_le_sum (fun c _ => hwr c)).trans ?_)
  simp only [sum_const, card_univ, nsmul_eq_mul, card_certificate]
  push_cast
  ring_nf
  exact le_rfl

end HeadComplexity.PartialLinearCapacity
