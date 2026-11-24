import HeadComplexity.Research.FilteredAlgebraCapacity
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Algebra.MvPolynomial

set_option linter.style.header false
set_option maxRecDepth 2000
set_option linter.style.whitespace false

/-!
A polynomial chart for split smoothable filtered reciprocal clusters. Matrix
transport supplies the multiplication constants; even determinant powers
clear its denominators without changing any strict sign. This chart does not
assert access from arbitrary original xorformer truth tables.
-/

noncomputable section
namespace HeadComplexity.SplitSmoothableCapacity
open MvPolynomial PolynomialRootCount
open scoped BigOperators

abbrev Parameter (n G q : ℕ) := Unit ⊕
  (Fin G × ((Bool × Option (Fin q) × Option (Fin n)) ⊕ (Fin (q+1) × Fin (q+1))))

@[simp] theorem card_parameter (n G q : ℕ) :
    Fintype.card (Parameter n G q) = 1 + 2 * (n+1) * (G*(q+1)) + G*(q+1)^2 := by
  simp [Parameter]
  ring

def weight (n G q : ℕ) (k : Fin G → Fin q → ℕ) : Parameter n G q → ℕ
  | Sum.inl _ => G*(q+1)
  | Sum.inr (_, Sum.inl (false, none, _)) => 1
  | Sum.inr (_, Sum.inl (true, none, _)) => G*(q+1)
  | Sum.inr (g, Sum.inl (false, some i, _)) => G*k g i+1
  | Sum.inr (g, Sum.inl (true, some i, _)) => G*(q+1-k g i)
  | Sum.inr (_, Sum.inr _) => 1

variable {n G q : ℕ}

def affinePoly (kind : Bool) (g : Fin G) (i : Option (Fin q)) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inr (g, Sum.inl (kind,i,none))) +
    ∑ a, C (boolToReal (x a)) * X (Sum.inr (g, Sum.inl (kind,i,some a)))

def matrixPoly (g : Fin G) : Matrix (Fin (q+1)) (Fin (q+1)) (MvPolynomial (Parameter n G q) ℝ) :=
  fun i j => X (Sum.inr (g, Sum.inr (i,j)))

def determinantPoly (g : Fin G) : MvPolynomial (Parameter n G q) ℝ := (matrixPoly g).det

def structureNumerator (g : Fin G) (i j l : Fin q) : MvPolynomial (Parameter n G q) ℝ :=
  ∑ a : Fin (q+1), (matrixPoly g).adjugate l.succ a * matrixPoly g a i.succ * matrixPoly g a j.succ

theorem affinePoly_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (kind : Bool) (g : Fin G) (i : Option (Fin q)) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (affinePoly kind g i x)
      (weight n G q k (Sum.inr (g, Sum.inl (kind,i,none)))) := by
  unfold affinePoly
  apply weightedDegreeLE_add (weightedDegreeLE_X _ _)
  apply weightedDegreeLE_sum Finset.univ
  intro a _
  apply weightedDegreeLE_C_mul
  cases kind <;> cases i <;> exact weightedDegreeLE_X _ _

theorem determinant_weightedDegreeLE {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (w : σ → ℕ) (M : Matrix ι ι (MvPolynomial σ ℝ)) (D : ℕ)
    (hM : ∀ i j, WeightedDegreeLE w (M i j) D) :
    WeightedDegreeLE w M.det (Fintype.card ι * D) := by
  classical
  rw [Matrix.det_apply']
  apply weightedDegreeLE_sum Finset.univ
  intro s _
  have hprod := weightedDegreeLE_prod Finset.univ (fun i _ => hM (s i) i)
  have hc := weightedDegreeLE_C_mul ((Equiv.Perm.sign s : ℤ) : ℝ) hprod
  simpa only [map_intCast, Finset.sum_const, Finset.card_univ, smul_eq_mul] using hc

theorem determinantPoly_weightedDegreeLE (k : Fin G → Fin q → ℕ) (g : Fin G) :
    WeightedDegreeLE (weight n G q k) (determinantPoly g) (q+1) := by
  simpa [determinantPoly] using determinant_weightedDegreeLE (weight n G q k)
    (matrixPoly (n := n) g) 1 (fun i j => weightedDegreeLE_X _ _)

theorem adjugate_weightedDegreeLE (k : Fin G → Fin q → ℕ) (g : Fin G)
    (i j : Fin (q+1)) :
    WeightedDegreeLE (weight n G q k) ((matrixPoly g).adjugate i j) q := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hh := determinant_weightedDegreeLE (weight n G q k)
    ((matrixPoly (n := n) g).submatrix j.succAbove i.succAbove) 1
    (fun a b => weightedDegreeLE_X _ _)
  have hc := weightedDegreeLE_C_mul ((-1 : ℝ) ^ ((j : ℕ) + (i : ℕ))) hh
  simpa only [map_pow, map_neg, map_one, Fintype.card_fin, mul_one] using hc

theorem structureNumerator_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (g : Fin G) (i j l : Fin q) :
    WeightedDegreeLE (weight n G q k) (structureNumerator g i j l) (q+2) := by
  unfold structureNumerator
  apply weightedDegreeLE_sum Finset.univ
  intro a _
  have hi : WeightedDegreeLE (weight n G q k) (matrixPoly g a i.succ) 1 := weightedDegreeLE_X _ _
  have hj : WeightedDegreeLE (weight n G q k) (matrixPoly g a j.succ) 1 := weightedDegreeLE_X _ _
  simpa [Nat.add_assoc] using weightedDegreeLE_mul (weightedDegreeLE_mul
    (adjugate_weightedDegreeLE k g l.succ a) hi) hj


/-- The numerator of the coordinate of U^(m+1), with determinant^m removed. -/
def powerNumerator (k : Fin G → Fin q → ℕ) (g : Fin G) (x : Fin n → Bool) :
    ℕ → Fin q → MvPolynomial (Parameter n G q) ℝ
  | 0, l => affinePoly false g (some l) x
  | m+1, l => ∑ i : Fin q, ∑ j : Fin q,
      if k g i + k g j ≤ k g l then
        affinePoly false g (some i) x * powerNumerator k g x m j * structureNumerator g i j l
      else 0

theorem powerNumerator_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (g : Fin G) (x : Fin n → Bool) (m : ℕ) (l : Fin q) :
    WeightedDegreeLE (weight n G q k) (powerNumerator k g x m l)
      (G*k g l + 1 + m*(q+3)) := by
  induction m generalizing l with
  | zero => simpa [powerNumerator, weight] using affinePoly_weightedDegreeLE k false g (some l) x
  | succ m ih =>
    rw [powerNumerator]
    apply weightedDegreeLE_sum Finset.univ
    intro i _
    apply weightedDegreeLE_sum Finset.univ
    intro j _
    split
    · rename_i hij
      have hA : WeightedDegreeLE (weight n G q k) (affinePoly false g (some i) x)
          (G*k g i+1) := affinePoly_weightedDegreeLE k false g (some i) x
      apply weightedDegreeLE_mono (weightedDegreeLE_mul
        (weightedDegreeLE_mul hA (ih j)) (structureNumerator_weightedDegreeLE k g i j l))
      nlinarith [Nat.mul_le_mul_left G hij]
    · exact weightedDegreeLE_zero _ _

def clusterNumerator (k : Fin G → Fin q → ℕ) (g : Fin G) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  affinePoly true g none x * affinePoly false g none x ^ q * determinantPoly g ^ (2*(q+1)) +
    ∑ m : Fin q, ∑ l : Fin q,
      C ((-1 : ℝ)^((m : ℕ)+1)) * affinePoly true g (some l) x *
        powerNumerator k g x m l * affinePoly false g none x ^ (q-m-1) *
          determinantPoly g ^ (2*(q+1)-m)

def clearingFactor (g : Fin G) (x : Fin n → Bool) : MvPolynomial (Parameter n G q) ℝ :=
  affinePoly false g none x ^ (q+1) * determinantPoly g ^ (2*(q+1))

def clearingPoly (x : Fin n → Bool) : MvPolynomial (Parameter n G q) ℝ :=
  ∏ g : Fin G, clearingFactor g x

def scorePoly (k : Fin G → Fin q → ℕ) (x : Fin n → Bool) :
    MvPolynomial (Parameter n G q) ℝ :=
  X (Sum.inl ()) * clearingPoly x +
    ∑ g : Fin G, clusterNumerator k g x * ∏ h ∈ Finset.univ.erase g, clearingFactor h x

theorem clusterNumerator_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (hk : ∀ g i, k g i ≤ q) (g : Fin G) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (clusterNumerator k g x)
      (G*(q+1)+2*q+2*(q+1)^2) := by
  have hB : WeightedDegreeLE (weight n G q k) (affinePoly false g none x) 1 :=
    affinePoly_weightedDegreeLE k false g none x
  have hD := determinantPoly_weightedDegreeLE (n := n) k g
  unfold clusterNumerator
  apply weightedDegreeLE_add
  · have hA : WeightedDegreeLE (weight n G q k) (affinePoly true g none x) (G*(q+1)) :=
      affinePoly_weightedDegreeLE k true g none x
    apply weightedDegreeLE_mono (weightedDegreeLE_mul
      (weightedDegreeLE_mul hA (weightedDegreeLE_pow hB q))
      (weightedDegreeLE_pow hD (2*(q+1))))
    simp only [one_mul]
    nlinarith
  · apply weightedDegreeLE_sum Finset.univ
    intro m _
    apply weightedDegreeLE_sum Finset.univ
    intro l _
    have hA : WeightedDegreeLE (weight n G q k) (affinePoly true g (some l) x)
        (G*(q+1-k g l)) := affinePoly_weightedDegreeLE k true g (some l) x
    apply weightedDegreeLE_mono (weightedDegreeLE_mul (weightedDegreeLE_mul
      (weightedDegreeLE_mul (weightedDegreeLE_C_mul _ hA)
        (powerNumerator_weightedDegreeLE k g x m l))
      (weightedDegreeLE_pow hB (q-m-1)))
      (weightedDegreeLE_pow hD (2*(q+1)-m)))
    simp only [one_mul]
    have he : q+1-k g l+k g l=q+1 := by have := hk g l; omega
    have heq : G*(q+1-k g l)+G*k g l=G*(q+1) := by nlinarith [congrArg (fun a => G*a) he]
    have hm := m.isLt
    have hqm : q-m-1+m+1=q := by omega
    have hdm : 2*(q+1)-m+m=2*(q+1) := by omega
    nlinarith [congrArg (fun a => (q+1)*a) hdm]

theorem clearingFactor_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (g : Fin G) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (clearingFactor g x) (q+1+2*(q+1)^2) := by
  have hh := weightedDegreeLE_mul (weightedDegreeLE_pow
    (affinePoly_weightedDegreeLE k false g none x) (q+1))
    (weightedDegreeLE_pow (determinantPoly_weightedDegreeLE k g) (2*(q+1)))
  convert hh using 1 <;> simp [clearingFactor, weight]
  ring

theorem clearingPoly_weightedDegreeLE (k : Fin G → Fin q → ℕ) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (clearingPoly x) (G*(q+1+2*(q+1)^2)) := by
  have hh := weightedDegreeLE_prod Finset.univ (fun g _ => clearingFactor_weightedDegreeLE k g x)
  simpa [clearingPoly] using hh

theorem scorePoly_weightedDegreeLE (k : Fin G → Fin q → ℕ)
    (hk : ∀ g i, k g i ≤ q) (x : Fin n → Bool) :
    WeightedDegreeLE (weight n G q k) (scorePoly k x) ((3+2*(q+1))*(G*(q+1))) := by
  unfold scorePoly
  apply weightedDegreeLE_add
  · apply weightedDegreeLE_mono (weightedDegreeLE_mul
      (weightedDegreeLE_X _ _) (clearingPoly_weightedDegreeLE k x))
    simp only [weight]
    nlinarith
  · apply weightedDegreeLE_sum Finset.univ
    intro g _
    have hprod := weightedDegreeLE_prod (Finset.univ.erase g)
      (fun h _ => clearingFactor_weightedDegreeLE k h x)
    apply weightedDegreeLE_mono (weightedDegreeLE_mul
      (clusterNumerator_weightedDegreeLE k hk g x) hprod)
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ g),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hG : 0 < G := Nat.zero_lt_of_lt g.isLt
    have he : G-1+1=G := by omega
    have heq := congrArg (fun a => a*(q+1+2*(q+1)^2)) he
    have hqG : q ≤ G*(q+1) := by nlinarith
    nlinarith


theorem weight_pos (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q) (i : Parameter n G q) : 0 < weight n G q k i := by
  rcases i with _ | ⟨g, ⟨kind, i, a⟩ | ⟨i,j⟩⟩
  · exact Nat.mul_pos hG (by omega)
  · cases kind <;> cases i <;> simp only [weight]
    · omega
    · omega
    · exact Nat.mul_pos hG (by omega)
    · rename_i i
      exact Nat.mul_pos hG (by have := hk g i; omega)
  · simp [weight]

theorem weight_le (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q) (i : Parameter n G q) :
    weight n G q k i ≤ (3+2*(q+1))*(G*(q+1)) := by
  have hbase : 1 ≤ G*(q+1) := Nat.mul_pos hG (by omega)
  have hscale : G*(q+1) ≤ (3+2*(q+1))*(G*(q+1)) := by nlinarith
  apply le_trans _ hscale
  rcases i with _ | ⟨g, ⟨kind, i, a⟩ | ⟨i,j⟩⟩
  · rfl
  · cases kind <;> cases i <;> simp only [weight]
    · exact hbase
    · rename_i i
      nlinarith [Nat.mul_le_mul_left G (hk g i)]
    · rfl
    · exact Nat.mul_le_mul_left G (Nat.sub_le _ _)
  · exact hbase

def represented (n G q : ℕ) (k : Fin G → Fin q → ℕ) : Set ((Fin n → Bool) → Bool) :=
  strictPolynomialSignPatterns (scorePoly (n := n) k)

theorem card_represented_le (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q)
    (hparameters : 1+2*(n+1)*(G*(q+1))+G*(q+1)^2 ≤ 2^n) :
    ((represented n G q k).ncard : ℝ) ≤
      (4*Real.exp 1*((3+2*(q+1))*(G*(q+1)) : ℕ)*(2 : ℝ)^n /
        (1+2*(n+1)*(G*(q+1))+G*(q+1)^2 : ℕ))^
          (1+2*(n+1)*(G*(q+1))+G*(q+1)^2) /
        ∏ i : Parameter n G q, (weight n G q k i : ℝ) := by
  have hh := weightedStrictPolynomialSignPatterns_card_le
    (show 0 < Fintype.card (Parameter n G q) by simp)
    (show Fintype.card (Parameter n G q) ≤ Fintype.card (Fin n → Bool) by
      simpa only [card_parameter,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
        using hparameters)
    (weight n G q k) (weight_pos k hG hk) (weight_le k hG hk)
    (scorePoly (n := n) k) (scorePoly_weightedDegreeLE k hk)
  simpa only [represented,card_parameter,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat] using hh


/-- The same affine coefficients with multiplication transported by the matrix. -/
def transportedPoint (θ : Parameter n G q → ℝ) :
    FilteredAlgebraCapacity.Parameter n G q → ℝ
  | Sum.inl _ => θ (Sum.inl ())
  | Sum.inr (g, Sum.inl a) => θ (Sum.inr (g, Sum.inl a))
  | Sum.inr (g, Sum.inr (i,j,l)) => eval θ (structureNumerator g i j l) / eval θ (determinantPoly g)

@[simp] theorem eval_affine_transported (θ : Parameter n G q → ℝ)
    (kind : Bool) (g : Fin G) (i : Option (Fin q)) (x : Fin n → Bool) :
    eval (transportedPoint θ) (FilteredAlgebraCapacity.affinePoly kind g i x) =
      eval θ (affinePoly kind g i x) := by
  simp [FilteredAlgebraCapacity.affinePoly,affinePoly,transportedPoint]

@[simp] theorem eval_structure_transported (θ : Parameter n G q → ℝ)
    (g : Fin G) (i j l : Fin q) :
    eval (transportedPoint θ) (FilteredAlgebraCapacity.structurePoly g i j l) =
      eval θ (structureNumerator g i j l) / eval θ (determinantPoly g) := by
  simp [FilteredAlgebraCapacity.structurePoly,transportedPoint]

theorem eval_powerNumerator (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (g : Fin G) (x : Fin n → Bool) (hD : eval θ (determinantPoly g) ≠ 0)
    (m : ℕ) (l : Fin q) :
    eval θ (powerNumerator k g x m l) =
      eval (transportedPoint θ) (FilteredAlgebraCapacity.nilpotentPower k g x m l) *
        eval θ (determinantPoly g)^m := by
  induction m generalizing l with
  | zero => simp [powerNumerator,FilteredAlgebraCapacity.nilpotentPower]
  | succ m ih =>
    simp only [powerNumerator,FilteredAlgebraCapacity.nilpotentPower,map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split
    · simp only [map_mul,eval_affine_transported,eval_structure_transported,ih]
      rw [pow_succ]
      field_simp
    · simp

theorem eval_clusterNumerator (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (g : Fin G) (x : Fin n → Bool) (hD : eval θ (determinantPoly g) ≠ 0) :
    eval θ (clusterNumerator k g x) =
      eval (transportedPoint θ) (FilteredAlgebraCapacity.clusterNumerator k g x) *
        eval θ (determinantPoly g)^(2*(q+1)) := by
  simp only [clusterNumerator,FilteredAlgebraCapacity.clusterNumerator,map_add,map_mul,
    map_pow,map_sum,eval_C,eval_affine_transported,add_mul,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro l _
  rw [eval_powerNumerator k θ g x hD]
  have he : (m : ℕ)+(2*(q+1)-m)=2*(q+1) := by have := m.isLt; omega
  calc
    _ = ((-1 : ℝ)^((m : ℕ)+1) * eval θ (affinePoly true g (some l) x) *
      eval (transportedPoint θ) (FilteredAlgebraCapacity.nilpotentPower k g x m l) *
      eval θ (affinePoly false g none x)^(q-m-1)) *
      (eval θ (determinantPoly g)^((m : ℕ)+(2*(q+1)-m))) := by rw [pow_add]; ring
    _ = _ := by rw [he]

def determinantClearing (θ : Parameter n G q → ℝ) : ℝ :=
  ∏ g : Fin G, eval θ (determinantPoly g)^(2*(q+1))

theorem determinantClearing_pos (θ : Parameter n G q → ℝ)
    (hD : ∀ g, eval θ (determinantPoly g) ≠ 0) : 0 < determinantClearing θ := by
  apply Finset.prod_pos
  intro g _
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero (hD g)) _


theorem eval_clearingPoly (θ : Parameter n G q → ℝ) (x : Fin n → Bool) :
    eval θ (clearingPoly x) =
      eval (transportedPoint θ) (FilteredAlgebraCapacity.clearingPoly x) *
        determinantClearing θ := by
  simp [clearingPoly,clearingFactor,FilteredAlgebraCapacity.clearingPoly,
    determinantClearing,Finset.prod_mul_distrib]

theorem eval_scorePoly (k : Fin G → Fin q → ℕ) (θ : Parameter n G q → ℝ)
    (x : Fin n → Bool) (hD : ∀ g, eval θ (determinantPoly g) ≠ 0) :
    eval θ (scorePoly k x) =
      eval (transportedPoint θ) (FilteredAlgebraCapacity.scorePoly k x) *
        determinantClearing θ := by
  simp only [scorePoly,map_add,map_mul,map_sum,map_prod,eval_X]
  rw [eval_clearingPoly]
  simp only [FilteredAlgebraCapacity.scorePoly,map_add,map_mul,map_sum,map_prod,map_pow,
    eval_X,transportedPoint,add_mul,Finset.sum_mul,eval_affine_transported]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro g _
    rw [eval_clusterNumerator k θ g x (hD g)]
    simp only [clearingFactor,map_mul,map_pow,Finset.prod_mul_distrib]
    have he := Finset.mul_prod_erase Finset.univ
      (fun h : Fin G => eval θ (determinantPoly h)^(2*(q+1))) (Finset.mem_univ g)
    unfold determinantClearing
    rw [←he]
    ring

theorem mem_represented_of_transported (k : Fin G → Fin q → ℕ)
    (θ : Parameter n G q → ℝ) (f : (Fin n → Bool) → Bool)
    (hD : ∀ g, eval θ (determinantPoly g) ≠ 0)
    (hf : ∀ x, if f x then
      0 < eval (transportedPoint θ) (FilteredAlgebraCapacity.scorePoly k x) else
      eval (transportedPoint θ) (FilteredAlgebraCapacity.scorePoly k x) < 0) :
    f ∈ represented n G q k := by
  refine ⟨θ,fun x => ?_⟩
  rw [eval_scorePoly k θ x hD]
  have hpos := determinantClearing_pos θ hD
  have hx := hf x
  cases hfval : f x
  · simp only [hfval,Bool.false_eq_true,↓reduceIte] at hx ⊢
    exact mul_neg_of_neg_of_pos hx hpos
  · simp only [hfval,↓reduceIte] at hx ⊢
    exact mul_pos hx hpos


/-- This is an explicit real split orbit; its closure is in the real topology. -/
def splitOrbit (n G q : ℕ) : Set (FilteredAlgebraCapacity.Parameter n G q → ℝ) :=
  {η | ∃ θ : Parameter n G q → ℝ,
    (∀ g, eval θ (determinantPoly g) ≠ 0) ∧ transportedPoint θ = η}

theorem mem_represented_of_closure (k : Fin G → Fin q → ℕ)
    (η : FilteredAlgebraCapacity.Parameter n G q → ℝ) (f : (Fin n → Bool) → Bool)
    (hη : η ∈ closure (splitOrbit n G q))
    (hf : ∀ x, if f x then 0 < eval η (FilteredAlgebraCapacity.scorePoly k x) else
      eval η (FilteredAlgebraCapacity.scorePoly k x) < 0) :
    f ∈ represented n G q k := by
  let U : Set (FilteredAlgebraCapacity.Parameter n G q → ℝ) :=
    {ζ | ∀ x, if f x then 0 < eval ζ (FilteredAlgebraCapacity.scorePoly k x) else
      eval ζ (FilteredAlgebraCapacity.scorePoly k x) < 0}
  have hU : IsOpen U := by
    change IsOpen {ζ | ∀ x, if f x then
      0 < eval ζ (FilteredAlgebraCapacity.scorePoly k x) else
      eval ζ (FilteredAlgebraCapacity.scorePoly k x) < 0}
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro x
    cases f x
    · simpa using isOpen_lt (MvPolynomial.continuous_eval
        (FilteredAlgebraCapacity.scorePoly k x)) continuous_const
    · simpa using isOpen_lt continuous_const (MvPolynomial.continuous_eval
        (FilteredAlgebraCapacity.scorePoly k x))
  obtain ⟨ζ,hζU,hζ⟩ := mem_closure_iff.mp hη U hU hf
  obtain ⟨θ,hD,rfl⟩ := hζ
  exact mem_represented_of_transported k θ f hD hζU

/-- Original reciprocal positivity is only used to clear the base denominators.
All cluster tensors may lie on the boundary of the real split orbit. -/
theorem mem_represented_of_closure_score (k : Fin G → Fin q → ℕ)
    (η : FilteredAlgebraCapacity.Parameter n G q → ℝ) (f : (Fin n → Bool) → Bool)
    (hη : η ∈ closure (splitOrbit n G q))
    (hB : ∀ x g, 0 < eval η (FilteredAlgebraCapacity.affinePoly false g none x))
    (hf : ∀ x, if f x then 0 < FilteredAlgebraCapacity.score k η x else
      FilteredAlgebraCapacity.score k η x < 0) :
    f ∈ represented n G q k := by
  apply mem_represented_of_closure k η f hη
  intro x
  rw [FilteredAlgebraCapacity.eval_scorePoly k η x (fun g => (hB x g).ne')]
  have hpos := FilteredAlgebraCapacity.eval_clearingPoly_pos η x (hB x)
  have hx := hf x
  cases hfval : f x
  · simp only [hfval,Bool.false_eq_true,↓reduceIte] at hx ⊢
    exact mul_neg_of_neg_of_pos hx hpos
  · simp only [hfval,↓reduceIte] at hx ⊢
    exact mul_pos hx hpos


def smoothableFunctions (n G q : ℕ) (k : Fin G → Fin q → ℕ) :
    Set ((Fin n → Bool) → Bool) :=
  {f | ∃ η : FilteredAlgebraCapacity.Parameter n G q → ℝ,
    η ∈ closure (splitOrbit n G q) ∧
    (∀ x g, 0 < eval η (FilteredAlgebraCapacity.affinePoly false g none x)) ∧
    (∀ x, if f x then 0 < FilteredAlgebraCapacity.score k η x else
      FilteredAlgebraCapacity.score k η x < 0)}

theorem smoothableFunctions_subset_represented (k : Fin G → Fin q → ℕ) :
    smoothableFunctions n G q k ⊆ represented n G q k := by
  rintro f ⟨η,hη,hB,hf⟩
  exact mem_represented_of_closure_score k η f hη hB hf

theorem card_smoothableFunctions_le (k : Fin G → Fin q → ℕ) (hG : 0 < G)
    (hk : ∀ g i, k g i ≤ q)
    (hparameters : 1+2*(n+1)*(G*(q+1))+G*(q+1)^2 ≤ 2^n) :
    ((smoothableFunctions n G q k).ncard : ℝ) ≤
      (4*Real.exp 1*((3+2*(q+1))*(G*(q+1)) : ℕ)*(2 : ℝ)^n /
        (1+2*(n+1)*(G*(q+1))+G*(q+1)^2 : ℕ))^
          (1+2*(n+1)*(G*(q+1))+G*(q+1)^2) /
        ∏ i : Parameter n G q, (weight n G q k i : ℝ) := by
  apply le_trans _ (card_represented_le k hG hk hparameters)
  exact_mod_cast Set.ncard_le_ncard (smoothableFunctions_subset_represented k)

end HeadComplexity.SplitSmoothableCapacity
