import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

set_option linter.style.header false

/-!
Weighted support-degree bounds for multivariate polynomials. The weights may
be zero in this algebraic API; applications to weighted root counts require
strictly positive weights separately.
-/

noncomputable section
namespace HeadComplexity.PolynomialRootCount
open MvPolynomial
open scoped BigOperators Pointwise

variable {K R : Type*} [Fintype K] [CommSemiring R]

def monomialWeight (w : K → ℕ) (m : K →₀ ℕ) : ℕ := ∑ i, w i * m i

def WeightedDegreeLE (w : K → ℕ) (P : MvPolynomial K R) (D : ℕ) : Prop :=
  ∀ m ∈ P.support, monomialWeight w m ≤ D

@[simp] theorem monomialWeight_zero (w : K → ℕ) : monomialWeight w 0 = 0 := by
  simp [monomialWeight]

@[simp] theorem monomialWeight_add (w : K → ℕ) (m s : K →₀ ℕ) :
    monomialWeight w (m + s) = monomialWeight w m + monomialWeight w s := by
  simp [monomialWeight, mul_add, Finset.sum_add_distrib]

@[simp] theorem monomialWeight_single (w : K → ℕ) (i : K) (k : ℕ) :
    monomialWeight w (Finsupp.single i k) = w i * k := by
  classical
  simp [monomialWeight, Finsupp.single_apply, mul_ite]

theorem monomialWeight_eq_finsupp_sum (w : K → ℕ) (m : K →₀ ℕ) :
    monomialWeight w m = m.sum (fun i k => w i * k) := by
  exact (m.sum_fintype (fun i k => w i * k) (by simp)).symm

theorem weightedDegreeLE_zero (w : K → ℕ) (D : ℕ) :
    WeightedDegreeLE w (0 : MvPolynomial K R) D := by
  simp [WeightedDegreeLE]

theorem weightedDegreeLE_C (w : K → ℕ) (c : R) :
    WeightedDegreeLE w (C c) 0 := by
  classical
  intro m hm
  have hm' := support_monomial_subset (s := (0 : K →₀ ℕ)) (a := c) hm
  have hm0 : m = 0 := Finset.mem_singleton.mp hm'
  simp [hm0]

theorem weightedDegreeLE_monomial (w : K → ℕ) (m : K →₀ ℕ) (c : R) :
    WeightedDegreeLE w (monomial m c) (monomialWeight w m) := by
  classical
  intro s hs
  have hsm : s = m := Finset.mem_singleton.mp (support_monomial_subset hs)
  simp [hsm]

theorem weightedDegreeLE_X (w : K → ℕ) (i : K) :
    WeightedDegreeLE w (X i : MvPolynomial K R) (w i) := by
  simpa [X] using weightedDegreeLE_monomial w (Finsupp.single i 1) (1 : R)

theorem weightedDegreeLE_mono {w : K → ℕ} {P : MvPolynomial K R} {D E : ℕ}
    (hP : WeightedDegreeLE w P D) (hDE : D ≤ E) : WeightedDegreeLE w P E :=
  fun m hm => (hP m hm).trans hDE

theorem weightedDegreeLE_add {w : K → ℕ} {P Q : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (hQ : WeightedDegreeLE w Q D) :
    WeightedDegreeLE w (P + Q) D := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hP m h
  · exact hQ m h

theorem weightedDegreeLE_mul {w : K → ℕ} {P Q : MvPolynomial K R} {D E : ℕ}
    (hP : WeightedDegreeLE w P D) (hQ : WeightedDegreeLE w Q E) :
    WeightedDegreeLE w (P * Q) (D + E) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  simpa only [monomialWeight_add] using Nat.add_le_add (hP a ha) (hQ b hb)

theorem weightedDegreeLE_pow {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (k : ℕ) : WeightedDegreeLE w (P ^ k) (D * k) := by
  induction k with
  | zero => simpa using weightedDegreeLE_C w (1 : R)
  | succ k ih =>
      simpa [pow_succ, Nat.mul_succ] using weightedDegreeLE_mul ih hP

theorem weightedDegreeLE_sq {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) : WeightedDegreeLE w (P ^ 2) (2 * D) := by
  simpa [Nat.mul_comm] using weightedDegreeLE_pow hP 2

theorem weightedDegreeLE_C_mul {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (c : R) (hP : WeightedDegreeLE w P D) : WeightedDegreeLE w (C c * P) D := by
  simpa using weightedDegreeLE_mul (weightedDegreeLE_C w c) hP

theorem weightedDegreeLE_sum {ι : Type*} (s : Finset ι)
    {w : K → ℕ} {P : ι → MvPolynomial K R} {D : ℕ}
    (hP : ∀ i ∈ s, WeightedDegreeLE w (P i) D) :
    WeightedDegreeLE w (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedDegreeLE_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact weightedDegreeLE_add (hP i (by simp))
        (ih (fun j hj => hP j (by simp [hj])))

theorem weightedDegreeLE_prod {ι : Type*} (s : Finset ι)
    {w : K → ℕ} {P : ι → MvPolynomial K R} {D : ι → ℕ}
    (hP : ∀ i ∈ s, WeightedDegreeLE w (P i) (D i)) :
    WeightedDegreeLE w (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedDegreeLE_C w (1 : R)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact weightedDegreeLE_mul (hP i (by simp))
        (ih (fun j hj => hP j (by simp [hj])))

theorem weightedDegreeLE_pderiv {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (i : K) :
    WeightedDegreeLE w (pderiv i P) (D - w i) := by
  classical
  intro m hm
  have hcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro hzero
    have hnonzero := mem_support_iff.mp hm
    rw [coeff_pderiv, hzero, zero_mul] at hnonzero
    exact hnonzero rfl
  have h := hP _ (mem_support_iff.mpr hcoeff)
  simp only [monomialWeight_add, monomialWeight_single, mul_one] at h
  omega

theorem weightedDegreeLE_one_iff {P : MvPolynomial K R} {D : ℕ} :
    WeightedDegreeLE (fun _ : K => 1) P D ↔ P.totalDegree ≤ D := by
  classical
  simp only [WeightedDegreeLE, totalDegree, Finset.sup_le_iff,
    monomialWeight_eq_finsupp_sum, one_mul]

theorem weightedDegreeLE_of_totalDegree_le {w : K → ℕ}
    {P : MvPolynomial K R} {D W : ℕ}
    (hP : P.totalDegree ≤ D) (hw : ∀ i, w i ≤ W) :
    WeightedDegreeLE w P (W * D) := by
  classical
  intro m hm
  have hmdeg : (∑ i, m i) ≤ D := by
    have he : m.sum (fun _ k => k) = ∑ i, m i :=
      m.sum_fintype (fun _ k => k) (by simp)
    exact he ▸ (le_totalDegree hm).trans hP
  calc
    monomialWeight w m = ∑ i, w i * m i := rfl
    _ ≤ ∑ i, W * m i := Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hw i)
    _ = W * ∑ i, m i := (Finset.mul_sum _ _ _).symm
    _ ≤ W * D := Nat.mul_le_mul_left W hmdeg

theorem weightedDegreeLE_totalDegree_le {w : K → ℕ}
    {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (hw : ∀ i, 0 < w i) : P.totalDegree ≤ D := by
  apply weightedDegreeLE_one_iff.mp
  intro m hm
  apply le_trans _ (hP m hm)
  unfold monomialWeight
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hw i)

/-- Substitution does not increase weighted degree when each variable is
replaced by a polynomial whose target weighted degree is at most its weight. -/
theorem weightedDegreeLE_eval₂Hom {L : Type*} [Fintype L]
    {w : K → ℕ} {v : L → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (Q : K → MvPolynomial L R)
    (hQ : ∀ i, WeightedDegreeLE v (Q i) (w i)) :
    WeightedDegreeLE v (eval₂Hom C Q P) D := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff P, map_sum]
  apply weightedDegreeLE_sum P.support
  intro m hm
  rw [eval₂Hom_monomial]
  have hprod : WeightedDegreeLE v (m.prod fun i k => Q i ^ k) (monomialWeight w m) := by
    rw [monomialWeight_eq_finsupp_sum]
    exact weightedDegreeLE_prod m.support (fun i _ => weightedDegreeLE_pow (hQ i) (m i))
  exact weightedDegreeLE_mono (weightedDegreeLE_C_mul _ hprod) (hP m hm)

theorem weightedDegreeLE_translate {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (c : K → R) :
    WeightedDegreeLE w (eval₂Hom C (fun i => X i + C (c i)) P) D := by
  apply weightedDegreeLE_eval₂Hom hP
  intro i
  exact weightedDegreeLE_add (weightedDegreeLE_X w i)
    (weightedDegreeLE_mono (weightedDegreeLE_C w (c i)) (Nat.zero_le _))

theorem weightedDegreeLE_map {S : Type*} [CommSemiring S]
    {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (f : R →+* S) :
    WeightedDegreeLE w (map f P) D := by
  intro m hm
  exact hP m (support_map_subset f P hm)

theorem weightedDegreeLE_rename {L : Type*} [Fintype L]
    {w : K → ℕ} {v : L → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (f : K → L) (hf : ∀ i, v (f i) ≤ w i) :
    WeightedDegreeLE v (rename f P) D := by
  have h := weightedDegreeLE_eval₂Hom hP (fun i => (X (f i) : MvPolynomial L R))
    (fun i => weightedDegreeLE_mono (weightedDegreeLE_X v (f i)) (hf i))
  simpa only [rename_eq_aeval, aeval_def, Function.comp_def, algebraMap_eq,
    coe_eval₂Hom] using h

/-- Substituting the weight-th power for each variable turns a weighted-degree
bound into an ordinary total-degree bound. -/
theorem totalDegree_powerSubstitution_le {w : K → ℕ} {P : MvPolynomial K R} {D : ℕ}
    (hP : WeightedDegreeLE w P D) :
    (eval₂Hom C (fun i => (X i : MvPolynomial K R) ^ w i) P).totalDegree ≤ D := by
  apply weightedDegreeLE_one_iff.mp
  apply weightedDegreeLE_eval₂Hom hP
  intro i
  simpa using weightedDegreeLE_pow (weightedDegreeLE_X (fun _ => 1) i) (w i)

section Ring
variable {A : Type*} [CommRing A]

theorem weightedDegreeLE_neg {w : K → ℕ} {P : MvPolynomial K A} {D : ℕ}
    (hP : WeightedDegreeLE w P D) : WeightedDegreeLE w (-P) D := by
  intro m hm
  exact hP m (by simpa using hm)

theorem weightedDegreeLE_sub {w : K → ℕ} {P Q : MvPolynomial K A} {D : ℕ}
    (hP : WeightedDegreeLE w P D) (hQ : WeightedDegreeLE w Q D) :
    WeightedDegreeLE w (P - Q) D := by
  simpa [sub_eq_add_neg] using weightedDegreeLE_add hP (weightedDegreeLE_neg hQ)

end Ring
end HeadComplexity.PolynomialRootCount
