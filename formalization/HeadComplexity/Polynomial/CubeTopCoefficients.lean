import HeadComplexity.Polynomial.MeanGridCubic

set_option linter.style.header false

/-!
# Highest squarefree coefficients are determined by spin-cube values

Finite Walsh averaging isolates a squarefree coefficient whenever the total
degree is at most the size of its support. Consequently the cubic mean-grid
polynomial retains exactly the raw cubic coefficients on three distinct groups.
-/

namespace HeadComplexity.CubeTopCoefficients

noncomputable section

open Finset MvPolynomial MeanGridCubic MeanGridSymmetrization
open scoped BigOperators

variable {α : Type*} [Fintype α]

def exponent (S : Finset α) : α →₀ ℕ := ∑ p ∈ S, Finsupp.single p 1

omit [Fintype α] in
open Classical in
theorem exponent_apply (S : Finset α) (p : α) :
    exponent S p = if p ∈ S then 1 else 0 := by
  classical
  simp [exponent, Finsupp.single_apply]

theorem exponent_sum (S : Finset α) : (∑ p, exponent S p) = S.card := by
  classical
  simp [exponent_apply]

omit [Fintype α] in
theorem mem_oddSupport (d : α →₀ ℕ) (p : α) :
    p ∈ oddSupport d ↔ d p % 2 = 1 := by
  classical
  simp only [oddSupport, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro he
    simp [he] at h

omit [Fintype α] in
theorem oddSupport_exponent (S : Finset α) : oddSupport (exponent S) = S := by
  classical
  ext p
  rw [mem_oddSupport, exponent_apply]
  by_cases h : p ∈ S <;> simp [h]

omit [Fintype α] in
theorem exponent_le_of_oddSupport (S : Finset α) (d : α →₀ ℕ)
    (hd : oddSupport d = S) (p : α) : exponent S p ≤ d p := by
  classical
  rw [exponent_apply]
  by_cases hp : p ∈ S
  · rw [if_pos hp]
    have hm : d p % 2 = 1 := (mem_oddSupport d p).mp (hd.symm ▸ hp)
    omega
  · simp [hp]

omit [Fintype α] in
theorem eq_exponent_of_top_support [Finite α] (S : Finset α) (d : α →₀ ℕ)
    (hd : d.sum (fun _ e ↦ e) ≤ S.card) (hs : oddSupport d = S) : d = exponent S := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hsumd : (∑ p, d p) ≤ S.card := by
    rwa [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)] at hd
  have hle (p : α) (_ : p ∈ Finset.univ) : exponent S p ≤ d p :=
    exponent_le_of_oddSupport S d hs p
  have he : (∑ p, exponent S p) = ∑ p, d p := by
    have hh := Finset.sum_le_sum hle
    rw [exponent_sum] at hh ⊢
    omega
  have hp := (Finset.sum_eq_sum_iff_of_le hle).mp he
  ext p
  exact (hp p (Finset.mem_univ p)).symm

def character (S : Finset α) (x : α → Bool) : ℝ := ∏ p ∈ S, spin x p

open Classical in
def fourier (P : MvPolynomial α ℝ) (S : Finset α) : ℝ :=
  average (fun x : α → Bool ↦ character S x * eval (spin x) P)

open Classical in
theorem character_univ (S : Finset α) (x : α → Bool) :
    character S x = ∏ p : α, if p ∈ S then spin x p else 1 := by
  classical
  rw [← Finset.prod_filter]
  simp [character]

theorem spin_pair_average (d : ℕ) (b : Prop) [Decidable b] :
    average (fun x : Bool ↦
      (if b then (if x then 1 else -1 : ℝ) else 1) * (if x then 1 else -1 : ℝ) ^ d) =
        if (d % 2 = 1 ↔ b) then 1 else 0 := by
  classical
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · have hp : (-1 : ℝ) ^ d = 1 := by
      rw [power_on_spin (-1) (by norm_num) d]
      simp [hd]
    by_cases hb : b <;> simp [average, hp, hd, hb]
  · have hp : (-1 : ℝ) ^ d = -1 := by
      rw [power_on_spin (-1) (by norm_num) d]
      simp [hd]
    by_cases hb : b <;> simp [average, hp, hd, hb]

open Classical in
theorem average_character_monomial (S : Finset α) (d : α →₀ ℕ) :
    average (fun x : α → Bool ↦ character S x * ∏ p ∈ d.support, spin x p ^ d p) =
      if oddSupport d = S then 1 else 0 := by
  classical
  have he (x : α → Bool) : (∏ p ∈ d.support, spin x p ^ d p) = ∏ p : α, spin x p ^ d p :=
    Finsupp.prod_fintype d (fun p e ↦ spin x p ^ e) (fun _ ↦ pow_zero _)
  simp_rw [he, character_univ, ← Finset.prod_mul_distrib]
  change average (fun x : α → Bool ↦ ∏ p : α,
    (if p ∈ S then (if x p then 1 else -1 : ℝ) else 1) *
      (if x p then 1 else -1 : ℝ) ^ d p) = _
  rw [average_product (fun p (b : Bool) ↦
    (if p ∈ S then (if b then 1 else -1 : ℝ) else 1) *
      (if b then 1 else -1 : ℝ) ^ d p)]
  simp_rw [spin_pair_average]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, forall_true_left]
  apply propext
  constructor
  · intro h
    ext p
    exact (mem_oddSupport d p).trans (h p)
  · intro h p
    rw [← mem_oddSupport, h]

theorem fourier_eq_top_coefficient (P : MvPolynomial α ℝ) (S : Finset α)
    (hP : P.totalDegree ≤ S.card) : fourier P S = P.coeff (exponent S) := by
  classical
  unfold fourier
  simp_rw [eval_eq, Finset.mul_sum]
  rw [average_finset_sum]
  have he (d : α →₀ ℕ) :
      average (fun x : α → Bool ↦ character S x *
        (P.coeff d * ∏ p ∈ d.support, spin x p ^ d p)) =
          P.coeff d * (if oddSupport d = S then 1 else 0) := by
    have hmul (x : α → Bool) : character S x *
        (P.coeff d * ∏ p ∈ d.support, spin x p ^ d p) =
          P.coeff d * (character S x * ∏ p ∈ d.support, spin x p ^ d p) := by ring
    simp_rw [hmul]
    rw [average_mul, average_character_monomial]
  simp_rw [he]
  have hs (d : α →₀ ℕ) (hd : d ∈ P.support) :
      (oddSupport d = S) ↔ d = exponent S := by
    constructor
    · exact eq_exponent_of_top_support S d ((le_totalDegree hd).trans hP)
    · rintro rfl
      exact oddSupport_exponent S
  calc
    _ = ∑ d ∈ P.support, if d = exponent S then P.coeff d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d = exponent S <;> simp [hs d hd, h, oddSupport_exponent]
    _ = _ := by
      rw [Finset.sum_ite_eq']
      by_cases h : exponent S ∈ P.support
      · simp [h]
      · simp only [h, ↓reduceIte]
        exact (not_ne_iff.mp (fun hc ↦ h (MvPolynomial.mem_support_iff.mpr hc))).symm

omit [Fintype α] in
/-- Equality on the spin cube determines every top-degree squarefree coefficient. -/
theorem top_coefficient_eq_of_cube_eq [Finite α] (P Q : MvPolynomial α ℝ) (S : Finset α)
    (hP : P.totalDegree ≤ S.card) (hQ : Q.totalDegree ≤ S.card)
    (he : ∀ x : α → Bool, eval (spin x) P = eval (spin x) Q) :
    P.coeff (exponent S) = Q.coeff (exponent S) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [← fourier_eq_top_coefficient P S hP, ← fourier_eq_top_coefficient Q S hQ]
  simp only [fourier, he]

/-- Three distinct-group coefficients of the averaged polynomial are unchanged. -/
theorem meanPolynomial_cubic_coefficient {n m : ℕ} (hm : 2 < m)
    (P : MvPolynomial (Fin n × Fin m) ℝ) (hP : P.totalDegree ≤ 3)
    (S : Finset (Fin n)) (hS : S.card = 3) :
    (meanPolynomial P).coeff (exponent S) = (rename Prod.fst P).coeff (exponent S) := by
  classical
  apply top_coefficient_eq_of_cube_eq
  · exact (meanPolynomial_degree P).trans (hS ▸ hP)
  · exact (totalDegree_rename_le Prod.fst P).trans (hS ▸ hP)
  · exact meanPolynomial_corner hm P hP

end

end HeadComplexity.CubeTopCoefficients
