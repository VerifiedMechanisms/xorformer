import HeadComplexity.Results.AffineStatisticProjective
import HeadComplexity.Results.TopThresholdDegree

set_option linter.style.header false

/-! Every proper subset of the parity truth table is realizable with `n - 1`
heads. The full table requires `n` heads. This is a feasibility obstruction,
not the requested worst-case asymptotic head lower bound. -/
namespace HeadComplexity
namespace PuncturedParity
open Finset
open scoped BigOperators

variable {n : ℕ}

def xorBits (x v : Fin n → Bool) : Fin n → Bool := fun i ↦ Bool.xor (x i) (v i)

theorem distance_affine (x v : Fin n → Bool) :
    affineValue (hammingWeight v : ℝ) (fun i ↦ if v i then -1 else 1) x =
      (hammingWeight (xorBits x v) : ℝ) := by
  rw [hammingWeight_eq_sum, hammingWeight_eq_sum]
  unfold affineValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> cases hv : v i <;> norm_num [xorBits, boolToReal, hx, hv]

theorem distance_zero_iff (x v : Fin n → Bool) :
    hammingWeight (xorBits x v) = 0 ↔ x = v := by
  rw [hammingWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · intro h
    funext i
    have hi : xorBits x v i ≠ true := @h i
    cases hx : x i <;> cases hv : v i <;> simp_all [xorBits]
  · intro h i
    subst h
    simp [xorBits]

theorem parity_xor (x v : Fin n → Bool) :
    PARITY n (xorBits x v) = Bool.xor (PARITY n x) (PARITY n v) := by
  have hprod : paritySignValue (xorBits x v) = paritySignValue x * paritySignValue v := by
    simp only [paritySignValue_eq_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases hx : x i <;> cases hv : v i <;> norm_num [xorBits, boolToReal, hx, hv]
  cases hx : PARITY n x <;> cases hv : PARITY n v <;>
    cases hz : PARITY n (xorBits x v) <;>
    simp_all [paritySignValue] <;> norm_num at hprod

def puncturedProfile (k : ℕ) : Bool := if k = 0 then true else decide (Odd k)

theorem puncturedProfile_signChanges (n : ℕ) :
    signChanges n puncturedProfile = n - 1 := by
  have hset : (Finset.range n).filter (fun t ↦ puncturedProfile t ≠ puncturedProfile (t + 1)) =
      (Finset.range n).erase 0 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    by_cases ht : t = 0
    · subst ht
      norm_num [puncturedProfile]
    · have hflip : decide (Odd t) ≠ decide (Odd (t + 1)) := by
        by_cases hodd : Odd t <;> simp [Nat.odd_add_one, hodd]
      simp [puncturedProfile, ht, hflip, and_comm]
  unfold signChanges
  rw [hset]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [Finset.card_erase_of_mem (by simpa using Nat.pos_of_ne_zero hn), Finset.card_range]

def punctured (v x : Fin n → Bool) : Bool :=
  if x = v then !(PARITY n x) else PARITY n x

theorem punctured_as_profile (v x : Fin n → Bool) :
    punctured v x = Bool.xor (puncturedProfile (hammingWeight (xorBits x v))) (PARITY n v) := by
  by_cases h : x = v
  · subst x
    have hz := (distance_zero_iff v v).mpr rfl
    rw [hz]
    simp [punctured, puncturedProfile]
  · have hz : hammingWeight (xorBits x v) ≠ 0 := fun h0 ↦ h ((distance_zero_iff x v).mp h0)
    simp only [punctured, ite_eq_right h, puncturedProfile, ite_eq_right hz]
    change PARITY n x = Bool.xor (PARITY n (xorBits x v)) (PARITY n v)
    rw [parity_xor]
    cases PARITY n x <;> cases PARITY n v <;> rfl

theorem distance_profile_computable (v : Fin n → Bool) (F : ℕ → Bool) :
    computableWithHeadsN n (signChanges n F)
      (fun x ↦ F (hammingWeight (xorBits x v))) := by
  obtain ⟨P, hdeg, hsign⟩ := exists_sign_poly F n
  apply computableWithHeadsN_of_univariateAffine (hammingWeight v : ℝ)
    (fun i ↦ if v i then -1 else 1)
  refine ⟨P, hdeg, ?_⟩
  intro x
  rw [distance_affine]
  exact hsign _ (hammingWeight_le n _)

theorem punctured_computable (v : Fin n → Bool) :
    computableWithHeadsN n (n - 1) (punctured v) := by
  have h := distance_profile_computable v puncturedProfile
  rw [puncturedProfile_signChanges] at h
  have heq : punctured v = fun x ↦
      Bool.xor (puncturedProfile (hammingWeight (xorBits x v))) (PARITY n v) :=
    funext (punctured_as_profile v)
  rw [heq]
  cases hv : PARITY n v
  · simpa only [Bool.xor_false] using h
  · simpa only [Bool.xor_true] using (computableWithHeadsN_complement_iff _).mpr h

/-- Every proper subset of the parity constraints is feasible with `n - 1`
heads. The completion differs from parity at just one omitted vertex. -/
theorem proper_subset_parity_feasible (S : Set (Fin n → Bool)) (hS : S ≠ Set.univ) :
    ∃ f : (Fin n → Bool) → Bool, computableWithHeadsN n (n - 1) f ∧
      ∀ x ∈ S, f x = PARITY n x := by
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra hh
    push Not at hh
    exact hS (Set.eq_univ_of_forall hh)
  refine ⟨punctured v, punctured_computable v, ?_⟩
  intro x hx
  have hxv : x ≠ v := fun heq ↦ hv (heq ▸ hx)
  simp [punctured, hxv]

/-- The full parity table is infeasible at the same head count. -/
theorem full_parity_infeasible (hn : 0 < n) :
    ¬ computableWithHeadsN n (n - 1) (PARITY n) := by
  intro h
  have hh := HStar_le_of_computableWithHeadsN h
  rw [HStar_parity] at hh
  omega

end PuncturedParity
end HeadComplexity
