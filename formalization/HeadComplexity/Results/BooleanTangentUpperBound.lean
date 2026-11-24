import HeadComplexity.Atoms.TwoHeadPencil
import HeadComplexity.Results.AffineStatisticUpperBound

set_option linter.style.header false

/-!
# Tangent classifiers at Boolean zero families

A nontrivial family of affine fractions can vanish at every Boolean input
without vanishing as a rational function on real inputs. Perturbing such a
family and rescaling its numerators realizes every strict first derivative
with the same number of heads. The original vanilla definitions are used.
-/

namespace HeadComplexity

open scoped BigOperators Topology

namespace CubeAffine

private theorem positive_between (a b ε t : ℝ) (ha : 0 < a)
    (hab : 0 < a + ε * b) (ht : 0 < t) (htε : t < ε) :
    0 < a + t * b := by
  by_cases hb : 0 ≤ b
  · exact add_pos_of_pos_of_nonneg ha (mul_nonneg ht.le hb)
  · have hb' : b < 0 := lt_of_not_ge hb
    have hm := mul_lt_mul_of_neg_right htε hb'
    linarith

/-- A zero family with strictly positive denominator slopes can be perturbed
to realize any strict sign of its first variation, with no extra head. -/
theorem computable_of_zero_family_tangent {n H : ℕ}
    (N D A B : Fin H → CubeAffine n)
    (hD : ∀ h x, 0 < (D h).eval x)
    (hslope : ∀ h i, 0 < (D h).slope i)
    (hzero : ∀ x, ∑ h, (N h).eval x / (D h).eval x = 0)
    (f : (Fin n → Bool) → Bool)
    (hsign : ∀ x, (0 < ∑ h,
      ((A h).eval x * (D h).eval x - (N h).eval x * (B h).eval x) /
        ((D h).eval x) ^ 2 ↔ f x = true))
    (hne : ∀ x, (∑ h,
      ((A h).eval x * (D h).eval x - (N h).eval x * (B h).eval x) /
        ((D h).eval x) ^ 2) ≠ 0) :
    computableWithSharedHeadsN n H f := by
  classical
  let S (t : ℝ) (x : Fin n → Bool) : ℝ := ∑ h,
    ((A h).eval x * (D h).eval x - (N h).eval x * (B h).eval x) /
      ((D h).eval x * ((D h).eval x + t * (B h).eval x))
  have hS0 (x : Fin n → Bool) : S 0 x = ∑ h,
      ((A h).eval x * (D h).eval x - (N h).eval x * (B h).eval x) /
        ((D h).eval x) ^ 2 := by simp [S, pow_two]
  have hcont (x : Fin n → Bool) : ContinuousAt (fun t : ℝ ↦ S t x) 0 := by
    apply tendsto_finsetSum
    intro h _
    apply continuousAt_const.div
      (continuousAt_const.mul (continuousAt_const.add
        (continuousAt_id.mul continuousAt_const)))
    simpa using mul_ne_zero (hD h x).ne' (hD h x).ne'
  let α (j : Fin H × ((Fin n → Bool) ⊕ Fin n)) : ℝ :=
    Sum.elim (D j.1).eval (D j.1).slope j.2
  let β (j : Fin H × ((Fin n → Bool) ⊕ Fin n)) : ℝ :=
    Sum.elim (B j.1).eval (B j.1).slope j.2
  have hα (j : Fin H × ((Fin n → Bool) ⊕ Fin n)) : 0 < α j := by
    rcases j with ⟨h, x | i⟩
    · exact hD h x
    · exact hslope h i
  obtain ⟨ε, hε, hεpos⟩ := exists_positive_perturbation α β hα
  obtain ⟨t, ht, htε, hstable⟩ := exists_pos_lt_sign_preserving S hcont
    (fun x ↦ by simpa only [hS0] using hne x) ε hε
  have hpos (j : Fin H × ((Fin n → Bool) ⊕ Fin n)) :
      0 < α j + t * β j :=
    positive_between _ _ ε t (hα j) (hεpos j) ht htε
  let E (h : Fin H) := combine 1 (D h) t (B h)
  let V (h : Fin H) := combine t⁻¹ (N h) 1 (A h)
  let r (h : Fin H) := ratio (V h) (E h)
  have hE (h : Fin H) (x : Fin n → Bool) : 0 < (E h).eval x := by
    simpa [E, combine_eval, α, β] using hpos (h, Sum.inl x)
  have hEs (h : Fin H) (i : Fin n) : 0 < (E h).slope i := by
    simpa [E, combine, α, β] using hpos (h, Sum.inr i)
  have hterm (h : Fin H) (x : Fin n → Bool) :
      (r h).eval x = t⁻¹ * ((N h).eval x / (D h).eval x) +
        ((A h).eval x * (D h).eval x - (N h).eval x * (B h).eval x) /
          ((D h).eval x * ((D h).eval x + t * (B h).eval x)) := by
    have he : (D h).eval x + t * (B h).eval x ≠ 0 := by
      simpa [E, combine_eval] using (hE h x).ne'
    simp only [r, ratio_eval, V, E, combine_eval, one_mul]
    field_simp [ht.ne', (hD h x).ne', he]
    ring
  have hscore (x : Fin n → Bool) : (∑ h, (r h).eval x) = S t x := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, zero_add]
  apply (computableWithSharedHeadsN_iff_affineFractionComputable H f).mpr
  refine ⟨r, 0, fun h ↦ ratio_admissible _ _ (hE h) (Or.inl (hEs h)), fun x ↦ ?_⟩
  rw [zero_add, hscore, (hstable x).1, hS0]
  exact hsign x

end CubeAffine

end HeadComplexity
