import HeadComplexity.Atoms.WeightedPolynomial

set_option linter.style.header false

/-!
# Polynomial certificates for positive projections

`PositiveWeightedSignDegLE f K` says that some positive weighted statistic
`wT lam` reduces `f` to a real univariate sign polynomial of degree at most
`K`.  The least such `K` is `positiveWeightedSignDeg f`.

This packages the polynomial certificates behind the existing
positive-projection sign-change bound. On a finite ordered projection image,
least sign-polynomial degree equals the number of label changes, so the minimum
is the polynomial presentation of that earlier invariant. Binary weights make
the statistic injective, so every Boolean function has such a certificate. The
minimum is therefore attained, including in dimension zero.
-/

namespace HeadComplexity

variable {n K L : ℕ}

/-- A Boolean function has positive weighted sign degree at most `K` if it is
sign-represented by a degree-at-most-`K` polynomial in some positive weighted
sum of its bits. -/
def PositiveWeightedSignDegLE (f : (Fin n → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ lam : Fin n → ℝ, (∀ i, 0 < lam i) ∧
    UnivariateThresholdDegLE (wT lam) f K

namespace PositiveWeightedSignDegLE

/-- A positive weighted sign-degree certificate remains valid at every larger
degree bound. -/
theorem mono {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f K) (hKL : K ≤ L) :
    PositiveWeightedSignDegLE f L := by
  obtain ⟨lam, hlam, hpoly⟩ := h
  exact ⟨lam, hlam, hpoly.mono hKL⟩

/-- A positive weighted sign-degree certificate is realized by the same
number of attention heads. -/
theorem computable {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f K) : computableWithHeadsN n K f := by
  obtain ⟨lam, hlam, hpoly⟩ := h
  exact weighted_computable_of_UnivariateThresholdDegLE lam hlam f hpoly

/-- A positive weighted sign-degree certificate also yields the exact
fractional-atom representation with the same number of atoms. -/
theorem fracComputable {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f K) : HeadComplexity.fracComputable n K f := by
  obtain ⟨lam, hlam, hpoly⟩ := h
  exact weighted_fracComputable_of_UnivariateThresholdDegLE lam hlam f hpoly

end PositiveWeightedSignDegLE

/-- Binary weights give every Boolean function a positive weighted sign-degree
certificate of degree at most `2^n - 1`. -/
theorem binaryWeights_positiveWeightedSignDegLE (f : (Fin n → Bool) → Bool) :
    PositiveWeightedSignDegLE f (2 ^ n - 1) := by
  classical
  let lam : Fin n → ℝ := fun i ↦ (2 : ℝ) ^ (i : ℕ)
  have hlam : ∀ i, 0 < lam i := fun i ↦ by
    simp only [lam]
    positivity
  have hinj : Function.Injective (wT lam) := by
    simpa only [lam] using (wT_two_pow_injective (n := n))
  let G : ℝ → Bool := f ∘ Function.invFun (wT lam)
  have hf : ∀ bits, f bits = G (wT lam bits) := by
    intro bits
    change f bits = f (Function.invFun (wT lam) (wT lam bits))
    rw [Function.leftInverse_invFun hinj bits]
  have hpoly := weighted_univariateThresholdDegLE lam f G hf
  have hcard : (Finset.univ.image (wT lam)).card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  refine ⟨lam, hlam, ?_⟩
  rwa [hcard] at hpoly

/-- Every Boolean function has a positive weighted sign-degree certificate.
Binary weights separate all Boolean inputs, and Lagrange interpolation on the
finite image supplies the polynomial. -/
theorem exists_positiveWeightedSignDegLE (f : (Fin n → Bool) → Bool) :
    ∃ K, PositiveWeightedSignDegLE f K :=
  ⟨2 ^ n - 1, binaryWeights_positiveWeightedSignDegLE f⟩

/-- The least positive weighted sign degree of a Boolean function. -/
noncomputable def positiveWeightedSignDeg (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_positiveWeightedSignDegLE f)

/-- The minimum positive weighted sign degree is attained. -/
theorem positiveWeightedSignDeg_spec (f : (Fin n → Bool) → Bool) :
    PositiveWeightedSignDegLE f (positiveWeightedSignDeg f) := by
  classical
  exact Nat.find_spec (exists_positiveWeightedSignDegLE f)

/-- Every explicit positive weighted sign-degree certificate upper-bounds the
minimum. -/
theorem positiveWeightedSignDeg_le {f : (Fin n → Bool) → Bool}
    (h : PositiveWeightedSignDegLE f K) : positiveWeightedSignDeg f ≤ K := by
  classical
  exact Nat.find_min' (exists_positiveWeightedSignDegLE f) h

/-- The minimum positive weighted sign degree is realized using that many
attention heads. -/
theorem positiveWeightedSignDeg_computable (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n (positiveWeightedSignDeg f) f :=
  (positiveWeightedSignDeg_spec f).computable

/-- The minimum positive weighted sign degree is also realized in the
fractional-atom normal form using that many atoms. -/
theorem positiveWeightedSignDeg_fracComputable (f : (Fin n → Bool) → Bool) :
    fracComputable n (positiveWeightedSignDeg f) f :=
  (positiveWeightedSignDeg_spec f).fracComputable

/-- The binary-weight interpolation certificate recovers the universal
`2^n - 1` upper bound for positive weighted sign degree. -/
theorem positiveWeightedSignDeg_le_universal (f : (Fin n → Bool) → Bool) :
    positiveWeightedSignDeg f ≤ 2 ^ n - 1 :=
  positiveWeightedSignDeg_le (binaryWeights_positiveWeightedSignDegLE f)

end HeadComplexity
