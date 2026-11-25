import HeadComplexity.Results.FourBitThreeHeadRealization

set_option linter.style.header false

namespace HeadComplexity

namespace FourBitCertificate

def truthTable (f : (Fin 4 → Bool) → Bool) : BitVec 16 :=
  BitVec.ofBoolListLE [f (vertex 0), f (vertex 1), f (vertex 2), f (vertex 3),
    f (vertex 4), f (vertex 5), f (vertex 6), f (vertex 7),
    f (vertex 8), f (vertex 9), f (vertex 10), f (vertex 11),
    f (vertex 12), f (vertex 13), f (vertex 14), f (vertex 15)]

theorem truthTable_bit (f : (Fin 4 → Bool) → Bool) (v : Fin 16) :
    (truthTable f).getLsbD v.val = f (vertex v) := by
  unfold truthTable
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases v <;> rfl

theorem truthTable_injective : Function.Injective truthTable := by
  intro f g h
  funext x
  obtain ⟨v, rfl⟩ := vertex_surjective x
  rw [← truthTable_bit f v, ← truthTable_bit g v, h]

@[simp] theorem truthTable_parity : truthTable (PARITY 4) = 27030 := by decide +kernel

@[simp] theorem truthTable_not_parity :
    truthTable (fun x => !(PARITY 4 x)) = 38505 := by decide +kernel

end FourBitCertificate

/-- Every four-bit Boolean function other than parity and its complement is
computable with three unchanged vanilla heads. The proof checks 24 exact integer
templates and a finite sign-pattern coverage certificate in the Lean kernel. -/
theorem vanilla_three_computes_fourBit_nonparity (f : (Fin 4 → Bool) → Bool)
    (h0 : f ≠ PARITY 4) (h1 : f ≠ fun x => !(PARITY 4 x)) :
    computableWithSharedHeadsN 4 3 f := by
  open FourBitCertificate in
  have hy0 : truthTable f ≠ 27030 := by
    intro h
    apply h0
    apply truthTable_injective
    simpa only [truthTable_parity] using h
  open FourBitCertificate in
  have hy1 : truthTable f ≠ 38505 := by
    intro h
    apply h1
    apply truthTable_injective
    simpa only [truthTable_not_parity] using h
  obtain ⟨i, hi⟩ := FourBitCertificate.mask_coverage _ hy0 hy1
  have hm := FourBitCertificate.maskMatches_matches i _ hi
  simp only [FourBitCertificate.truthTable_bit] at hm
  obtain ⟨a, ha⟩ := SignTemplate.exists_strict_score_or_neg
    (FourBitCertificate.features (FourBitCertificate.family i))
    (FourBitCertificate.certificates i) (FourBitCertificate.certificates_valid i)
    (fun v => f (FourBitCertificate.vertex v)) hm
  exact FourBitCertificate.vanilla_of_strict_feature_score f _ a ha

/-- Symmetric targets have the reverse implication at every head count, using
sign changes and zero-head padding. -/
theorem vanilla_of_pureRoPEComputable_symmetric {n H : ℕ} (F : ℕ → Bool)
    (hf : pureRoPEComputable n H (symmetricFn F)) :
    computableWithSharedHeadsN n H (symmetricFn F) := by
  have hb := signChanges_le_of_ThresholdDegLE (thresholdDegLE_of_pureRoPEComputable hf)
  apply computableWithSharedHeadsN_mono hb
  exact computableWithSharedHeadsN_of_computableWithHeadsN (symmetricFn_computable F n)

/-- Four input bits have pure/vanilla equivalence at every head count. -/
theorem pureRoPEComputable_iff_vanilla_fourBit {H : ℕ}
    (f : (Fin 4 → Bool) → Bool) :
    pureRoPEComputable 4 H f ↔ computableWithSharedHeadsN 4 H f := by
  constructor
  · intro hf
    by_cases hp : f = PARITY 4
    · subst f
      exact vanilla_of_pureRoPEComputable_symmetric (fun k => decide (Odd k)) hf
    by_cases hn : f = fun x => !(PARITY 4 x)
    · subst f
      exact vanilla_of_pureRoPEComputable_symmetric (fun k => !(decide (Odd k))) hf
    by_cases hh : H ≤ 2
    · exact vanilla_of_pureRoPEComputable_le_two hh hf
    · exact computableWithSharedHeadsN_mono (by omega)
        (vanilla_three_computes_fourBit_nonparity f hp hn)
  · exact pureRoPEComputable_of_vanilla

/-- Universal pure/vanilla equivalence at every head count on at most four bits,
including the empty input and zero heads. -/
theorem pureRoPEComputable_iff_vanilla_of_input_le_four {n H : ℕ}
    (hn : n ≤ 4) (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n H f ↔ computableWithSharedHeadsN n H f := by
  by_cases hn4 : n = 4
  · subst n
    exact pureRoPEComputable_iff_vanilla_fourBit f
  · exact pureRoPEComputable_iff_vanilla_of_input_le_three (by omega) f

/-- Minimum head counts agree on at most four input bits. -/
theorem pureRoPEHStar_eq_vanilla_of_input_le_four {n : ℕ}
    (hn : n ≤ 4) (f : (Fin n → Bool) → Bool) :
    PureRoPEHStar n f = HStar n f := by
  apply le_antisymm (pureRoPEHStar_le_vanilla f)
  have hf := (pureRoPEComputable_iff_vanilla_of_input_le_four hn f).mp
    (pureRoPEHStar_computable f)
  have hc := computableWithHeadsN_of_computableWithSharedHeadsN hf
  classical
  unfold HStar
  rw [dif_pos (exists_computable f)]
  exact Nat.find_min' _ hc

end HeadComplexity
