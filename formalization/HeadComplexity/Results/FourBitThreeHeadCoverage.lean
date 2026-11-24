import HeadComplexity.Results.FourBitThreeHeadData

set_option linter.style.header false
set_option linter.style.longLine false

namespace HeadComplexity.FourBitCertificate

open SignTemplate

def supportMasks : Fin 24 → BitVec 16 := ![15, 23, 51, 275, 23, 32781, 278, 33797, 180, 45, 35841, 29, 4110, 4172, 298, 4193, 1098, 12354, 20483, 4290, 4865, 1112, 360, 51]

def positiveMasks : Fin 24 → BitVec 16 := ![14, 21, 51, 259, 18, 32772, 272, 32769, 160, 44, 35841, 29, 4102, 4104, 264, 4192, 1098, 12352, 20481, 4288, 4097, 1112, 360, 50]

theorem support_eq (i : Fin 24) (v : Fin 16) :
    (certificates i).support v = (supportMasks i).getLsbD v.val := by
  fin_cases i <;> rfl

theorem positive_eq (i : Fin 24) (v : Fin 16) :
    (certificates i).positive v = (positiveMasks i).getLsbD v.val := by
  fin_cases i <;> rfl

def MaskMatches (y support positive : BitVec 16) : Prop :=
  y &&& support = positive ∨ y &&& support = support ^^^ positive

instance (y support positive : BitVec 16) : Decidable (MaskMatches y support positive) :=
  inferInstanceAs (Decidable (_ ∨ _))

set_option maxHeartbeats 0 in
-- A 163-node Boolean decision tree proves finite coverage by ordinary case splits.
private theorem boolean_coverage : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool,
  (b0 = false ∧ b1 = true ∧ b2 = true ∧ b3 = false ∧ b4 = true ∧ b5 = false ∧ b6 = false ∧ b7 = true ∧ b8 = true ∧ b9 = false ∧ b10 = false ∧ b11 = true ∧ b12 = false ∧ b13 = true ∧ b14 = true ∧ b15 = false) ∨
  (b0 = true ∧ b1 = false ∧ b2 = false ∧ b3 = true ∧ b4 = false ∧ b5 = true ∧ b6 = true ∧ b7 = false ∧ b8 = false ∧ b9 = true ∧ b10 = true ∧ b11 = false ∧ b12 = true ∧ b13 = false ∧ b14 = false ∧ b15 = true) ∨
  ((b0 = false ∧ b1 = true ∧ b2 = true ∧ b3 = true) ∨ (b0 = true ∧ b1 = false ∧ b2 = false ∧ b3 = false)) ∨
  ((b0 = true ∧ b1 = false ∧ b2 = true ∧ b4 = true) ∨ (b0 = false ∧ b1 = true ∧ b2 = false ∧ b4 = false)) ∨
  ((b0 = true ∧ b1 = true ∧ b4 = true ∧ b5 = true) ∨ (b0 = false ∧ b1 = false ∧ b4 = false ∧ b5 = false)) ∨
  ((b0 = true ∧ b1 = true ∧ b4 = false ∧ b8 = true) ∨ (b0 = false ∧ b1 = false ∧ b4 = true ∧ b8 = false)) ∨
  ((b0 = false ∧ b1 = true ∧ b2 = false ∧ b4 = true) ∨ (b0 = true ∧ b1 = false ∧ b2 = true ∧ b4 = false)) ∨
  ((b0 = false ∧ b2 = true ∧ b3 = false ∧ b15 = true) ∨ (b0 = true ∧ b2 = false ∧ b3 = true ∧ b15 = false)) ∨
  ((b1 = false ∧ b2 = false ∧ b4 = true ∧ b8 = true) ∨ (b1 = true ∧ b2 = true ∧ b4 = false ∧ b8 = false)) ∨
  ((b0 = true ∧ b2 = false ∧ b10 = false ∧ b15 = true) ∨ (b0 = false ∧ b2 = true ∧ b10 = true ∧ b15 = false)) ∨
  ((b2 = false ∧ b4 = false ∧ b5 = true ∧ b7 = true) ∨ (b2 = true ∧ b4 = true ∧ b5 = false ∧ b7 = false)) ∨
  ((b0 = false ∧ b2 = true ∧ b3 = true ∧ b5 = true) ∨ (b0 = true ∧ b2 = false ∧ b3 = false ∧ b5 = false)) ∨
  ((b0 = true ∧ b10 = true ∧ b11 = true ∧ b15 = true) ∨ (b0 = false ∧ b10 = false ∧ b11 = false ∧ b15 = false)) ∨
  ((b0 = true ∧ b2 = true ∧ b3 = true ∧ b4 = true) ∨ (b0 = false ∧ b2 = false ∧ b3 = false ∧ b4 = false)) ∨
  ((b1 = true ∧ b2 = true ∧ b3 = false ∧ b12 = true) ∨ (b1 = false ∧ b2 = false ∧ b3 = true ∧ b12 = false)) ∨
  ((b2 = false ∧ b3 = true ∧ b6 = false ∧ b12 = true) ∨ (b2 = true ∧ b3 = false ∧ b6 = true ∧ b12 = false)) ∨
  ((b1 = false ∧ b3 = true ∧ b5 = false ∧ b8 = true) ∨ (b1 = true ∧ b3 = false ∧ b5 = true ∧ b8 = false)) ∨
  ((b0 = false ∧ b5 = true ∧ b6 = true ∧ b12 = true) ∨ (b0 = true ∧ b5 = false ∧ b6 = false ∧ b12 = false)) ∨
  ((b1 = true ∧ b3 = true ∧ b6 = true ∧ b10 = true) ∨ (b1 = false ∧ b3 = false ∧ b6 = false ∧ b10 = false)) ∨
  ((b1 = false ∧ b6 = true ∧ b12 = true ∧ b13 = true) ∨ (b1 = true ∧ b6 = false ∧ b12 = false ∧ b13 = false)) ∨
  ((b0 = true ∧ b1 = false ∧ b12 = true ∧ b14 = true) ∨ (b0 = false ∧ b1 = true ∧ b12 = false ∧ b14 = false)) ∨
  ((b1 = false ∧ b6 = true ∧ b7 = true ∧ b12 = true) ∨ (b1 = true ∧ b6 = false ∧ b7 = false ∧ b12 = false)) ∨
  ((b0 = true ∧ b8 = false ∧ b9 = false ∧ b12 = true) ∨ (b0 = false ∧ b8 = true ∧ b9 = true ∧ b12 = false)) ∨
  ((b3 = true ∧ b4 = true ∧ b6 = true ∧ b10 = true) ∨ (b3 = false ∧ b4 = false ∧ b6 = false ∧ b10 = false)) ∨
  ((b3 = true ∧ b5 = true ∧ b6 = true ∧ b8 = true) ∨ (b3 = false ∧ b5 = false ∧ b6 = false ∧ b8 = false)) ∨
  ((b0 = false ∧ b1 = true ∧ b4 = true ∧ b5 = true) ∨ (b0 = true ∧ b1 = false ∧ b4 = false ∧ b5 = false)) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  cases b0
  ·
    cases b1
    ·
      cases b3
      ·
        cases b4
        ·
          cases b2
          ·
            simp
          ·
            cases b6
            ·
              cases b10
              ·
                simp
              ·
                cases b15
                ·
                  simp
                ·
                  simp
            ·
              cases b12
              ·
                simp
              ·
                cases b5
                ·
                  simp
                ·
                  simp
        ·
          cases b8
          ·
            simp
          ·
            cases b2
            ·
              simp
            ·
              cases b6
              ·
                cases b10
                ·
                  simp
                ·
                  cases b15
                  ·
                    simp
                  ·
                    simp
              ·
                cases b12
                ·
                  simp
                ·
                  cases b15
                  ·
                    cases b5
                    ·
                      cases b7
                      ·
                        simp
                      ·
                        simp
                    ·
                      simp
                  ·
                    simp
      ·
        cases b5
        ·
          cases b4
          ·
            simp
          ·
            cases b8
            ·
              simp
            ·
              simp
        ·
          cases b2
          ·
            cases b12
            ·
              simp
            ·
              cases b6
              ·
                simp
              ·
                simp
          ·
            simp
    ·
      cases b2
      ·
        cases b4
        ·
          simp
        ·
          simp
      ·
        cases b3
        ·
          cases b12
          ·
            cases b6
            ·
              cases b8
              ·
                cases b5
                ·
                  simp
                ·
                  simp
              ·
                cases b15
                ·
                  cases b10
                  ·
                    cases b4
                    ·
                      simp
                    ·
                      cases b5
                      ·
                        cases b7
                        ·
                          simp
                        ·
                          cases b9
                          ·
                            cases b11
                            ·
                              simp
                            ·
                              cases b13
                              ·
                                simp
                              ·
                                cases b14
                                ·
                                  simp
                                ·
                                  simp
                          ·
                            simp
                      ·
                        simp
                  ·
                    simp
                ·
                  simp
            ·
              simp
          ·
            simp
        ·
          simp
  ·
    cases b1
    ·
      cases b2
      ·
        cases b3
        ·
          simp
        ·
          cases b12
          ·
            simp
          ·
            cases b6
            ·
              simp
            ·
              cases b8
              ·
                cases b15
                ·
                  simp
                ·
                  cases b10
                  ·
                    simp
                  ·
                    cases b4
                    ·
                      cases b5
                      ·
                        simp
                      ·
                        cases b7
                        ·
                          cases b9
                          ·
                            simp
                          ·
                            cases b11
                            ·
                              cases b13
                              ·
                                cases b14
                                ·
                                  simp
                                ·
                                  simp
                              ·
                                simp
                            ·
                              simp
                        ·
                          simp
                    ·
                      simp
              ·
                cases b5
                ·
                  simp
                ·
                  simp
      ·
        cases b4
        ·
          simp
        ·
          simp
    ·
      cases b3
      ·
        cases b5
        ·
          cases b2
          ·
            simp
          ·
            cases b12
            ·
              cases b6
              ·
                simp
              ·
                simp
            ·
              simp
        ·
          cases b4
          ·
            cases b8
            ·
              simp
            ·
              simp
          ·
            simp
      ·
        cases b4
        ·
          cases b8
          ·
            cases b2
            ·
              cases b6
              ·
                cases b12
                ·
                  cases b15
                  ·
                    simp
                  ·
                    cases b5
                    ·
                      simp
                    ·
                      cases b7
                      ·
                        simp
                      ·
                        simp
                ·
                  simp
              ·
                cases b10
                ·
                  cases b15
                  ·
                    simp
                  ·
                    simp
                ·
                  simp
            ·
              simp
          ·
            simp
        ·
          cases b2
          ·
            cases b6
            ·
              cases b12
              ·
                cases b5
                ·
                  simp
                ·
                  simp
              ·
                simp
            ·
              cases b10
              ·
                cases b15
                ·
                  simp
                ·
                  simp
              ·
                simp
          ·
            simp

set_option maxHeartbeats 0 in
-- Translate the finite Boolean decision tree back to the 24 bit-mask cylinders.
theorem mask_coverage (y : BitVec 16) (h0 : y ≠ 27030) (h1 : y ≠ 38505) :
    ∃ i : Fin 24, MaskMatches y (supportMasks i) (positiveMasks i) := by
  obtain hp0 | hp1 | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 :=
    boolean_coverage (y.getLsbD 0) (y.getLsbD 1) (y.getLsbD 2) (y.getLsbD 3) (y.getLsbD 4) (y.getLsbD 5) (y.getLsbD 6) (y.getLsbD 7) (y.getLsbD 8) (y.getLsbD 9) (y.getLsbD 10) (y.getLsbD 11) (y.getLsbD 12) (y.getLsbD 13) (y.getLsbD 14) (y.getLsbD 15)
  · exfalso
    apply h0
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k <;> simp_all
  · exfalso
    apply h1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k <;> simp_all
  · refine ⟨0, ?_⟩
    change MaskMatches y 15 14
    rcases h0 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨1, ?_⟩
    change MaskMatches y 23 21
    rcases h1 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨2, ?_⟩
    change MaskMatches y 51 51
    rcases h2 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨3, ?_⟩
    change MaskMatches y 275 259
    rcases h3 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨4, ?_⟩
    change MaskMatches y 23 18
    rcases h4 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨5, ?_⟩
    change MaskMatches y 32781 32772
    rcases h5 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨6, ?_⟩
    change MaskMatches y 278 272
    rcases h6 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨7, ?_⟩
    change MaskMatches y 33797 32769
    rcases h7 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨8, ?_⟩
    change MaskMatches y 180 160
    rcases h8 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨9, ?_⟩
    change MaskMatches y 45 44
    rcases h9 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨10, ?_⟩
    change MaskMatches y 35841 35841
    rcases h10 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨11, ?_⟩
    change MaskMatches y 29 29
    rcases h11 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨12, ?_⟩
    change MaskMatches y 4110 4102
    rcases h12 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨13, ?_⟩
    change MaskMatches y 4172 4104
    rcases h13 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨14, ?_⟩
    change MaskMatches y 298 264
    rcases h14 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨15, ?_⟩
    change MaskMatches y 4193 4192
    rcases h15 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨16, ?_⟩
    change MaskMatches y 1098 1098
    rcases h16 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨17, ?_⟩
    change MaskMatches y 12354 12352
    rcases h17 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨18, ?_⟩
    change MaskMatches y 20483 20481
    rcases h18 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨19, ?_⟩
    change MaskMatches y 4290 4288
    rcases h19 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨20, ?_⟩
    change MaskMatches y 4865 4097
    rcases h20 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨21, ?_⟩
    change MaskMatches y 1112 1112
    rcases h21 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨22, ?_⟩
    change MaskMatches y 360 360
    rcases h22 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
  · refine ⟨23, ?_⟩
    change MaskMatches y 51 50
    rcases h23 with h | h
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k <;> simp_all

theorem maskMatches_matches (i : Fin 24) (y : BitVec 16)
    (hy : MaskMatches y (supportMasks i) (positiveMasks i)) :
    Matches (certificates i) (fun v => y.getLsbD v.val) ∨
      Matches (certificates i) (fun v => !(y.getLsbD v.val)) := by
  rcases hy with hy | hy
  · left
    intro v hv
    rw [support_eq] at hv
    rw [positive_eq]
    have hb := congrArg (fun b : BitVec 16 => b.getLsbD v.val) hy
    simpa only [BitVec.getLsbD_and, hv, Bool.and_true] using hb
  · right
    intro v hv
    rw [support_eq] at hv
    rw [positive_eq]
    have hb := congrArg (fun b : BitVec 16 => b.getLsbD v.val) hy
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, hv, Bool.and_true,
      Bool.true_xor] at hb
    simpa only [Bool.not_not] using congrArg Bool.not hb

end HeadComplexity.FourBitCertificate
