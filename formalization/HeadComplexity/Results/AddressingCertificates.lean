import HeadComplexity.Results.Addressing

set_option linter.style.header false

/-! # Exact integral addressing certificates -/

namespace HeadComplexity.AddressingCertificates

def denConstant1 : Fin 2 → ℤ := ![1, 1]

def denCoefficient1 : Fin 2 → Fin 3 → ℤ :=
  ![![1, 1, 1],
    ![2, 3, 4]]

def denominator1 (h : Fin 2) : IntegralOrientedDenominator 3 where
  constant := denConstant1 h
  coefficient := denCoefficient1 h
  orientation := by fin_cases h <;> decide

def numConstant1 : Fin 2 → ℤ := ![0, 0]

def numCoefficient1 : Fin 2 → Fin 3 → ℤ :=
  ![![-940, 3440, -10364],
    ![1392, -6392, 25880]]

def bias1 : ℤ := -61

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
/-- Every checked word has the target strict sign after positive clearing. -/
theorem checked1 : ∀ word : Fin 8,
    (0 < integralClearedScore denominator1 bias1 numConstant1 numCoefficient1
        (cubeBits word) ↔ IDX 1 (cubeBits word) = true) ∧
      integralClearedScore denominator1 bias1 numConstant1 numCoefficient1
        (cubeBits word) ≠ 0 := by decide +kernel

/-- Exact finite data passed through the existing actual-head compiler. -/
def certificate1 : IntegralClearedScoreCertificate 3 2 (IDX 1) where
  denominator := denominator1
  bias := bias1
  numConstant := numConstant1
  numCoefficient := numCoefficient1
  represents := by
    intro bits
    obtain ⟨word, rfl⟩ := cubeBits_surjective 3 bits
    exact checked1 word

theorem HStar_IDX1 : HStar 3 (IDX 1) = 2 := by
  exact Nat.le_antisymm certificate1.HStar_le (addressCount_succ_le_HStar 1)

def denConstant2 : Fin 3 → ℤ := ![2, 1, 1]

def denCoefficient2 : Fin 3 → Fin 6 → ℤ :=
  ![![1, 1, 2, 1, 2, 1],
    ![2, 1, 2, 1, 1, 1],
    ![1, 2, 1, 2, 2, 1]]

def denominator2 (h : Fin 3) : IntegralOrientedDenominator 6 where
  constant := denConstant2 h
  coefficient := denCoefficient2 h
  orientation := by fin_cases h <;> decide

def numConstant2 : Fin 3 → ℤ := ![173, -203, 26]

def numCoefficient2 : Fin 3 → Fin 6 → ℤ :=
  ![![203, -203, -15, -203, -169, 203],
    ![13, 161, -18, 30, 184, -114],
    ![-203, 1, 45, 170, -18, -33]]

def bias2 : ℤ := 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
/-- Every checked word has the target strict sign after positive clearing. -/
theorem checked2 : ∀ word : Fin 64,
    (0 < integralClearedScore denominator2 bias2 numConstant2 numCoefficient2
        (cubeBits word) ↔ IDX 2 (cubeBits word) = true) ∧
      integralClearedScore denominator2 bias2 numConstant2 numCoefficient2
        (cubeBits word) ≠ 0 := by decide +kernel

/-- Exact finite data passed through the existing actual-head compiler. -/
def certificate2 : IntegralClearedScoreCertificate 6 3 (IDX 2) where
  denominator := denominator2
  bias := bias2
  numConstant := numConstant2
  numCoefficient := numCoefficient2
  represents := by
    intro bits
    obtain ⟨word, rfl⟩ := cubeBits_surjective 6 bits
    exact checked2 word

theorem HStar_IDX2 : HStar 6 (IDX 2) = 3 := by
  exact Nat.le_antisymm certificate2.HStar_le (addressCount_succ_le_HStar 2)

def denConstant3 : Fin 4 → ℤ := ![1000, 22029032, 22034149, 22030391]

def denCoefficient3 : Fin 4 → Fin 11 → ℤ :=
  ![![22026466, 1, 22026466, 1, 1, 4764, 1, 1, 1, 1, 1],
    ![-22026466, -1, -563, -1, -485, -1, -76, -415, -1, -22, -1],
    ![-1959, -3563, -22026466, -1, -121, -1, -1, -1, -1, -1, -1034],
    ![-1, -22026466, -1, -1, -144, -1, -1571, -1066, -1, -1, -138]]

def denominator3 (h : Fin 4) : IntegralOrientedDenominator 11 where
  constant := denConstant3 h
  coefficient := denCoefficient3 h
  orientation := by fin_cases h <;> decide

def numConstant3 : Fin 4 → ℤ := ![-42568, -16622, -14668, 83654]

def numCoefficient3 : Fin 4 → Fin 11 → ℤ :=
  ![![-10314, -171161, -36369, 124386, -13248, 1052, -12245, -5783, 7390, -22003, -22036],
    ![-2559, -204994, -65214, -1610, 29882, 655, 2624, -677, 12207, 625, -6785],
    ![234978, -36046, -10799, 5177, -13621, -5057, -1519, 74534, 12665, -4377, -17400],
    ![72237, 91371, -132731, -5346, 9544, 5519, -28717, -61088, -5598, 58660, 13018]]

def bias3 : ℤ := 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the complete finite certificate using the trusted kernel.
/-- Every checked word has the target strict sign after positive clearing. -/
theorem checked3 : ∀ word : Fin 2048,
    (0 < integralClearedScore denominator3 bias3 numConstant3 numCoefficient3
        (cubeBits word) ↔ IDX 3 (cubeBits word) = true) ∧
      integralClearedScore denominator3 bias3 numConstant3 numCoefficient3
        (cubeBits word) ≠ 0 := by decide +kernel

/-- Exact finite data passed through the existing actual-head compiler. -/
def certificate3 : IntegralClearedScoreCertificate 11 4 (IDX 3) where
  denominator := denominator3
  bias := bias3
  numConstant := numConstant3
  numCoefficient := numCoefficient3
  represents := by
    intro bits
    obtain ⟨word, rfl⟩ := cubeBits_surjective 11 bits
    exact checked3 word

theorem HStar_IDX3 : HStar 11 (IDX 3) = 4 := by
  exact Nat.le_antisymm certificate3.HStar_le (addressCount_succ_le_HStar 3)

end HeadComplexity.AddressingCertificates
