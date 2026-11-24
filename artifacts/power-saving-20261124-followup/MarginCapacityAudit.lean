import HeadComplexity.Research.MarginCapacityEstimates

open HeadComplexity HeadComplexity.RelativeMarginQuantifiers
open HeadComplexity.OriginalMarginCapacity HeadComplexity.MarginCapacityEstimates

example {n H : ℕ} (hn : 32 ≤ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * Real.sqrt n)) :
    (highMarginFunctions n H (Real.exp (-Real.exp (Real.sqrt n)))).ncard ≤
      2 ^ (2 ^ (n - 1)) :=
  card_highMargin_sqrt_scale hn hwidth

example {n H : ℕ} (hn : 32 ≤ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * (n : ℝ) ^ 2)) :
    (highMarginFunctions n H (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))).ncard ≤
      2 ^ (2 ^ (n - 1)) :=
  card_highMargin_logarithmic_scale hn hwidth

example {n H B : ℕ} {C : ℝ} (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)) :
    (highMarginFunctions n (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp (Real.sqrt n)))).ncard ≤ 2 ^ (2 ^ (n - 1)) :=
  card_highMargin_sqrt_overhead hn hC hoverhead hwidth

example {n H B : ℕ} {C : ℝ} (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)) :
    (highMarginFunctions n (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))).ncard ≤ 2 ^ (2 ^ (n - 1)) :=
  card_highMargin_logarithmic_overhead hn hC hoverhead hwidth

#print axioms highMarginFunctions_subset_orderedPatterns
#print axioms card_highMarginFunctions_le
#print axioms card_highMargin_sqrt_scale
#print axioms card_highMargin_logarithmic_scale
#print axioms card_highMargin_sqrt_overhead
#print axioms card_highMargin_logarithmic_overhead
