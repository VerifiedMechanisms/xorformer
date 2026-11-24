import HeadComplexity.Results.WarrenBound

open HeadComplexity

example : WarrenStrictSignPatternBound := warrenStrictSignPatternBound

example {n : ℕ} (hn : 1 ≤ n) (hsize : 35 * n * n ≤ 2 ^ n - 1) :
    (2 ^ n - 1) / (35 * n * n) < worstCaseHeadComplexity n :=
  worstCaseHeadComplexity_gt_div hn hsize

#print axioms strictPolynomialSignPatterns_card_le
#print axioms warrenStrictSignPatternBound
#print axioms worstCaseHeadComplexity_gt_div
