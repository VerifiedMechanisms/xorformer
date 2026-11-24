import HeadComplexity

-- Run from formalization:
-- lake env lean ../artifacts/head-compression/audit_universal_log_saving.lean
-- Only propext, Classical.choice, and Quot.sound should occur below.

#check HeadComplexity.worstCaseHeadComplexity_isBigO_two_pow_div_mul_log
#check HeadComplexity.worstCaseHeadComplexity_real_le_log_saving
#check HeadComplexity.worstCaseHeadComplexity_exists_log_saving

#print axioms HeadComplexity.worstCaseHeadComplexity_isBigO_two_pow_div_mul_log
#print axioms HeadComplexity.worstCaseHeadComplexity_real_le_log_saving
#print axioms HeadComplexity.worstCaseHeadComplexity_exists_log_saving
#print axioms HeadComplexity.AxisZeroGluing.hasStrictReverseGridCompiler_affinePlane
#print axioms HeadComplexity.AxisZeroGluing.exists_affinePlane_reverse_grid
#print axioms HeadComplexity.exists_compact_cauchy_grid_decoder
