# Four-head quartic face obstruction

## Statement

Split fourteen input coordinates into blocks of sizes eight, two, two, and two, denoted $X,Y,Z,W$. Index the eight columns by triples from $Y \times Z \times W$. Suppose a Boolean function has the following faces, with independently chosen fixed backgrounds:

1. For every off-diagonal row and column, varying its one $X$ coordinate and the three column coordinates gives the negative of four-bit parity in sign coordinates.

2. For every column, tying all eight $X$ coordinates to one bit and varying the three column coordinates gives positive four-bit parity in sign coordinates.

Then the unchanged original xorformer requires at least five heads. Zero denominator directions and either orientation of each admissible denominator are included.

The Lean declarations are `FourHeadQuarticPattern.not_computable_four` and `FourHeadQuarticPattern.HStar_ge_five` in `formalization/HeadComplexity/Results/FourHeadQuarticPattern.lean`. They use only `propext`, `Classical.choice`, and `Quot.sound`.

## Proof

Clear the positive affine denominators of an arbitrary four-head representation. The resulting polynomial has degree at most four. A fourth alternating difference is its mixed quartic coefficient and is independent of all fixed background coordinates. Tying the $X$ coordinates replaces the relevant coefficient by their sum.

Let $C$ be the eight-by-eight matrix of coefficients of $X_iY_jZ_kW_l$. The negative faces force strictly negative off-diagonal entries, and the positive tied faces force strictly positive column sums.

Write $A_h$ for numerator slopes and $B_h$ for denominator slopes. Expanding the cleared numerator gives

$$ C=A_X T^{\top}+B_X D^{\top}. $$

Here the column indexed by head $h$ in $T$ is the sum of the six products assigning the other three denominator slopes to the three column coordinates. Each denominator has uniformly positive, uniformly negative, or identically zero slopes. Therefore every column of $B_X$ and every column of $T$ has uniform sign, with identically zero columns allowed. Reorienting these columns and their paired unrestricted factors independently gives two nonnegative factors whose nonzero columns are strictly positive.

`ThreeHeadTripartiteCross.uniform_obstruction`, despite its historical namespace, is generic in the head count. Its four-head instance excludes exactly such an eight-by-eight matrix with nonpositive off-diagonal entries and positive column sums. The underlying proof is `PositiveHalfRankCross.obstruction`; it treats zero columns through the rank obstruction and the full-rank case through inverse positivity.

The exact quartic expansion and uniform-sign product lemma are `FourHeadQuarticFace.alternating_face` and `FourHeadQuarticFace.triple_uniform`. The Boolean sign extraction is `FourHeadBooleanFace.alternating_pos` and `FourHeadBooleanFace.alternating_neg`.

The original architecture is covered by `computableWithHeadsN_iff_affineFractionComputable`, which extracts all admissible affine fractions from an arbitrary original model. This argument does not restrict width, parameter values, numerator slopes, or the query realization.

## Fixed finite target

Take all fixed background bits zero on the fifty-six negative faces, and all fixed background bits one on the eight positive tied faces. The resulting prescriptions are consistent on exactly 281 distinct inputs. The standard-library verifier `artifacts/rope/tripartite_faces/verify_fixed_patterns.py` checks these overlaps exactly.

An explicit integer quartic completing the prescriptions is stored in `artifacts/rope/tripartite_faces/quartic_completion.json`, with its full 16384-bit truth table in `quartic_completion_truth_table.txt`. The verifier evaluates all scores with Python integers, proves each is odd and hence nonzero, and checks every prescribed sign with minimum integer margin seven. The polynomial has degree at most four. A negative parity face gives threshold degree at least four by the usual alternating-sum argument, so this explicit target has threshold degree exactly four and vanilla head complexity at least five. The finite polynomial certificate is checked by Python integer arithmetic; the generic architecture lower bound is checked by Lean.

This is a rigorous all-vanilla lower-bound target. A pure four-head representation satisfying these Boolean labels remains unproved. Quartic coefficient inequalities alone do not establish the labels, since lower-degree terms contribute to every actual score.
