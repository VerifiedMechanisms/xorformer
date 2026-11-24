# Exact finite chart interpolation in Lean

The finite zero-chart kernel and its quantitative coefficient recovery are proved in Lean. This is a component of the explicit Boolean separation argument; the full lower-bound theorem requires the model, averaging, sign-probe, and tensor-obstruction bridges as well.

## Algebraic kernel

`PureCubicIrreducible.coordinatePolynomial_irreducible` proves irreducibility of the fourteen-variable coordinate polynomial. `coordinatePolynomial_degree` proves its total degree is three, and `eq_scalar_mul_of_dvd` identifies every degree-at-most-three multiple with a scalar multiple.

`PrimitiveGraphDivision.primitive_linear_dvd_of_graph_zero` proves a general fraction-field graph-division lemma. It descends divisibility by a primitive linear polynomial from the fraction field to the original unique-factorization domain. `PureCubicGraphKernel.restriction_zero_iff_dvd` applies it to the actual rational graph.

`PureCubicFiniteKernel.finite_chart_kernel_iff` proves that vanishing at all points of the finite ten-point product chart is equivalent to being a scalar multiple of the coordinate polynomial. Denominator clearing produces a polynomial of total degree at most nine, so the finite grid suffices. The proof uses no numerical rank assertion.

## Original coordinates and exact row bounds

`PureCubicRawKernel.finite_raw_kernel_iff` transfers the kernel through the exact invertible chart matrix. `rawTarget_formula` gives the original cleared pure polynomial, and `eval_rawTarget_means` identifies it with the actual replicated Boolean construction.

`PureCubicNodeBounds.rawNode_abs_bound` proves that every chart node lies strictly inside the cube of radius one sixteenth. `finite_node_denominator` supplies a common positive integer coordinate denominator below two to the power 138. `finite_cubic_row` clears every cubic evaluation row with a positive denominator below two to the power 414, and `node_monomial_bound` bounds every matrix entry by one in absolute value.

## Quantitative interpolation

`CubicMonomialBasis.degreeSet_fourteen_three_card` proves that the space has exactly 680 monomials. The proof gives an equivalence with multisets of size three over fourteen variable symbols and one padding symbol. `polynomial_reconstruct` reconstructs every cubic from its indexed coefficients.

`PureCubicInterpolation.coefficient_recovery` combines the actual finite kernel and denominator bounds with `FiniteKernelMinor.quantitative_kernel_recovery`. If all evaluations of a cubic at the finite raw chart have absolute value at most a positive error, every coefficient is within two to the power 300000 times that error of one scalar multiple of the explicit target. All kernel, rank, rational-denominator, and matrix-entry assumptions are discharged for the actual chart.

## Verification

The modules build with the repository's Lean toolchain. The audited principal declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; they contain no `sorry` or additional axioms. Exact indexing uses classical finite equivalences and does not require enumerating the enormous replicated Boolean cube.
