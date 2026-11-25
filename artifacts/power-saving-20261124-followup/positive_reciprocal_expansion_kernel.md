# Exact positive reciprocal expansion in the kernel

## Statements

The file `formalization/HeadComplexity/Research/PositiveReciprocalExpansion.lean` closes the previously written positive-expansion ingredient. All declarations below are in namespace `HeadComplexity.PositiveReciprocalExpansion`.

For a finite coordinate set, let $c\gt0$, $w_i\geq0$, and $B(x)=c+\sum_iw_ix_i$. Let $F_S(x)$ be the indicator of the anchored face $x_S=0$. The theorem `reciprocal_with_endpoint_identities` proves the existence of coefficients $\kappa_S\geq0$ satisfying

$$ \frac1{B(x)}=\sum_S\kappa_SF_S(x),\qquad\sum_S\kappa_S=\frac1c,\qquad\sum_{S:i\notin S}\kappa_S=\frac1{c+w_i}. $$

The theorem `reciprocal_with_mass_bound` also supplies the weighted coefficient estimate

$$ \sum_S\kappa_S\left(c+\sum_{i\notin S}w_i\right)\leq n+1. $$

The stronger `ratio_with_full_cube_mass` proves, for every real-valued numerator function $A$ on the cube,

$$ \frac{A(x)}{B(x)}=\sum_S\kappa_SF_S(x)A(x),\qquad\sum_S\|\kappa_SF_SA\|_\infty\leq(n+1)\|A/B\|_\infty. $$

The norm in this declaration is Lean's finite function-space norm, hence the supremum of the absolute values over the entire Boolean cube. No denominator conditioning, coefficient magnitude bound, or sign restriction on $A$ is assumed. The statement for arbitrary $A$ is a decomposition and norm estimate; when $A$ is affine, `uniformlyOneAtomApproximable_face_affine` additionally supplies the genuine original-head approximation of each block.

Finally, `normalized_product_probability_expansion` proves that every finite product

$$ \prod_h\frac{c_h}{c_h+\sum_iw_{h,i}x_i} $$

is exactly a sum $\sum_S\kappa_SF_S$ with $\kappa_S\geq0$ and $\sum_S\kappa_S=1$. The number of factors does not enter this mass bound. This statement concerns constant-numerator factors of one coherent orientation. It does not extend to arbitrary signed affine numerators or opposite orientations without another argument.

## Finite proof

The proof uses no integration or limiting reciprocal series. Positive face expansions are closed under addition and multiplication, since $F_SF_T=F _{S\cup T}$. Coefficients for a product are grouped explicitly by the union of their two index sets.

Induct on the finite set of active denominator coordinates. Writing $T$ for the contribution from the remaining coordinates, the insertion identity is

$$ \frac1{c+T+w_ix_i}=\frac1{c+w_i+T}+w_i(1-x_i)\frac1{c+T}\frac1{c+w_i+T}. $$

Both shifted intercepts remain strictly positive. The identity holds for each of the two Boolean values of $x_i$, and all scalar coefficients in the inductive construction are nonnegative. Evaluation at zero and at each singleton gives the endpoint identities. The existing weighted mass identity then gives the coefficient bound.

For the norm estimate, restrict to the face where all coordinates in $S$ vanish. The denominator is then bounded by the intercept plus the weights outside $S$. Multiplying this bound by $\kappa_S\|A/B\|_\infty$ bounds the block norm. Summing gives the displayed full-cube estimate. All these steps, including the pointwise supremum bound, are kernel checked.

## Scope and remaining barrier

The subsequent module `OriginalAnchoredExpansion.lean` closes the original-model assembly as well. Its exact declaration `HeadComplexity.OriginalAnchoredExpansion.original_head_expansion` proves that every genuine `FracAtom` has an exact decomposition into blocks indexed by the cube's coordinate subsets, with every block uniformly approximable by one genuine original head, and

$$ \sum_S\|\mathrm{block}_S\|_\infty\leq(n+1)\mathrm{atomSup}(\phi). $$

The theorem handles both coherent denominator orientations by simultaneous complementation. The separate declaration `norm_eval_eq_atomSup` proves that the finite function-space norm agrees exactly with the supremum used in the requested relative-margin definition. No original model definition was changed. The limiting blocks themselves need not be exact single heads; their approximation by genuine heads is explicit in the statement.

The expansion has as many as $2^n$ face blocks. Its polynomial amplitude budget does not imply a width bound comparable to an arbitrary source width. Sampling still depends on the source margin. The classification-specific support-compression or representation-changing repair theorem needed for the requested lower bound remains open.

## Verification

`positive-reciprocal-expansion-build.txt` records a successful 2,542-job module build. `positive-reciprocal-expansion-axioms.txt` records all 17 transitive `#print axioms` checks. Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The final combined run also includes this module in the complete changed-module audit.

`original-anchored-expansion-build.txt` records the successful 4,029-job build of the all-original-head assembly. `original-anchored-expansion-axioms.txt` checks all five declarations in that module, with the same three standard axioms.

An independent audit checked the complete-cube norm, nonnegative versus strictly positive slopes, endpoint mass identities, and the distinction between exact face blocks and their genuine-head approximations. No additional margin or conditioning hypothesis was found.
