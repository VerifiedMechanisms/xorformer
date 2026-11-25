# Margin-repair research handoff

## Outcome and exact open premise

This work did not prove a fixed-power or logarithmic improvement for the original unrestricted worst-case head complexity. No original model definition, denominator admissibility condition, or relative-margin definition was changed.

The missing premise still quantifies over truth tables and all comparable-width representations. At the benchmark width, one sufficient statement would be that every table represented with $H\leq c2^n/n^{3/2}$ original heads has some comparison representation with $K\leq CH$ heads and relative margin at least $\exp(-\exp(\sqrt n))$. The audited high-margin count would then exclude universality after choosing $c$ small enough for the overhead $C$. Approximate-label and polynomial-overhead healthy-margin variants are also sufficient through the root agent's counting interfaces. None of those access premises was established.

The strongest fixed-denominator obstructions below quantify over every coefficient refit and every allowed repetition. They still do not imply that the underlying table lacks a good representation with new denominators.

## Kernel-checked positive results

`Research/IntegerSeparatorMarginRepair.lean` proves `HeadComplexity.IntegerSeparatorMarginRepair.one_head_repair` and `repair_of_HStar_le_one`. These repair every original one-head truth table using a bounded integer affine separator and a genuine positive affine denominator. The determinant hypotheses and original-head bridge are explicit.

`Research/OneHeadLayerAverages.lean` proves `affine_ratio_budget`: every affine ratio with positive denominator on the complete five-bit cube, unit signed gap for the threshold at Hamming weight two, and uniform norm at most $K$ satisfies $K\geq(11+4\sqrt6)/5$. This permits arbitrary denominator slope signs and uses five cyclic singleton rows, five cyclic adjacent-pair rows, and the two endpoints. `witness_layer_bounds` verifies all six layers of the sharp positive-slope ratio. The 15 declarations are kernel checked with the standard three axioms, and the module build completed with 3833 jobs in commit `52daaaa0`.

The capacity agent's `OneHeadOriginalMarginOptimum.hasRelativeMargin_iff` completes the original-model bridge: this truth table has a width-one representation of relative margin at least $\gamma$ exactly when $\gamma\leq5/(11+4\sqrt6)$. `exists_attaining` constructs a genuine positive-slope optimizer, and `exists_no_same_width_improvement` quantifies over every original width-one replacement with arbitrary bias. These are kernel checked in commit `7d03b376`. They refute an unconditional width-preserving improvement to margin one, while leaving constant-overhead repair at the task's tiny target margins open.

`Research/LowDegreeMarginRepair.lean` proves `exists_integer_monomial_separator`. The finite-margin agent's `MonomialMarginCompiler.hasRelativeMargin_of_thresholdDegree` converts this into width equal to the number of degree-bounded monomials and margin $1/(2D D!+1)$. This is useful at small degree, but the generic degree bound is too large at critical width.

`Research/UniversalCubeMargin.lean` proves `HeadComplexity.UniversalCubeMargin.hasRelativeMargin_universal`: every truth table has an original width $2^n$ representation with relative margin at least $1/(2\cdot3^n+1)$. The theorem uses the exact Boolean monomial expansion and full-cube coefficient mass. It does not assume that an arbitrary mixed vertex indicator is one-head admissible.

`Research/LinearCylinderMargin.lean` proves `HeadComplexity.LinearCylinderMargin.hasRelativeMargin_of_cylinder_affine_sum`. It preserves a complete unit-gap scalar score expressed as affine functions on mixed cylinders, with explicit head cost and full-cube amplitude. This permits arbitrary signed cancellation among the blocks.

`Research/ActiveMarginImprovement.lean` proves `HeadComplexity.ActiveMarginImprovement.exists_strict_margin_improvement` and `exists_improvement_of_active_interpolation`. They justify a finite strict improvement when every active constraint receives enough signed correction relative to the patch amplitude. They do not prove a quantitative improvement size, a bound on iteration count, or recycling of the additional heads.

`Research/ExceptionalMarginRepair.lean` proves `HeadComplexity.ExceptionalMarginRepair.relativeMargin_ge_of_exceptional_patch`. If a strict source score has relative gap at least $\tau$ outside an exception set, and a patch has unit signed gap on that set and full amplitude at most $B$, then the concatenated original heads achieve full relative margin at least $\tau/(3B)$. Patch signs outside the exception set may be arbitrary. The missing issue is producing the quantitative exception-set premise for every narrow table.

All these modules built successfully, and their recorded exported-declaration audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Written quantitative constructions

`partial_label_grid_margin_compiler.md` proves a healthy original-head compiler for arbitrary prescribed labels on $M$ cube points, with unrestricted values elsewhere. For any fixed $0\lt\eta\lt1$, its width is

$$ O_\eta\left(\frac{2^n\log^4(n+1)}{n^2}+\frac{\sqrt{2^nM}\log^2(n+1)}{n^{1-\eta/2}}\right), $$

and its full-cube amplitude is $\exp(O_\eta(n^2\log(n+1)))$. The remote grid decoder, common row partition, occupancy estimates, all-incidence signs, rank gluing, and residual point patches were independently audited. This construction does not show that merely tiny slack is confined to $O(nH)$ points.

`universal_log_width_quantitative_margin.md` assembles a healthy-margin version of the inspected remote universal logarithmic-saving upper construction: width at most $2323202\cdot2^n/(n\log n)$ and margin at least $\exp(-100n^2\log(n+1))$ for $n\geq32$. This is a written assembly using the identified remote revision, not a claim that the remote universal theorem was imported or rebuilt locally.

`approximate_hamming_pencil_repair.md` jointly repairs arbitrary signed Hamming-pencil scores on at least $63/64$ of the cube using $O(\sqrt n)$ genuine heads and margin $\exp(-O(n\log n))$. The argument refits whole central layers, not individual heads. Arbitrary weighted statistics need not have only $O(\sqrt n)$ typical values; the weighted-pencil Cramer estimate remains too weak.

`scalar_cylinder_exponential_mass.md` improves scalar mixed-cylinder amplitude to $(r+1)32^r$ at width $\max(1,r)$, where $r$ is the smaller literal count, independently of approximation tolerance. `positive_product_compilation_boundary.md` identifies the positive constant-numerator product class where anchored probability mixtures give a product-length-independent sampling theorem. Neither construction supplies a sign-preserving compiler for arbitrary original sums.

## Decisive failed inequalities and their scope

`partial_label_grid_margin_compiler.md` includes a fixed-denominator majority example. Every numerator refit with arbitrary repeated copies has relative signed gap at most $4\epsilon$ on a designated $7/8$ of the cube. Changing to a genuine strictly positive affine denominator gives a one-head repair of margin greater than $1/4$. Thus optimizing coefficients with denominators frozen cannot supply the desired almost-everywhere margin premise.

The shared-direction notes and the finite-margin agent's `approximate_shared_direction_obstruction.md` exclude fixed-direction healthy repair even with arbitrary new pole positions, arbitrary width, and $15/16$ label agreement for suitable tables. New denominator directions remain allowed by the unrestricted problem and are not excluded.

`active_margin_improvement_and_recycling_gap.md` gives an abstract dictionary where every active-set interpolation has small support and perfect outside control, yet every fixed-width representation remains arbitrarily ill-conditioned. This rules out an abstract inference from local improvement to constant-overhead global repair. It is not an original-model counterexample.

`mixed_cylinder_dense_obstruction.md` gives a sign-only, critical-width obstruction to a universal exact mixed-cylinder compiler with only polylogarithmic overhead. The same bad family has a healthy approximate compiler in `approximate_mixed_cylinder_repair.md`. Exact-label and approximate-label access therefore must be distinguished.

`hamming_layer_gate_lower_bounds.md` proves a written unrestricted $\Omega(\sqrt n)$ head lower bound for uniform constant-error value approximation of a central Hamming-layer gate, using denominator symmetrization and the checked primary Paturi theorem. `Research/ExactLayerGateLowerBound.lean` kernel checks the exact nonnegative single-layer gate lower bound $H\geq n$. These are value-compilation statements, not lower bounds for the gate's truth table.

`mixed_point_high_order_amplitude.md` proves, for every width, the value-approximation bound

$$ D\geq\frac{1-4^k\epsilon}{2n+1}\min\left\lbrace\binom rk,\binom sk\right\rbrace. $$

It forces exponential amplitude for arbitrarily accurate balanced mixed-point gates. Exponential amplitude is still compatible with the healthy margins needed in this task.

`opposite_two_head_bounded_closure.md` proves that one positive and one negative head of bounded individual norms cannot approach a mixed point with at least two literals of each sign. Combined with the inherited same-orientation endpoint obstruction and scalar upper compiler, the six-bit gate $111000$ has bounded-amplitude approximation width exactly three. The full compactness theorem is written and independently audited by both other agents. `Research/ReciprocalHalfFaceGeometry.lean` checks three supporting inequalities; its build completed with 3137 jobs, and all three exported declarations have the standard three axioms.

Finally, `Research/GlobalParityMargin.lean` proves `HeadComplexity.GlobalParityMargin.relativeMargin_parity_le`, an all-representation bound $\gamma\leq2/2^n$ for parity at every width. This is a genuine unrestricted margin statement, but its scale is much larger than either target margin. Together with the universal healthy-margin upper construction, it shows why a dual certificate that forgets width cannot by itself establish the required low-margin exception class.

## Remaining next lemma

A successful continuation must prove a global new-representation access statement, count the truth tables for which every comparison representation fails it, or replace the margin argument. No frozen-denominator, individual-head, local-optimum, or positive-quadrature result above implies that global quantifier.

One density-specific capacity target remains plausible but unproved: control the relevant Boolean evaluation-map extension branches on an address cube of dimension about $\log_2(nH)$, including singular strata, by $\exp(O(nH\log n))$. At critical width only $O(\log n)$ coordinates remain outside the address cube; the explicit selector/permutation constructions respect this budget. Generic polynomial degree, local injectivity, and the existing small-width branch examples do not prove this bound.

`exact_address_fiber_capacity_gap.md` identifies an additional singular-fiber obstruction: at width one, exactly the same constant score on an address face admits $2^{m^2}$ distinct extensions in $2m+1$ dimensions. More generally every original width $H$ table embeds into an exactly constant face fiber at width $2H+1$ in one extra dimension. The full embedding is written and independently audited; `SameFaceScoreFiber.lean` checks the identity and a genuine differing-table pair. `RelativeMarginRestriction.hasRelativeMargin_restrict` kernel-checks that every healthy repair of such an embedding restricts to a healthy repair of its original table.
