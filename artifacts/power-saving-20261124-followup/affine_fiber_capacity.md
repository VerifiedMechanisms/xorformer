# Capacity from few joint denominator observations

## Kernel-checked finite theorem

Let $N=2^n$ and $K\geq1$. Consider all truth tables having an original-model representation, with any finite number of heads, for which the joint denominator observation vector

$$ x\longmapsto(B_1(x),\ldots,B_H(x)) $$

takes at most $K$ distinct values on the Boolean cube. The denominator family may depend on the target, every numerator and the bias are arbitrary real coefficients, and arbitrary signed cancellation is allowed. No margin condition is imposed.

If $n^2+1\leq N^2$ and $(n+1)K\leq N$, the number of such tables is at most

$$ \left(\frac{4eN^2}{n^2+1}\right)^{n^2+1}\left(\frac{4eN}{(n+1)K}\right)^{(n+1)K}. $$

A simpler integral bound is

$$ 2^{(2n+4)(n^2+1)+(n+4)(n+1)K}. $$

These are the declarations `card_originalFunctions_le` and `card_originalFunctions_le_pow` in namespace `HeadComplexity.AffineFiberCapacity`, file `formalization/HeadComplexity/Research/AffineFiberCapacity.lean`. The class `originalFunctions` quantifies over every finite original head count. Its predicate `HasAtMostFibers` means that some map from the cube to $\mathrm{Fin}(K)$ has exactly the same equality fibers as the full denominator observation map. This is equivalent to the stated cardinality restriction and does not prescribe the partition in advance.

The theorem `card_originalFunctions_le_half_tables` gives the exact finite consequence when

$$ (2n+4)(n^2+1)+(n+4)(n+1)K\leq N/2. $$

In particular, the written asymptotic consequence is that $K\leq N/(100n^2)$ suffices for every sufficiently large $n$. If a proposed access alternative has $K\leq H/\exp(\sqrt n)$ at $H\asymp N/n^{3/2}$, or $K\leq H/\exp(n/\log n)$ at the logarithmic fallback width, its contribution is much smaller still. No such access alternative has been established for arbitrary original truth tables.

## Proof and original-model bridge

Write the affine denominator slopes as $b_{hi}$. Constants do not affect equality of two observations. The joint squared distance is

$$ \sum_h(B_h(x)-B_h(y))^2=\sum_{i,j}G_{ij}(x_i-y_i)(x_j-y_j),\qquad G_{ij}=\sum_hb_{hi}b_{hj}. $$

Choose a positive $\varepsilon$ smaller than every nonzero distance in this finite list. Then

$$ \varepsilon-\sum_{i,j}G_{ij}(x_i-y_i)(x_j-y_j) $$

is positive exactly when the two joint observations agree, and negative otherwise. This is a polynomial of degree one in the $n^2+1$ free parameters consisting of $G$ and $\varepsilon$. Allowing arbitrary real matrices enlarges the family. Warren's theorem over the $N^2$ ordered pairs gives the first factor. This construction is formalized in `gram_identity` and `observationRelation_mem`.

For each counted relation choose one canonical code of its at most $K$ classes. On a fixed class every denominator is constant, so the entire score is an affine function of the Boolean input. The corresponding comparison class has $(n+1)K$ arbitrary coefficients and degree-one score polynomials, giving the second factor. The coefficient choice for each class absorbs every original numerator and the bias. The declarations `exists_fiber_affine_score` and `mem_represented_of_original` prove this bridge for genuine `FracAtom` heads. No rescaling or head replacement is required.

The union over all counted partitions proves the finite formula. For the integral version, use $12N^2\leq2^{2n+4}$ and $12N\leq2^{n+4}$ in the coarse Warren bound. All listed declarations have transitive axiom set contained in `[propext, Classical.choice, Quot.sound]`.

## Sharper partition count, written only

There is an elementary improvement of the first factor to $N^{2n}$. Let $L$ be the linear observation map and put

$$ \Delta=\lbrace x-y:x,y\in\lbrace0,1\rbrace^n\rbrace,\qquad V=\mathrm{span}(\Delta\cap\ker L). $$

Choose a basis for $V$ from the displayed generating set, of size at most $n$, and pad it with zero vectors to a list of length $n$. Each entry has at most $N^2$ choices of an ordered pair representing it. For every cube pair, its difference belongs to $\ker L$ if and only if it belongs to $V$. Thus this list determines the complete partition, and there are at most $N^{2n}$ partitions.

Consequently the same original class satisfies the stronger written bound

$$ N^{2n}\left(\frac{4eN}{(n+1)K}\right)^{(n+1)K}. $$

Only the Gram-matrix version is currently formalized. Both versions are counts of truth tables over all partitions and all coefficient choices, rather than a statement about one badly conditioned representation.

## Remaining gap

Few distinct observations are different from low affine rank. A rank $d$ linear map has at least $2^d$ distinct Boolean observations because independent image columns give distinct subset sums. The converse estimate $d\leq\log_2K$ is useful at small $K$, but at $K\asymp H/\exp(\sqrt n)$ it may still allow $d$ close to $n$. The fiber count above remains inexpensive in that regime.

Generic positive denominator slopes can distinguish every Boolean input, giving $K=N$. The theorem therefore does not bound the entire unrestricted class. What remains needed is a sign-preserving representation or truth-table decomposition which places every insufficient-margin target into this class, the ordinary Cayley–Bacharach class, or another comparably small class.
