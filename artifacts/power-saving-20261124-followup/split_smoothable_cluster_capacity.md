# Weighted capacity of real split smoothable clusters

## Status and scope

The uniform-length finite theorem is kernel checked as `HeadComplexity.SplitSmoothableCapacity.card_smoothableFunctions_le`. Its proof includes the adjugate matrix substitution, the exact positive determinant-clearing identity, and preservation of a full strict truth table in the real-topological closure of the split orbit. The Lean parameter `q` counts nonidentity vectors, so each cluster has length `q + 1`. The nonuniform-length formula, the simplified product-of-weights bound, and the asymptotic estimates below are written proofs, independently audited by the margin-repair agent. The sign-count input is the unconditional kernel-checked `HeadComplexity.weightedStrictPolynomialSignPatterns_card_le`.

The result improves the [filtered local algebra count](filtered_local_algebra_capacity.md) for algebras that are Euclidean limits of the split semisimple algebra. It reaches the requested power scale for this comparison class. It does not prove that every unrestricted xorformer truth table, or every universally low-margin table at comparable width, admits such a clustered representation.

## The exact smoothability premise

For a positive integer $q$, use a fixed basis $e_0,\ldots,e_{q-1}$ of $\mathbb R^q$. Let $\mu(M)$ be the multiplication law obtained by transporting coordinatewise multiplication through an invertible real matrix $M$. With basis vectors mapped to the columns of $M$, its structure coefficients are

$$ c_{ij\ell}(M)=\sum_{a=0}^{q-1}(M^{-1})_{\ell a}M_{ai}M_{aj}=\frac{\sum_a\mathrm{adj}(M)_{\ell a}M_{ai}M_{aj}}{\det M}. $$

The numerator is homogeneous of ordinary degree $q+1$, and the denominator is homogeneous of degree $q$. Thus each structure coefficient is a rational homogeneous function of degree one in the matrix entries.

Here **real split smoothable** means precisely that the complete multiplication tensor of the target algebra belongs to the Euclidean closure of

$$ \lbrace\mu(M):M\in\mathrm{GL}_q(\mathbb R)\rbrace. $$

This premise is stronger than a bare assertion of complex smoothability. It is the explicit closure property used by the proof. No unproved implication from a different notion of smoothability is used.

The target algebra has identity $e_0=1$ and an adapted filtration basis, as in the preceding note. Nearby transported laws need not have $e_0$ as identity and need not preserve the filtration. They are used only as parameter points of a fixed polynomial comparison score. Allowing all invertible matrices is a harmless enlargement of that parameter set.

## Finite theorem

Put $N=2^n$ and $d=n+1$. Fix cluster lengths $q_1,\ldots,q_G\geq1$, adapted filtration-order lists, and

$$ K=\sum_gq_g,\qquad Q=\max_gq_g,\qquad t=\sum_gq_g^2,\qquad p=1+2dK+t. $$

Consider strict scores of the form defined in the preceding note, where every cluster algebra is real split smoothable, every base denominator is positive on the full Boolean cube, and every real affine coefficient and signed cancellation is permitted.

If $p\leq N$, their number of strict truth tables is at most

$$ \left(\frac{4e(3+2Q)N}{p}\right)^p Q^{2dK}K^{dG+t}. $$

### Why strict labels transfer to matrix parameters

Let $P_x$ be the polynomial score obtained by clearing the positive base denominators in the filtered-algebra construction, for a Boolean vertex $x$. Its structure coefficients occur only in the permitted slots

$$ k_\ell\geq k_i+k_j. $$

Keep this exact slot mask fixed when evaluating $P_x$ on another multiplication tensor. At the target filtered law, this polynomial equals the positively cleared genuine reciprocal score. At nearby tensors, it remains a well-defined polynomial even if those tensors violate the filtration.

Fix all affine numerator and denominator coefficients of a strict target score. There are finitely many vertices, and every $P_x$ is nonzero at the target tensor. Continuity therefore supplies one neighborhood of the full list of cluster tensors on which every strict sign is unchanged. Choose, for every cluster, a matrix law in this neighborhood using its real split smoothability. This preserves the entire truth table simultaneously.

The matrix law is not claimed to represent the same inverse in the filtered algebra. The count applies to the polynomial with its original mask, which is the continuous function whose values were just compared.

### Weighted rational substitution

Give the affine coefficients the same weights as before:

$$ w(B_{g,0})=\frac1K,\qquad w(B_{g,i})=\frac{k_i}{q_g}+\frac1K,\qquad w(L_{g,i})=1-\frac{k_i}{q_g}\quad(i\geq1),\qquad w(L_{g,0})=w(c)=1. $$

For this step give every structure coefficient weight $1/K$. This is no larger than its earlier permitted weight

$$ \frac{k_\ell-k_i-k_j}{q_g}+\frac1K. $$

Consequently the previous weighted-degree bound of three still holds. Give every matrix entry weight $1/K$. The rational substitution $c_{ij\ell}=c_{ij\ell}(M_g)$ then has exactly the required homogeneous weight $1/K$.

A score monomial from cluster $g$ contains at most $q_g-2$ structure factors when $q_g\geq2$, and none when $q_g=1$. This is because the $m$-th nilpotent power contains $m-1$ multiplication factors and $m\leq q_g-1$.

After substituting all matrix laws, clear the rational expressions by multiplying the *entire* score by

$$ E(M)=\prod_g(\det M_g)^{2q_g}. $$

This multiplier is positive whenever all matrices are invertible. Its exponent exceeds every structure denominator exponent, so the result is a polynomial. The added weighted degree is exactly

$$ \sum_g\frac{2q_g^2}{K}=\frac{2t}{K}\leq2Q. $$

More explicitly, replacing $m$ structure factors of weight $m/K$ gives numerator weight $m(q_g+1)/K$; the remaining determinant power contributes $(2q_g-m)q_g/K$. Their sum is $m/K+2q_g^2/K$, which is the original contribution plus the stated clearing cost.

Thus every final Boolean evaluation polynomial has weighted degree at most $3+2Q$. Positivity of the common determinant multiplier preserves all the labels already transferred to the matrix parameters.

### Parameter and weight products

The free parameters consist of the bias, $2dK$ affine coefficients, and $t$ matrix entries. There are no hidden multiplication slots or auxiliary variables. The product of weights satisfies

$$ \prod_{a=1}^p w_a\geq Q^{-2dK}K^{-(dG+t)}. $$

Multiply all rational weights and the degree bound by a common positive integer. The weighted sign-count theorem now gives the claimed finite formula. Invertibility and positivity restrictions only reduce its parameter set. $\blacksquare$

## The two target scales for this comparison class

Allow ordered lists of cluster lengths satisfying $q\leq q_g\leq2q$, all filtration-order assignments, and total size at most $K_{\max}$. Include constants through the empty list. For every sufficiently large $n$, at most $2^{N/2}$ strict truth tables belong to this union in either of these regimes:

1. $q=\lceil\sqrt n\rceil$ and $K_{\max}\leq N/(1000n^{3/2})$.

2. $q=\lceil\log n\rceil$ and $K_{\max}\leq N\log n/(1000n^2)$.

**Estimate.** Set $c=1/1000$. We have $G\leq K/q$, $Q\leq2q$, and $t\leq QK$. Eventually $p\leq5nK\leq N$. The logarithm of the finite formula is

$$ p\log\left(\frac{4e(3+2Q)N}{p}\right)+2dK\log Q+(dG+t)\log K. $$

The first two terms are $o(N)$ at both scales. The number of compositions and filtration-order lists contributes at most $K_{\max}\log(4q)=o(N)$ as well.

At the first scale, eventually $\sqrt n\leq q\leq2\sqrt n$, $Q\leq4\sqrt n$, $d\leq2n$, and $\log K\leq n\log2$. Therefore

$$ dG\log K\leq2cN\log2,\qquad t\log K\leq4cN\log2. $$

At the second scale, eventually $\log n\leq q\leq2\log n$ and $Q\leq4\log n$, giving

$$ dG\log K\leq2cN\log2,\qquad t\log K\leq4cN\log2\frac{(\log n)^2}{n}=o(N). $$

In both cases the total is strictly less than $N\log2/2$ for every sufficiently large $n$. The empty list adds two tables, absorbed by this strict eventual gap. $\blacksquare$

## What remains unproved

This theorem counts all real split smoothable local algebras in the specified moderate-length window. It does not count arbitrary large clusters at the same cost, and it does not justify cutting a large local algebra into smaller ones.

The unrestricted missing lemma is a global, strict truth-table preserving access statement with the charged total-length budget, or an upper count for its excluded tables. To combine it with the high-margin result, that excluded set must be quantified over every comparable-width representation of each truth table. A low-margin certificate, a local algebra attached to one degeneration, or a weak limit with vanishing score coordinates does not establish this access statement.
