# Support dimension and the degree obstruction

## A real-valued support bound

Let $P$ be a nonzero real function on the Boolean cube whose multilinear polynomial degree is at most $d\leq n$. Its support, viewed as a family of subsets of $[n]$, satisfies

$$ \mathrm{VC}(\mathrm{supp}P)\geq n-d. $$

The main real-degree theorem of [Chang and Fang](https://arxiv.org/html/2510.13705v1) is stated for Boolean-valued functions. It should not be applied directly to a cleared rational-score numerator. Their null-design lemma nevertheless gives the displayed real-valued extension, as the following independent argument verifies.

## Proof

Put $g(S)=(-1)^{|S|}P(1_S)$. If $A\subseteq[n]$ and $|A|\leq n-d-1$, then

$$ \sum_{S\supseteq A}g(S)=0. $$

Indeed, substitute the multilinear expansion of $P$. For a monomial indexed by $T$ with $|T|\leq d$, the corresponding sum is $\sum_{S\supseteq A\cup T}(-1)^{|S|}$. At least one coordinate lies outside $A\cup T$, and pairing sets which differ in that coordinate makes the sum zero.

More generally, let $g$ be any nonzero real function on subsets, and let $s$ be the largest integer for which all sums over supersets of sets of size at most $s$ vanish. If even the sum over supersets of the empty set is nonzero, the support already shatters the empty set, which is the only conclusion needed when $d=n$. Otherwise $s\geq0$. Because the zeta transform on the Boolean lattice is invertible, some superset sum is nonzero. Choose $T$ of size $s+1$ with

$$ a=\sum_{S\supseteq T}g(S)\neq0. $$

For $U\subseteq T$, let $g_T(U)=\sum_{S:S\cap T=U}g(S)$. The sums of $g_T$ over supersets of proper subsets of $T$ vanish, whereas its total over supersets of $T$ is $a$. Boolean-lattice inversion gives

$$ g_T(U)=(-1)^{|T|-|U|}a\neq0\qquad(U\subseteq T). $$

Every trace $U$ is therefore attained by a point of the support of $g$, so that support shatters $T$. In the application above, $s\geq n-d-1$, giving a shattered set of size at least $n-d$. Multiplication by $(-1)^{|S|}$ does not change support. $\blacksquare$

This is the argument behind the real-field instance of the cited paper's Lemma 2.3, with nonzero support explicitly required. The published phrase “supported on” must not be read as permitting the identically zero function in that lemma.

## Consequence and limitation for rational heads

A score with $H$ positive affine denominators has the same support as its cleared numerator

$$ P=c\prod_{h=1}^H B_h+\sum_{h=1}^H A_h\prod_{g\neq h}B_g. $$

This polynomial has degree at most $H$. If it is nonzero on the cube and $H\leq n$, its support has VC dimension at least $n-H$. This applies to arbitrary real numerators, arbitrary signed cancellation, and target-dependent denominators.

At either requested critical width, $H\gg n$, and Boolean multilinear reduction gives only degree at most $n$. The resulting support statement is then the trivial bound zero. It does not constrain the zero set left for later cancellation layers and does not yield a count of universally low-margin truth tables.

Thus this support theorem is valid in the real-valued setting after the proof above, but it does not repair the critical-width boundary argument. A useful replacement would have to control the localized complexity of supports in terms of a structural head budget, rather than only the cleared polynomial degree. This note is a written proof and source audit, not a Lean formalization.
