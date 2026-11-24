# Affine Address Budgets and Permutation Symmetries

## Scope

The earlier [critical-scale audit](critical-scale-address-audit.md) computes the size of two particular factorial interpolation constructions. This note gives two structural bounds that do not require standard coordinate addresses: an affine-section bound for independently selected interpolation blocks, and an exact symmetry classification for a generic reciprocal array.

Neither statement bounds all isolated interpolation solutions or all full-cube sign patterns. In particular, equality at specially chosen parameter points need not arise from a symmetry of the entire observation map. The unrestricted lower-bound target remains open.

## Affine sections of the cube

**Lemma 1.** If a nonempty affine subspace $V\subseteq\mathbb R^n$ has dimension $d$, then

$$ |V\cap\lbrace0,1\rbrace^n|\leq2^d. $$

**Proof.** On the direction space of $V$, the coordinate functionals span the dual space. Choose $d$ of them that form a basis. Projection to these coordinates is injective on $V$: the difference of two points with the same projection is annihilated by a basis of the dual and hence is zero. The selected coordinates of a Boolean point have at most $2^d$ possible values. $\blacksquare$

Let $L_1,\ldots,L_s$ be affine forms on $\mathbb R^n$. Suppose each block has a nonempty set of Boolean queries $Q_j$ on which

$$ L_j(x)\neq0,\qquad L_i(x)=0\quad(i\neq j). $$

**Theorem 2.** Every block satisfies $|Q_j|\leq2^{n-s+1}$. Consequently, if every block needs at least $2H$ distinct queries, then

$$ s\leq n-\log_2H. $$

**Proof.** The affine forms are linearly independent as functions. Indeed, evaluate a linear relation at any point of $Q_j$ to force the coefficient at index $j$ to vanish, and repeat for every $j$.

Fix a block $j$. The equations $L_i=0$ for $i\neq j$ are consistent because $Q_j$ is nonempty. Their linear parts are independent: a dependence of the linear parts would give a constant linear combination of the affine forms; evaluating it at a common zero shows that this constant is zero, contradicting their independence. Their common zero set therefore has dimension $n-s+1$. Lemma 1 gives the cardinality bound. Taking logarithms of $2H\leq2^{n-s+1}$ gives the last assertion. $\blacksquare$

This covers oblique affine selectors and selectors whose nonzero value varies within a block. It does not cover jointly coupled queries in which several selector forms are nonzero. If a construction has $s$ independently permuted lists of $H$ poles and each list has at least $2H$ distinct queries selected as in Theorem 2, its raw permutation count is bounded by

$$ (H!)^s\leq2^{H\log_2H\log_2(2^n/H)}. $$

This is a bound on the stated parameter choices, not on every possible representation or even on the number of distinct signs within all parameter families.

## Generic column permutations

Fix $H\geq2$, $n\geq1$, and $c\gt0$. Let $b_{hi}\gt0$ be independently variable real coefficients. For a Boolean support $S\subseteq[n]$, define the actual constant-numerator head sum

$$ T_S(b)=\sum_{h=1}^H\frac1{c+\sum_{i\in S}b_{hi}}. $$

A tuple of permutations $\sigma=(\sigma_1,\ldots,\sigma_n)\in\mathfrak S_H^n$ acts by $(\sigma b)_{hi}=b _{\sigma_i(h),i}$. For a query set $Q\subseteq\lbrace0,1\rbrace^n$, let $G_Q$ be the graph on $[n]$ joining distinct coordinates that are simultaneously one at some query. Let its connected component sizes be $d_1,\ldots,d_k$.

**Theorem 3.** The identities $T_S(\sigma b)=T_S(b)$ hold for every query support $S$ and every positive coefficient array $b$ if and only if the permutations $\sigma_i$ are equal within each connected component of $G_Q$. Thus the identity symmetry group has cardinality $(H!)^k$.

**Proof.** If the permutations agree within each component, every nonempty query support lies in one component. Its row sum is merely permuted, and its reciprocal sum is unchanged. The empty query is constant.

Conversely, suppose $i,j\in S$ and the identity holds on the positive open coefficient domain. Set all coefficients equal to a fixed positive number $a$ and differentiate once in $b_{ri}$ and once in $b_{tj}$. With $D=c+|S|a$, the mixed derivative of $T_S$ is $2D^{-3}$ if $r=t$, and zero otherwise. For the permuted table it is $2D^{-3}$ if $\sigma_i^{-1}(r)=\sigma_j^{-1}(t)$, and zero otherwise. Equality of these derivatives for all $r,t$ says that the two permutation matching relations agree with equality. Taking $r=t$ proves $\sigma_i^{-1}(r)=\sigma_j^{-1}(r)$ for every $r$, so $\sigma_i=\sigma_j$. Propagate this conclusion along every graph path. $\blacksquare$

## Many queries restrict this symmetry mechanism

Write $m=|Q|$ and $N=2^n$.

**Theorem 4.** The number $k$ of components satisfies

$$ m\leq1+\sum_{j=1}^k(2^{d_j}-1)\leq2^{n-k+1}+k-1. $$

In particular, if $m\geq2n$, then

$$ k\leq\log_2(N/m)+2. $$

**Proof.** Every nonempty query support is contained in a single connected component, giving the first bound. For positive integers $a,b$, one has $2^a+2^b\leq2^{a+b-1}+2$. To verify this, assume $a\geq b$. Then $2^{a+b-1}-2^a=2^a(2^{b-1}-1)\geq2(2^{b-1}-1)=2^b-2$. Repeatedly merge two parts while leaving a part of size one. This shows that the largest sum of powers with $k$ positive parts totaling $n$ is $2^{n-k+1}+2(k-1)$. The second bound follows.

If $m\geq2n$, then $m-k+1\geq m-n+1\geq m/2$. The preceding inequality implies $2^{n-k+1}\geq m/2$. Taking logarithms proves the last display. $\blacksquare$

For an array with distinct entries in every column, the symmetry action is free. Quotienting its orbit by simultaneous row relabeling leaves exactly $(H!)^{k-1}$ points. If a regular observation system has $nH$ independent coefficient directions, it must use at least $nH$ queries. When $H\geq2$, Theorem 4 then yields

$$ \log_2\bigl((H!)^{k-1}\bigr)\leq H\log_2H\bigl(1+\log_2(N/(nH))\bigr). $$

For fixed $1\lt x\lt2$ and $H=\lfloor N/n^x\rfloor$, eventually $N/(2n^x)\leq H\leq N/n^x$. Therefore this last logarithm is at most

$$ nH\bigl((x-1)\log_2n+2\bigr). $$

The conclusion concerns multiplicity generated by the specified identity symmetry group. It does not bound additional solutions not in that group orbit, and it does not replace a count of strict sign tables.

## Essential boundary of the generic-array hypothesis

The independent-coefficient hypothesis in Theorem 3 cannot be silently replaced by a common-level permutation family. For example, take $H=3$, distinct positive levels $a,b,d$, and first column $(a,b,d)$. The second columns $(b,d,a)$ and $(d,a,b)$ give identical full two-bit reciprocal tables: singleton sums agree, and the doubleton sums both equal

$$ \frac1{c+a+b}+\frac1{c+b+d}+\frac1{c+d+a}. $$

After fixing the first column, these two arrays are not related by a simultaneous row permutation. Their equality exploits the tied levels. Nor does Theorem 3 apply when a permutation preserves prescribed observations only at isolated parameter points rather than throughout the positive parameter domain.

Thus these results quantify two specific address and symmetry mechanisms. Extending them to arbitrary coupled observations, tied levels, and non-symmetry interpolation multiplicity would require additional theorems. None is assumed here, and neither result supplies the desired fixed-exponent lower bound.

## Verification

These are complete written proofs. `verify_affine_address_budget.py` checks finite symmetry groups through their exact quadratic coefficient tensors, the component-size inequality, and the tied-level counterexample using rational arithmetic. There are no new Lean declarations in this note.
