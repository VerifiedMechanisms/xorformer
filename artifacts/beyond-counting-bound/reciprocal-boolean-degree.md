# The Global Degree of the Boolean Reciprocal Variety Is Already Large

## Statement

Let $E_n=\lbrace0,1\rbrace^n$ and let $L_n$ be the projectivized space of affine evaluation tables on $E_n$. Thus its coordinates are the linear forms

$$ \ell_x(a)=a_0+\sum_{i=1}^n a_i x_i,\qquad x\in E_n. $$

Let $R_n$ be the complex projective closure of the reciprocal tables $[1/\ell_x(a)]_{x\in E_n}$ wherever every denominator is nonzero. For every $n\geq1$,

$$ \deg R_n\geq 2^{n(n-1)/2}. $$

The same complex Zariski closure is obtained if the parameters are restricted to $a_0,a_1,\ldots,a_n\gt0$. Every point in that restricted parametrization has the same, all-positive sign table.

This theorem is an obstruction to replacing the global algebraic degree by $\exp(o(n^2))$ on the grounds that the query points are Boolean or the denominator coefficients are positive. It is not a lower bound for head complexity or for the number of sign tables.

## Proof

### Lemma 1. Comparison after reducing an integer matrix modulo two

Fix an order on the columns of an integer matrix. Let $M_{\mathbb Q}$ and $M_2$ be the represented matroids over $\mathbb Q$ and $\mathbb F_2$. Every independent set of $M_2$ is independent in $M_{\mathbb Q}$: a square minor that is nonzero modulo two is a nonzero integer. Consequently every circuit $C$ of $M_{\mathbb Q}$ contains a circuit $D$ of $M_2$.

Put $c=\min C$ and $d=\min D$. Then

$$ D\setminus\lbrace d\rbrace\subseteq C\setminus\lbrace c\rbrace. $$

Indeed, the only possible obstruction would be $c\in D\setminus\lbrace d\rbrace$. But $c\in D$ forces $d=c$, since $c$ is least in the larger set $C$.

A broken circuit is a circuit with its least element removed. Thus every set that contains no broken circuit of $M_2$ contains no broken circuit of $M_{\mathbb Q}$. If both matrices have rank $r$, their no-broken-circuit bases satisfy the same inclusion. The comparison of no-broken-circuit sets is formalized as `HeadComplexity.BrokenCircuitWeakening.noBrokenCircuit_mono`; the matrix reduction and degree interpretation here are written arguments.

### Lemma 2. Explicitly many binary affine bases without broken circuits

Identify a Boolean vector with its binary integer in $\lbrace0,\ldots,2^n-1\rbrace$, and use that order. Consider the columns $(1,x)$ over $\mathbb F_2$. For each $j=0,\ldots,n-1$, independently choose an integer

$$ 2^j\leq v_j\lt2^{j+1}. $$

Let $B=\lbrace0,v_0,\ldots,v_{n-1}\rbrace$. These $n+1$ augmented columns form a basis. Subtracting the column at zero from the other columns leaves a triangular binary matrix with diagonal entries one.

We claim that $B$ contains no broken circuit. Suppose otherwise, and write the circuit as $C=\lbrace w\rbrace\cup D$, where $w=\min C$ and $D=C\setminus\lbrace w\rbrace\subseteq B$. A circuit over $\mathbb F_2$ has its unique nonzero dependence supported on all its columns, with every coefficient one. In particular the bitwise sum of the points in $C$ is zero.

If $0\in D$, then $w\lt0$, which is impossible. Thus $D$ consists of selected $v_j$'s. It is nonempty, since none of the augmented columns is zero. If $D$ has just one point $v_j$, its bitwise sum forces $w=v_j$, contradicting that these are distinct circuit elements.

If $D$ has at least two points, let $k$ be the largest selected index and let $j\lt k$ be any other selected index. Only $v_k$ has a nonzero bit at position $k$, and none has a nonzero bit above it. The identity $w=\bigoplus_{v\in D}v$ therefore gives

$$ w\geq2^k\gt v_j. $$

This contradicts $w=\min C$. The claim follows.

Different choices give different bases because each dyadic interval contains exactly one selected point. Their number is

$$ \prod_{j=0}^{n-1}2^j=2^{n(n-1)/2}. $$

### Conclusion of the degree bound

The integer matrix with columns $(1,x)$ has rank $n+1$ over both $\mathbb Q$ and $\mathbb F_2$: the columns at zero and the coordinate vectors are a basis. Lemma 1 transfers every basis in Lemma 2 to a no-broken-circuit basis of its characteristic-zero matroid.

[Proudfoot and Speyer, Lemma 2](https://arxiv.org/pdf/math/0410069), identify the degree of the reciprocal linear space with the number of no-broken-circuit bases. The degree of a homogeneous affine cone equals the degree of its projectivization. Their result therefore gives the claimed lower bound for $R_n$.

### Positive parameters have the same complex closure

Suppose a homogeneous complex polynomial $F$ in the table coordinates vanishes on every table with $a_i\gt0$. Substitute $1/\ell_x(a)$ and multiply by a sufficiently large power of $\prod_x\ell_x(a)$. This gives a complex polynomial $G(a)$ vanishing on the real open positive orthant. Its real and imaginary parts both vanish on a real open box, so they are zero polynomials. For completeness, the last assertion follows by induction on the number of variables, applying the fact that a nonzero univariate polynomial cannot vanish on an interval to its coefficients one variable at a time.

Hence $F$ vanishes on the entire reciprocal parametrization wherever it is defined, and therefore on $R_n$. The vanishing ideals of the positive image and of $R_n$ agree. This proves equality of their complex Zariski closures. Every denominator, and hence every reciprocal, is positive on the restricted parameters. $\blacksquare$

## Relation to the recent polar-degree formula

[Briand, Kayser, and Weigert, Theorem A](https://arxiv.org/html/2606.26281v2), compute the polar degrees of a reciprocal linear space from the reduced characteristic polynomial of its matroid. Their indexing includes the ordinary degree as the zeroth polar degree. The theorem above therefore also bounds that term of their formula from below.

Their negative powers of linear spaces are coordinatewise powers of one linear-space point. They do not mean products of independently selected denominators from different heads. Neither the polar-degree formula nor the present lower bound counts the positive real orthants met by sums of admissible head scores. A transfer at that step remains unproved. The selected unboundedness target and every intermediate-exponent improvement remain open in this run.
