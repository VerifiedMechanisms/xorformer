# Two Heads Can Require Many Priority Lists

## Statement

A real-valued priority list inspects literals on distinct input coordinates in a fixed order. It returns a specified real constant at the first satisfied literal, and a specified default constant if none is satisfied. A signed or weighted list is included in this definition by changing its returned constants.

For every integer $k\geq1$, there is a Boolean function on $n=4k+2$ inputs with attention-head complexity exactly two, but any strict sign representation as an affine function plus a sum of $H$ priority lists requires $H\geq k+1$.

This is an obstruction to a proposed simplification of positive-denominator heads into priority rules. It does not prove an asymptotic worst-case lower bound for the head model itself.

## The two-head construction

Split the inputs into two disjoint blocks $x,y\in\lbrace0,1\rbrace^{2k+1}$ and set

$$ L_1(x)=\sum_i x_i-k-\tfrac12,\qquad L_2(y)=\sum_i y_i-k-\tfrac12,\qquad f_k(x,y)=\mathbf1\lbrace L_1(x)L_2(y)\gt0\rbrace. $$

Let

$$ D(x,y)=1+\sum_i x_i+\sum_i y_i,\qquad \delta=\frac1{2k+2}. $$

The score

$$ S(x,y)=\frac{L_1(x)}{D(x,y)}-\frac{L_1(x)}{D(x,y)+\delta L_2(y)}=\frac{\delta L_1(x)L_2(y)}{D(x,y)(D(x,y)+\delta L_2(y))} $$

strictly realizes $f_k$. Both denominators have strictly positive slopes on every coordinate. The second denominator's constant coefficient is $1-\delta(k+1/2)\gt0$, so both denominators are positive on the cube. Both numerators are affine, as allowed by the manuscript's head realization theorem. Thus two admissible heads suffice.

## A restriction lemma for lists

**Lemma.** Given $H$ priority lists, there is a partial assignment fixing at most $H$ coordinates on which all the lists become constant.

**Proof.** Process the lists one at a time. If the current list is already constant under the current partial assignment, make no change. Otherwise inspect its literals in order. Skip any literal already forced false. If a literal is already forced true before any unset literal, the list is already constant. In the remaining case, set the coordinate of the first unset literal to satisfy it. Earlier literals are forced false, so this fixes the list's output. At most one new coordinate is assigned at each step. Further restrictions preserve constancy of the lists already processed. $\blacksquare$

## The lower bound for lists

Suppose that an affine function plus $H\leq k$ lists strictly realizes $f_k$. Apply the restriction lemma. The resulting score is affine in the remaining variables.

At most $k$ coordinates in total have been fixed. Each block still admits completions with both signs of its majority margin: the number of fixed ones is at most $k$, so filling the remaining coordinates with zero gives a negative margin; the number of fixed zeros is at most $k$, so filling the remaining coordinates with one gives a positive margin.

Choose such completions $x^-,x^+$ in the first block and $y^-,y^+$ in the second. The function is positive on $(x^-,y^-)$ and $(x^+,y^+)$ and negative on $(x^-,y^+)$ and $(x^+,y^-)$. Every affine score $A$ satisfies

$$ A(x^-,y^-)+A(x^+,y^+)=A(x^-,y^+)+A(x^+,y^-). $$

Strict agreement would make the left side positive and the right side negative, a contradiction. Hence $H\geq k+1$.

The same rectangle argument with no restriction shows that $f_k$ is not a linear threshold function. One admissible head has the sign of an affine numerator after absorbing the output bias into its positive affine denominator. Therefore $H^{\ast}(f_k)\geq2$, completing the exact two-head claim. $\blacksquare$

## Consequence for the attempted counting method

There is no constant $C$ such that every $H$-head classifier can be represented by an affine score plus at most $CH$ priority lists. Apply the theorem with $H=2$ and $k+1\gt2C$.

This rules out that particular replacement mechanism. It does not rule out other uses of positivity or another sign-counting theorem. No assertion about the desired unbounded sequence follows from this auxiliary separation.

## The exact averaging representation does hold

There is an exact reason that priority lists are a plausible starting point. Let $w_0,\ldots,w_n\gt0$ and let $v_0,\ldots,v_n$ be arbitrary real numbers. Generate a random permutation of the indices by choosing each successive index with probability proportional to its weight among the remaining indices. Given $S\subseteq\lbrace1,\ldots,n\rbrace$, return the value at the first index of $\lbrace0\rbrace\cup S$ in this permutation. For a fixed permutation this is a priority list, with index zero specifying its default value. Its expectation is

$$ \mathbb E[L(S)]=\frac{w_0v_0+\sum_{i\in S}w_iv_i}{w_0+\sum_{i\in S}w_i}. $$

**Proof.** Put $A=\lbrace0\rbrace\cup S$. Induct on the number of indices outside $A$. If there are none, the first draw gives the formula immediately. Otherwise condition on the first drawn index. A draw in $A$ returns its value. A draw outside $A$ leaves the same set $A$ and, by induction, the expected value $T=(\sum_{i\in A}w_iv_i)/(\sum_{i\in A}w_i)$. Consequently the unconditional expectation is

$$ \frac{\sum_{i\in A}w_iv_i+\sum_{i\notin A}w_iT}{\sum_iw_i}=T. $$

The sampling rule supplies positive weights summing to one on the finite set of permutations, so this is also a finite convex-combination identity. $\blacksquare$

Taking $w_0=b_0$, $w_i=b_i$, $v_0=a_0/b_0$, and $v_i=a_i/b_i$ gives every affine ratio with positive denominator coefficients. The separation proved above shows exactly why this averaging identity does not imply a bounded-list representation with the same signs: even two such expectations can require arbitrarily many individual lists in a strict sign representation.
