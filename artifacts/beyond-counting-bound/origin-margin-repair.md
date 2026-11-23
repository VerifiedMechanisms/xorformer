# Unit Origin Margin Costs At Most One Additional Head

## Statement

Let $f$ be any Boolean function on $n$ bits that has an admissible $H$-head representation in the manuscript's exact model. It has an admissible $(H+1)$-head representation with score $T$ such that, writing $y(x)\in\lbrace-1,1\rbrace$ for its labels,

$$ T(0)=y(0),\qquad y(x)T(x)\geq1\text{ for every }x,\qquad y(x)T(x)\gt3/2\text{ whenever }x\neq0. $$

There is no restriction on the original embedding dimension, precision, or margin. This is an auxiliary normalization construction. It proves no asymptotic head lower bound.

## Explicit construction

Strictify the original score $S$ using the manuscript's finite-cube strictification lemma. Put

$$ \delta=\min_x y(x)S(x)\gt0,\qquad \sigma=y(0),\qquad q=2/\delta,\qquad K=\sigma qS(0)-1,\qquad M=2K. $$

The origin margin gives $\sigma qS(0)\geq2$, so $K\geq1$ and $M\gt0$. Multiply the original readout and numerators by $q$, and append the one head

$$ T(x)=qS(x)-\frac{\sigma K}{1+M\sum_i x_i}. $$

Its numerator is constant and its denominator has positive constant coefficient one and strictly positive, coherent slopes $M$. The positive-affine-ratio realization theorem makes it a genuine admissible attention head, with no approximation or limiting parameter.

At the origin, $\sigma^2=1$ gives

$$ T(0)=qS(0)-\sigma(\sigma qS(0)-1)=\sigma. $$

For every other vertex, $\sum_i x_i\geq1$, so

$$ 0\lt\frac{K}{1+2K\sum_i x_i}\leq\frac{K}{1+2K}\lt\frac12. $$

Since $y(x)qS(x)\geq2$, subtracting a term of absolute value less than one half leaves signed score strictly greater than $3/2$. This proves every claimed margin. $\blacksquare$

In the manuscript's normalized parametrization, removing the new head's constant numerator uses the exact identity

$$ -\frac{\sigma K}{1+Mt}=-\sigma K+\frac{\sigma KMt}{1+Mt}. $$

Together with the corresponding constant removals for the original heads, the normalized constant equals the actual origin score $\sigma$. Thus the construction applies to that parametrization as well.

## Why one cannot silently keep the head count unchanged

For $n\geq2$, take the label that is negative only at the all-one vertex. The affine score $2n-1-2\sum_i x_i$ realizes it with one head and unit margin. Suppose a one-head representation with origin value one also had unit margin. Write it as

$$ R(x)=1+\frac{u\cdot x}{B(x)},\qquad B(x)\gt0. $$

Each singleton vertex is positive, so $R(e_i)\geq1$ forces $u_i\geq0$. Consequently $R(1,\ldots,1)\geq1$, contradicting its negative label. This argument even allows arbitrary positive denominator tables. An additional head is sometimes necessary for this normalization.

## Verification and remaining gap

`HeadComplexity.OriginMarginRepair.computable_origin_margin_repair` constructs the extra genuine fractional atom from an arbitrary exact-model representation, including strictification and the finite minimum margin. The quantitative estimate, normalization identity, and singleton obstruction are also kernel checked in `OriginMarginRepair.lean`.

The additive cost of one head is negligible at the requested exponential scale. It repairs this normalization issue, but supplies neither a bound on the number of local minima nor a count of realizable signs. Those remain unproved. No original definition or target statement has been changed.
