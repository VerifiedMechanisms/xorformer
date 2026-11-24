# Margin free counts for structured denominator configurations

## Scope

The positive affine denominators are normalized as $B_h(x)=1+b_h\cdot x$. All linear numerator coefficients and the output bias remain arbitrary real numbers. Signed cancellation is unrestricted. The counts concern every strict truth table that admits a representation in the specified denominator family, rather than only representations with a prescribed relative margin.

The finite counts below are kernel checked in `StructuredDenominatorCapacity.lean`, using the unchanged original-model normalization bridge `DenominatorCapacity.represented_of_affine`. The asymptotic estimates are written deductions from these finite formulas. Neither family is proved to contain every original narrow truth table.

Set $N=2^n$ and $L=nH+1$. The general chart theorem counts a polynomial denominator chart with $q$ real parameters and degree at most $D$ by

$$ 2^L{N+2L\choose L}\left(\frac{4e(2DHL+1)N}{q+1}\right)^{q+1},\qquad q+1\leq N. $$

The extra real variable in $q+1$ is the radius of the compact coefficient box used to select an active sample certificate. There is no head overhead.

## Varying polynomial curves

Suppose all normalized denominator slope vectors lie on a common polynomial curve of degree at most $r$. Both the curve and the point of each head on that curve may vary:

$$ b_{hi}=\sum_{j=0}^{r}c_{ij}t_h^j. $$

The chart has $q=n(r+1)+H$ real parameters and denominator degree $D=r+1$. The exact finite count is `HeadComplexity.StructuredDenominatorCapacity.card_curve_le`.

This condition does not bound the affine span by a small constant. The positive moment curve $t\mapsto(t,t^2,\ldots,t^n)$ has full affine span in dimension $n$, as follows from the Vandermonde determinant at $n+1$ distinct positive values of $t$. It is included with $r=n$.

For any fixed $k$ and $r\leq n^k$, the family has fewer than $2^{N/2}$ truth tables at width $H\leq cN/n$, for a sufficiently small absolute $c\gt0$ and all sufficiently large $n$ depending on $k$. Here is a direct estimate, with constants left deliberately loose.

It suffices to count width $H=\lfloor cN/n\rfloor$, because smaller curve configurations can be padded with arbitrary positive curve points and zero numerators. For large $n$, $q+1\leq2H$, $L\leq2nH$, and $H\leq N$. Also

$$ \log_2\left(\frac{4e(2(r+1)HL+1)N}{q+1}\right)\leq4n. $$

Thus the Warren term contributes at most $8nH\leq8cN$ bits. The discrete certificate term satisfies

$$ \log_2\left(2^L{N+2L\choose L}\right)\leq L\log_2\left(\frac{2e(N+2L)}{L}\right). $$

Writing $a=L/N\leq2c$, its ratio to $N$ is at most $a\log_2(2e(1+2a)/a)$, which tends to zero as $c$ tends to zero. For example, $c=10^{-4}$ makes this term plus $8c$ smaller than $1/2$ once the stated eventual inequalities hold. The polynomial degree bound affects the threshold in $n$, but not this absolute choice of $c$.

Consequently both benchmark widths, $cN/n^{3/2}$ and $cN\log n/n^2$, have logarithmic count $o(N)$ in every fixed polynomial-degree curve family. This conclusion includes full-affine-span denominator configurations and imposes no margin condition.

## Unions of varying affine planes

Now allow $G$ affine subspaces of dimension at most $d$, with an arbitrary assignment $g(h)$ of heads to them. Write

$$ b_h=b_{g(h),0}+\sum_{j=1}^d t_{hj}c_{g(h),j}. $$

For a fixed assignment the chart has $q=Gn(d+1)+dH$ and degree $D=2$. The declaration `card_cluster_assignment_le` gives the corresponding finite bound. The declaration `card_clustered_le` also counts all $G^H$ assignments, adding at most $H\log_2G$ bits. Counting assignments this way is intentionally loose and requires no quotient by head permutations.

For $1\leq G\leq H/n$ and $d\geq1$, one has $q\leq(2d+1)H$. Assuming $H\leq N/(2n)$ and $q+1\leq N$, the finite count gives

$$ \log_2|\mathcal F_{G,d}(n,H)|=O\left(nH\log\frac{eN}{nH}+ndH+H\log G\right). $$

The constants are absolute. The first term comes from active sample selection; the second comes from the nonlinear parameters; the last counts the assignments.

Thus the clustered family has fewer than $2^{N/2}$ tables at the benchmark width $H\leq cN/n^{3/2}$ when $d\leq c'\sqrt n$, for sufficiently small constants. The same conclusion holds at fallback width $H\leq cN\log n/n^2$ when $d\leq c'n/\log n$. In both cases the assignment term is $o(N)$.

## What is still needed

These estimates make precise why low jet rank need not be charged by codimension alone. Coordinate flat strata, polynomial curves with full affine span, and sufficiently large clusters in small affine spaces can instead be counted directly by their parameter charts.

The missing unrestricted theorem is a complete cover of all exceptional truth tables by such cheap charts, or by another family with a comparable total count. A statement about the rank or conditioning of one chosen denominator configuration does not establish that cover. The quantifier must allow every truth table represented at the original width and account for all comparable-width representations when declaring a table exceptional.
