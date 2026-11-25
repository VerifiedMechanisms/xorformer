# Sparse grid compilation and the outside-control gap

## Written local theorem

Let $A$ be a ternary $r$ by $s$ matrix, with $s\leq r$, and let $m$ be its number of nonzero entries. For every fixed $\eta\in(0,2/3)$ and all sufficiently large $r$, the remote affine-plane construction admits an exact strict reverse grid module, zero on both axes, with

$$ O_\eta\left(r^{2/3}+m r^{-2/3+\eta}\right) $$

heads. The constants are absolute once $\eta$ is fixed. This is a written extension of the inspected construction, not a kernel-checked theorem. Its coefficient and full-cube norm bounds remain exponential in a polynomial of $r+s$. It is a local grid statement and is not a sparse-support compiler on the whole Boolean cube.

## Finite alphabets in the affine-plane decoder

The decoder in `Results/AffinePlaneCompiler.lean` accepts arbitrary tokens and row-specific Cauchy residues. Its Boolean-word application uses blocks of $a$ rows and the full alphabet of $2^a$ words. More generally, every row block may use its own alphabet of at most $q$ ternary words, where $q$ is a power of two and there are at most $q^2$ blocks.

For each block, inject its words into the token field, and prescribe the Cauchy decoder values separately for every row in that block. All other token values may be set to zero. The same incidence identity and correction remove the unwanted tokens. Thus $r\leq aq^2$ rows, with at most $q$ allowed words per block, use $2q^2+1$ strict grid heads before axis repair and at most $6q^2+6$ afterward. The bounds for prescribed values in $\lbrace-1,0,1\rbrace$ are identical to those for signs.

Set $a=\lceil r^{1/3}\rceil$ and choose the least power of two $q\geq2a+1$. A block with at most one nonzero entry has only $2a+1$ possible ternary words. Consequently any matrix with at most one nonzero entry per column in each block has an exact axis-zero module with $O(r^{2/3})$ heads. If every block-column has at most $k$ nonzeros, assign them in row order to $k$ layers and apply this construction to each layer.

## Partitioning the sparse columns

First remove every column with more than $T=r^{2/3-\eta}$ nonzero entries. There are at most $m/T$ such columns. For the remaining matrix, randomly permute the rows and partition them into blocks of size at most $a$.

For any fixed column and block, its occupancy has a hypergeometric tail bounded, for a fixed positive integer $k$, by

$$ \Pr[\text{occupancy}\geq k]\leq\binom ak\left(\frac{2T}{r}\right)^k\leq\left(\frac{2eaT}{kr}\right)^k $$

for all sufficiently large $r$. The factor two absorbs sampling without replacement. Since $aT/r=O(r^{-\eta})$, a union bound over at most $r^2$ block-column pairs is less than one when $k\eta\gt2$. Hence a suitable row partition exists with a constant number of layers depending only on $\eta$.

Each removed column costs only a constant number of heads. If its entries are $a_i$ and its column coordinate is $y_j$, let $U(z)=\sum_i a_i z_i$. On the one-hot product grid,

$$ 2\left(\frac{U(z)}{2-y_j}-\frac{U(z)}2\right)=U(z)y_j. $$

These two weak reverse heads have positive full-cube denominators. Adding a sufficiently small common multiple of $2-|z|-|y|$ to both denominators makes every slope strictly negative while leaving every grid value unchanged. The exact axis-repair construction then uses at most nine heads. Summing the sparse and removed-column modules proves the stated count.

## Why this does not give an unrestricted patch

Suppose $M$ exceptional cube vertices are assigned to product-star centers, with each vertex assigned exactly once. The local grids can then have a total of only $M$ nonzero entries, so the preceding local estimate is potentially useful.

The first global implication nevertheless fails: an axis-zero local module is unconstrained on deeper points of its center downset. Rank-weighted gluing guarantees the sign at a designated grid point because a leading correct contribution dominates every lower-scale contribution. At a nonexceptional point there is no designated leading contribution. Deeper-downset values can therefore be large and can have either sign. The construction does not approximate a correction supported only on the exceptional set.

One could eliminate this leakage by multiplying each module by the indicator of the corresponding global Hamming layer. There is currently no proved constant or sufficiently small overhead multiplication compiler for an arbitrary original denominator and that layer filter. Treating this product as a head would change the model.

There is also an earlier independent access gap: a fixed-denominator unit-gap linear program has a small active certificate, but this does not imply that only that many cube vertices have quantitatively small margin. The finite active-row certificate alone does not supply the set of exceptional vertices required by a sparse patch argument.

Thus the local theorem is positive construction evidence. Neither the global outside-control lemma nor the all-representation access lemma has been proved. An independent agent audited the finite-alphabet interface against the remote source, the random-partition estimate, the two-head column identity, and the stated global failure; all checks passed.
