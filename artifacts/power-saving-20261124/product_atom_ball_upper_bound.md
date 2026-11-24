# A universal upper bound for affine product atoms

## Statement and scope

For every integer $n\geq1$ and every Boolean function $F:\lbrace0,1\rbrace^n\to\lbrace-1,1\rbrace$, there is a strict sign representation by at most

$$ \frac{2^n}{2^{\lfloor\log_2(n+1)\rfloor}}\lt\frac{2^{n+1}}{n+1} $$

affine-times-product atoms. All one-bit product factors can be strictly positive. No free bias is needed.

This is a universal upper bound for the product comparison class, not for original affine-ratio heads. It does not give a width-sensitive compiler from an original representation. Together with the prior original upper bound of order $2^n/(n\log n)$, it identifies the logarithmic factor between these two currently available universal constructions. It does not prove that either upper bound is optimal.

## A partition into small Hamming balls

Put $r=\lfloor\log_2(n+1)\rfloor$ and $k=2^r-1$. Thus $1\leq k\leq n$ and $k+1\gt(n+1)/2$.

There is a partition of the $k$-bit cube into Hamming balls of radius one. To see this, form the $r$ by $k$ binary matrix whose columns are all nonzero vectors in $\mathbb F_2^r$, and let $C$ be its kernel. The matrix has rank $r$, so $|C|=2^{k-r}$. For every vertex $x$, its syndrome is either zero, in which case $x\in C$, or equals exactly one column, in which case flipping that column's bit gives a unique codeword. Hence the balls of radius one about $C$ are disjoint and cover the cube. Each has $k+1=2^r$ vertices.

Apply this partition separately in each fiber of the last $n-k$ bits. The resulting patches partition the full cube. Their number is

$$ T=2^{n-k}|C|=\frac{2^n}{k+1}. $$

## One product atom per patch

Fix a patch with center $c\in\lbrace0,1\rbrace^k$ and fiber value $z\in\lbrace0,1\rbrace^{n-k}$. For an input $x=(u,v)$, let $y_i$ be one when $u_i\neq c_i$ and zero otherwise. Each $y_i$ is an affine function of the corresponding input bit. For $0\lt\varepsilon\lt1$, define the positive product weight

$$ W_{c,z}(u,v)=\varepsilon^{d(u,c)+2d(v,z)}, $$

where $d$ is Hamming distance. This is a product of one-bit factors, each equal to one, $\varepsilon$, or $\varepsilon^2$.

Let $c^{(i)}$ be the neighbor of $c$ obtained by flipping coordinate $i$. Define the affine prefactor

$$ L_{c,z}(u,v)=F(c,z)+\sum_{i=1}^k y_i\left(\frac{F(c^{(i)},z)}{\varepsilon}-F(c,z)\right). $$

The atom $L_{c,z}W_{c,z}$ equals $F$ exactly on its patch: at the center the product weight is one, and at each neighbor it is $\varepsilon$.

At every input, the affine prefactor obeys

$$ |L_{c,z}(u,v)|\leq1+k(\varepsilon^{-1}+1)\leq\frac{2k+1}{\varepsilon}. $$

Outside this patch, either $v\neq z$, or $v=z$ and $d(u,c)\geq2$. In either case the product weight is at most $\varepsilon^2$. Therefore the absolute contribution of this atom outside its patch is at most $(2k+1)\varepsilon$.

Sum the $T$ atoms, one per patch, and choose

$$ 0\lt\varepsilon\lt\frac1{2T(2k+1)}. $$

At any vertex, its own patch contributes exactly its desired sign, while the total absolute contribution of every other patch is less than $1/2$. Thus the sum has sign $F$ everywhere, with signed margin greater than $1/2$. This proves the stated bound. $\blacksquare$

## Verification boundary

This is an elementary written proof. No finite computation or Lean verification is claimed. The product factors are positive, but their coordinate directions may differ from atom to atom. The construction therefore does not assert any corresponding coherent affine-denominator representation or resolve the requested original head lower bound.
