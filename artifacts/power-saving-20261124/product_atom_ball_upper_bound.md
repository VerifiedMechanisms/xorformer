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

## A fixed dictionary spans every real table

The same construction gives an exact linear-algebraic strengthening. There is a choice of $T$ positive product weights, depending only on $n$, such that their affine multiples span every real-valued table on the cube.

For each patch, keep its product weight $W_{c,z}$ and use the following $k+1$ affine prefactors:

$$ L_0=1-\sum_{i=1}^k y_i,\qquad L_i=y_i/\varepsilon\quad(1\leq i\leq k). $$

The resulting weighted functions equal the coordinate delta functions on their own patch. There are exactly $T(k+1)=N$ such functions in total. Index each by its designated vertex and let $E$ be their square evaluation matrix, with rows indexed by cube vertices. Every diagonal entry is one, and entries corresponding to other vertices of the same patch are zero.

At a vertex outside a function's patch, its product weight is at most $\varepsilon^2$. The center prefactor has absolute value at most $k$, while a neighbor prefactor has absolute value at most $1/\varepsilon$. Thus every off-diagonal matrix entry has absolute value at most $k\varepsilon$ when $0\lt\varepsilon\lt1$.

Choose $\varepsilon=1/(2Nk)$. Every row has sum of absolute off-diagonal entries strictly less than one. The matrix is invertible: if $Ea=0$, choose a coordinate of $a$ having largest absolute value; the equation in that row and strict diagonal dominance force that value to be zero. Consequently every real table has a unique expansion in these $N$ weighted affine basis functions.

Grouping the $k+1$ terms for each patch gives one affine prefactor multiplying its fixed positive product weight. This proves exact representation of every real table with the same $T$-atom dictionary. The factor choices are independent of the target, and only the affine numerators vary. The construction remains a statement about the product comparison class.

## A matching fixed-dictionary dimension obstruction

Suppose $K$ product weights are fixed independently of the target, and every Boolean sign table is represented strictly by affine multiples of these weights, without a separate free bias. Their attainable real tables form a linear space $V$ of dimension at most $(n+1)K$. In fact $V$ must equal the entire $N$-dimensional table space.

Otherwise choose a nonzero table $w$ orthogonal to $V$. Define a Boolean target to have the sign of $w$ at every nonzero coordinate, with arbitrary signs at its zero coordinates. Every real table strictly representing this target has strictly positive inner product with $w$, whereas every member of $V$ has inner product zero. This contradicts universality. Therefore

$$ K\geq\frac{N}{n+1}. $$

If a separate free bias is allowed, the same proof gives $(n+1)K+1\geq N$. Thus the fixed positive dictionary constructed above is within a factor two of the minimum possible dictionary size, even if only all strict Boolean signs are required. This lower bound does not apply when the product weights depend on the target.

## Verification boundary

This is an elementary written proof. No finite computation or Lean verification is claimed. The product factors are positive, but their coordinate directions may differ from atom to atom. The construction therefore does not assert any corresponding coherent affine-denominator representation or resolve the requested original head lower bound.
