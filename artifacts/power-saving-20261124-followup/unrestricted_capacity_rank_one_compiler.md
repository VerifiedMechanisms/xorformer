# A residue-degree obstruction to fixed rank-one compilers

## Statement and scope

Let $u_x=(1,x)\in\mathbb R^{n+1}$ for $x\in\lbrace0,1\rbrace^n$. Suppose a fixed finite family of linear maps $M_j:\mathbb R^{n+1}\to\mathbb R^{n+1}$ has rank at most one, and fixed polynomial residues $L_j(x)$ have degree at most $d$. Suppose the following identity holds for every parameter vector $w$, every Boolean query $x$, and every scalar function $F:\mathbb R\to\mathbb R$:

$$ F(u_x\cdot w)=\sum_j L_j(x)F(u_x\cdot M_jw). $$

Then $n\leq d+1$. In particular, affine residues do not permit such a compiler on three or more effective Boolean coordinates, regardless of how many rank-one maps are used.

This is a written theorem about a fixed linear recipe. The polynomial-selector step is kernel checked in `HeadComplexity.RankOneCompilerSelector.dimension_le_of_product_selector` and `no_affine_product_selector`. The reduction from the functional identity to that selector is proved below but is not formalized. The theorem does not rule out data-dependent maps, a global compiler coupling different heads, approximation preserving only signs, or a comparable-width margin repair.

The identity can be required merely on a nonempty open set of parameter vectors. The proof only needs a generic parameter vector avoiding finitely many proper hyperplanes inside that set. Thus positivity restrictions do not rescue this particular fixed recipe.

## Isolating a right direction

Write each nonzero rank-one map as $M_j=p_jq_j^\top$. Fix a target vertex $y$. Collect the indices for which $q_j$ is proportional to $u_y$, absorbing the nonzero proportionality factor into $p_j$, so that these maps have the form $p_ju_y^\top$. Denote this group by $J_y$. Zero maps can be discarded from the first-moment calculation.

For a fixed query $x$, the argument of $F$ from this group is

$$ (u_x\cdot p_j)(u_y\cdot w). $$

Every nonzero argument from a different right-direction group is a nonproportional linear form in $w$. Choose $w$ so that no such argument coincides with a nonzero argument from $J_y$, and so that $u_y\cdot w\neq0$. There are only finitely many forbidden proper hyperplanes. Also avoid coincidences with the target argument $u_x\cdot w$ when $x\neq y$.

Choose $F$ to equal its input on the finitely many nonzero arguments from $J_y$ and to vanish on all other arguments occurring in the identity, including zero. When $x=y$, the same prescription sets the target value to $u_y\cdot w$; if the target value had no matching argument, the identity would already be impossible. When $x\neq y$, its value is zero. Dividing the resulting identity by $u_y\cdot w$ proves

$$ \sum_{j\in J_y}L_j(x)(u_x\cdot p_j)=\begin{cases}1&x=y,\cr0&x\neq y.\end{cases} $$

The left side is a polynomial of degree at most $d+1$. A polynomial equal to a nonzero single-vertex indicator on the Boolean cube has degree at least $n$. The existing Boolean minimum-support theorem proves this fact, and `dimension_le_of_vertex_selector` records the exact consequence. Therefore $n\leq d+1$. $\blacksquare$

## Why individual fixed-set selectors are invalid

One cannot replace the grouped first moment by a claim that each individual residue is supported on the queries fixed by its map. Cancellation among different maps is permitted away from their fixed sets. In one bit, constant residues already give

$$ F(a+bx)=F(a)+F((a+b)x)-F(ax). $$

Thus the stronger proposed inequality $d\geq n-r+1$ for maps of rank $r$ would already fail at $n=r=1$ and $d=0$.

The degree threshold above is sharp. Gate on the first $n-1$ bits, using their exact vertex indicators of degree $n-1$, and apply this three-term identity to the remaining bit. This gives $3\cdot2^{n-1}$ rank-one terms with residues of degree $n-1$.

For two bits, the explicit identity is

$$ \begin{aligned} F(a+bx+cy)&=(1-y)\bigl(F(a)+F((a+b)x)-F(ax)\bigr)\cr&\quad+y\bigl(F(a+c)+F((a+c+b)x)-F((a+c)x)\bigr).\end{aligned} $$

It is kernel checked as `two_bit_six_term_identity`. The gates are affine. Multiplying these gates by an already affine numerator generally produces quadratic numerators, so this scalar identity is not automatically a compiler for arbitrary affine-numerator heads.

## A weaker covering bound for larger rank

For fixed maps of rank at most $r\geq1$, any universal scalar-kernel identity forces every query $u_x$ to be fixed by at least one map. Otherwise choose a generic $w$ with the target argument distinct from every compiled argument, and choose $F$ supported only at the target value.

The fixed space of a rank $r$ map has dimension at most $r$. Its intersection with the anchored cube has at most $2^{r-1}$ points: the first coordinate equals one, so this intersection lies in an affine flat of dimension at most $r-1$, and a coordinate projection injects any such Boolean flat into at most $r-1$ Boolean coordinates. Consequently a compiler with $J$ maps satisfies

$$ J\geq2^{n-r+1}. $$

This covering estimate is written, not formalized. It allows cancellations and arbitrary query-dependent residues, but still assumes one fixed list of linear maps works for every parameter vector. It does not bound an adaptive truth-table compiler.

## Verification and next gap

`RankOneCompilerSelector.lean` contains four kernel-checked declarations: the vertex-selector degree bound, the product-selector degree bound, its affine impossibility consequence, and the two-bit six-term identity. `RankOneSelectorAudit.lean` and `rank-one-selector-axioms.txt` record their transitive axioms; only `propext`, `Classical.choice`, and `Quot.sound` occur. The module build is recorded in `rank-one-selector-build.txt`.

The remaining useful access question is existential and global: can a finite Boolean-projection moment relation be replaced, modulo exact projection ghosts, by a comparably sparse ordinary moment relation using new parameter-dependent support? This note rules out one universal fixed-map construction of that replacement. It does not settle the existential question or the unrestricted capacity target.
