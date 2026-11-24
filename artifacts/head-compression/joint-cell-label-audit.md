# Label dependence and joint axis repair

## Scope and checked statements

This audit concerns `UniversalLogSaving.lean` and its affine-plane dependencies. It keeps the original model and `HeadComplexity.worstCaseHeadComplexity` unchanged. A local table is arbitrary; different tables may have independently chosen Boolean entries.

The existing compiler uses a field of size $q=2^a$, at most $a q^2$ rows, and an arbitrary number $s$ of columns. Its strict grid budget is $2q^2+1$, followed by the generic axis repair budget $6q^2+6$.

The new declaration `HeadComplexity.AxisZeroGluing.hasReverseAxisCompiler_affinePlane_joint` in `formalization/HeadComplexity/Results/JointCellRankRepair.lean` gives the complete axis-zero compiler with $3q^2+4$ heads. This is a constant improvement within one table. It does not provide an unbounded factor across tables.

`formalization/HeadComplexity/Results/JointCellLabelAudit.lean` checks token injectivity, the exact change in a line sum after a one-point token update, and the impossibility of decoding distinct tables from one identical memory using one identical decoder. These are restricted statements about the audited construction, not lower bounds for general joint compilation.

## Data that may be fixed before the labels

Fix a field $F$ of size $q$, a row embedding $i\mapsto(p_i,b_i)$ into $F^2\times\lbrace 0,\ldots,a-1\rbrace$, and a bijection from $F$ to the $a$-bit words. Fix the compact token map $t$ and poles $d_\alpha$ after choosing $\delta\gt 0$ with $(r+s)\delta\lt 1$.

$$ 0\lt t(z)\lt\delta,\qquad 1-\delta\lt d_\alpha\lt 1. $$

The scalar Cauchy decoders for each bit position can be fixed for all tables:

$$ c_b+\sum_{\alpha\in F}\frac{\eta_{b,\alpha}}{d_\alpha-t(z)}=\mathrm{sign}(\mathrm{decode}(z)_b). $$

Thus the row embedding, word alphabet, poles, token locations, residues, and row biases are independent of the labels. In the actual compiler the alphabet bijection is chosen before the table-dependent memory. None of these fixed choices identifies independently chosen words in different tables.

## Exact label dependence

For a table $\tau$, the memory $m^\tau_{g,j}\in F$ contains the labels in column $j$ at the rows assigned to point $g$. At full row capacity every point word can be chosen independently. At smaller row capacity the requested labels still determine the occupied bit positions, while the remaining positions are filled by the encoding construction.

For a nonvertical line $\ell=(\alpha,\beta)$ define its aggregate:

$$ Z^\tau_{\ell,j}=\sum_{g_2=\alpha g_1+\beta}\frac{1}{d_\alpha-t(m^\tau_{g,j})}. $$

The rank selector is fixed:

$$ f_\ell(i)=\begin{cases}\eta_{b_i,\alpha}&\beta=(p_i)_2-\alpha(p_i)_1,\cr 0&\text{otherwise}.\end{cases} $$

The incidence identity is exact:

$$ \sum_\ell f_\ell(i)Z^\tau_{\ell,j}=\sum_\alpha\frac{\eta_{b_i,\alpha}}{d_\alpha-t(m^\tau_{p_i,j})}+\sum_{g_1\neq(p_i)_1}\frac{\eta_{b_i,\alpha(i,g)}}{d_{\alpha(i,g)}-t(m^\tau_{g,j})},\qquad \alpha(i,g)=\frac{g_2-(p_i)_2}{g_1-(p_i)_1}. $$

The second sum is the interference. Its point correction has numerator and row pole

$$ A_g(i)=\begin{cases}-\eta_{b_i,\alpha(i,g)} & g_1\neq(p_i)_1,\cr 0&\text{otherwise},\end{cases}\qquad D_g(i)=d _{\alpha(i,g)}, $$

and column token $T^\tau_g(j)=t(m^\tau_{g,j})$. Both $A_g$ and $D_g$ are fixed. The denominator $D_g(i)-T^\tau_g(j)$ depends on the local labels.

| Part | Fixed before labels | Depends on the table |
| --- | --- | --- |
| Word decoder | Alphabet, bit residues, poles, row bias | Encoded words |
| Line rank factors | Row selectors and row denominator slopes | Every line aggregate and its column numerator |
| Shared affine rank correction | Denominator | The aggregate column vector |
| Point interference correction | Numerator and row slopes | Column denominator slopes |
| Point axis subtraction | All coefficients with the uniform choice below | None |
| Final row and column repair | Denominators and row vector | One aggregate column vector |
| Global descending assembly | Cover geometry | Numerator scales and suppression parameters may depend on all required signs |

Changing the token at one point $g$ and one column changes every incident line aggregate. Explicitly, for a line through $g$, the change is

$$ \frac{1}{d_\alpha-t(z')}-\frac{1}{d_\alpha-t(z)}\neq 0\qquad\text{when }z'\neq z. $$

This follows from injectivity of the token map and reciprocal map, and is formalized by `auditedAffinePlaneLineSum_update_ne`. The corresponding correction denominator also changes, as formalized by `auditedCauchyDenominator_ne`. A common finite plane therefore supplies a common indexing geometry, not common numerical line sums or common token denominators.

## One shared rank-axis cancellation

For arbitrary rank factors $f_h(i)g_h(j)$, choose positive shifts and scales depending only on the row factors:

$$ C_h=1+\sum_i\lvert f_h(i)\rvert,\qquad u_h(i)=C_h+f_h(i),\qquad M_h=4(r+1)C_h. $$

Then $0\lt u_h(i)\lt 2C_h$ and $u_h(i)/(M_h+u_h(i))\leq 1/(2(r+1))$. Choose one common $\varepsilon=1/(4(r+s+1))$ and put $B=1+2\varepsilon$. The head for factor $h$ has numerator $M_h\sum_jg_h(j)w_j$ and denominator

$$ B-\sum_i\left(\varepsilon+\frac{u_h(i)}{M_h+u_h(i)}\right)z_i-\varepsilon\sum_jw_j. $$

Every slope is strictly negative. The total slope cost is bounded by $(r+s)\varepsilon+r/(2(r+1))\lt 3/4$, so every denominator is positive on the entire Boolean cube.

At the grid point $(e_i,e_j)$ this head is $(M_h+C_h+f_h(i))g_h(j)$. On the left axis $z=0$, all these heads have the same denominator. They are jointly cancelled by one head with numerator $-\sum_hM_h\sum_jg_h(j)w_j$ and denominator $B-\varepsilon(\sum_i z_i+\sum_jw_j)$. Every numerator vanishes on the right axis $w=0$.

The resulting $L+1$ heads are exactly zero on both axes and have grid value

$$ \sum_h\bigl(C_h+f_h(i)\bigr)g_h(j). $$

The final three-head row and column repair supplies the requested row bias together with the column vector $-\sum_hC_hg_h(j)$. In particular, all table-dependent rank-axis corrections are absorbed in one column vector. They have not become label independent.

This construction is formalized as `exists_reverse_axis_rank_grid_joint`, with exact budget $L+4$.

## Point corrections and the complete local budget

For each compact Cauchy correction $A_g(i)/(D_g(i)-T_g(j))$, pair its head with the head having numerator $-A_g$ and constant column token $\delta/2$. The pair is exactly zero on both axes. The second head is independent of the labels. The pair's grid value is

$$ \frac{A_g(i)}{D_g(i)-T_g(j)}-\frac{A_g(i)}{D_g(i)-\delta/2}. $$

The omitted term is one row vector after summing over $g$, and can be included in the same final three-head repair used above. Both heads have strictly negative slopes and total slope cost below $(r+s)\delta\lt 1$, proving positivity throughout the Boolean cube.

With $L$ rank factors and $G$ point corrections the complete budget is $L+2G+4$, not a sum of separately repaired budgets. This is the declaration `exists_reverse_axis_rank_cauchy_grid_joint`.

For the affine plane, $L=G=q^2$. Incidence cancellation removes the interference exactly, the Cauchy decoder returns the Boolean sign exactly, and the resulting axis-zero module has $3q^2+4$ heads. Thus all grid signs are strict. The original descending-center transfer can be applied unchanged, charging every cell and both exceptional faces.

## What this does and does not share across cells

Concatenating $k$ arbitrary tables as $ks$ columns in an enlarged one-hot grid would use the same local compiler budget, but that grid requires $r+ks$ Boolean coordinates. The original model supplies only the original coordinates. A proposed sharing must explicitly realize those virtual columns and their arbitrary token assignments in that fixed cube.

Merely summing line aggregates over tables loses the table identifier before decoding. The point denominator then contains one token value, whereas independently chosen tables may require different words at the same point and column. The checked theorem `audited_shared_memory_table_eq` states the precise failure for one identical memory and decoder. This does not rule out a selector that changes the effective memory by a further admissible construction, but that construction and all of its heads must be charged.

Likewise, after the descending-center map, individual cell penalties usually change denominators. Common denominators within a local table do not imply common denominators after different localization penalties. Combining numerators without proving that the denominators agree is invalid. Dropping penalties also requires a new proof that prior signs survive all interference.

The current improvement merges axis-subtraction heads inside each table. It leaves $q^2$ arbitrary line-data heads and $q^2$ arbitrary token-denominator heads per table. Its ratio to separate compilation is bounded by a constant. An unbounded global gain still needs a way to encode and select independently chosen local words jointly, or a larger local domain with a fully charged cover and decoder.

## Validation

`lake build HeadComplexity.Results.JointCellLabelAudit HeadComplexity.Results.JointCellRankRepair` completed successfully with 9123 jobs. Transitive `#print axioms` for `hasReverseAxisCompiler_affinePlane_joint`, `exists_reverse_axis_rank_grid_joint`, and `exists_reverse_axis_rank_cauchy_grid_joint` returns only `propext`, `Classical.choice`, and `Quot.sound`. The line-update witness has the same list, and `audited_shared_memory_table_eq` uses only `Quot.sound`.

The static and KaTeX checker reports 70 source math spans and no findings. A real GitHub Markdown API render reports 70 rendered spans and no findings. The API was invoked directly because the machine has no `gh` executable. GitLab rendering was not attempted because `glab` is unavailable.
