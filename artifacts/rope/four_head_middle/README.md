# Four-head projected coefficient feasibility

These exact rational data certify a coefficient calculation, **not a Boolean head-count separation**. The verifier checks all identities and inequalities with SymPy rationals. It does not claim that either score satisfies the local Boolean labels needed for a lower bound.

For four centered pure atoms, write the score as follows, with the first input coordinate denoted by $t$.

$$ F(z)=T+\sum_{h=0}^{3}\frac{u_h\cdot z}{1+\beta_h\cdot z},\qquad u_h=k_hs_h+\ell_h\beta_h,\qquad s_{hi}\gt|\beta_{hi}|,\qquad\sum_i s_{hi}\lt1. $$

Clear the four positive denominators. Its component odd in $t$ and even under simultaneous negation of all sixteen remaining coordinates is $t$ times a quadratic. Let $b_h$ and $a_h$ be the coefficients of $t$ in the denominator and centered numerator. The mixed coefficient matrix between two blocks of eight spatial coordinates factors as follows.

$$ C=XHY^\top,\qquad X=(S_X\quad B_X),\qquad Y=(S_Y\quad B_Y),\qquad H=\begin{pmatrix}0&KA\cr AK&L\end{pmatrix},\qquad K=\mathrm{diag}(k). $$

The middle matrices have zero diagonal, and their off-diagonal entries are

$$ A_{ij}=\sum_{h\neq i,j}b_h,\qquad L_{ij}=\sum_{h\neq i,j}a_h+(T+\ell_i+\ell_j)A_{ij}. $$

`seed.json` gives a strict pure parameter point for which this cross matrix is a positive scalar multiple of the identity minus a small positive multiple of the all-ones matrix. `seed_zero_t_linear.json` additionally has exactly zero sum of the numerator coefficients of $t$. The latter permits a larger common normalization and therefore has more substantial denominator variation.

Run `python3 artifacts/rope/four_head_middle/verify_seed.py` from the repository root to regenerate and verify both files. Matrix rows in `S`, `B`, and `U` correspond to input coordinates, and columns correspond to heads. Coordinate zero is $t$, coordinates one through eight form the first spatial block, and coordinates nine through sixteen form the second block.

The full local matching pattern cannot be obtained from these middle forms. Its required negative off-diagonal entries in the second-block Gram matrix are incompatible with the cross matrix condition and the shared positive mass columns. The generic theorem `HeadComplexity.PositiveGramObstruction.gram_obstruction_of_column_sums` in [PositiveGramObstruction.lean](../../../formalization/HeadComplexity/Polynomial/PositiveGramObstruction.lean) proves this obstruction for arbitrary real matrices. Thus the data demonstrate why the mixed coefficient matrix alone is insufficient to certify a Boolean separation.
