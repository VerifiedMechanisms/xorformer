# Denominator Orders Do Not Determine Feasible Labels

## Statement

Two pairs of strictly coefficient-positive affine denominators on four bits have the same strict ordering of the cube vertices in each head, but different feasible Boolean sign patterns. Thus replacing each denominator by its order on the cube loses classification information. This is an obstruction to a proposed counting mechanism, not a worst-case head lower bound.

Put

$$ A(x)=1+16x_1+38x_2+36x_3+4x_4,\qquad B_-(x)=5+190x_1+160x_2+70x_3+14x_4,\qquad B_+(x)=1+38x_1+32x_2+14x_3+3x_4. $$

Consider scores with arbitrary real coefficients

$$ S_\pm(x)=c+\frac{\sum_{i=1}^4u_i x_i}{A(x)}+\frac{\sum_{i=1}^4v_i x_i}{B_\pm(x)}. $$

These are precisely the spaces obtained by allowing arbitrary affine numerators with the displayed fixed denominators and a free bias. To see this, for $D=d_0+\sum_i d_i x_i$ with $d_0\neq0$, rewrite an affine numerator $a_0+\sum_i a_i x_i$ as $(a_0/d_0)D+\sum_i(a_i-a_0d_i/d_0)x_i$.

## Identical denominator orders

List vertices lexicographically from $0000$ to $1111$. The value tables are

$$ A=(1,5,37,41,39,43,75,79,17,21,53,57,55,59,91,95), $$

$$ B_-=(5,19,75,89,165,179,235,249,195,209,265,279,355,369,425,439), $$

$$ B_+=(1,4,15,18,33,36,47,50,39,42,53,56,71,74,85,88). $$

Each table has distinct entries. The increasing vertex-index order for both $B_-$ and $B_+$ is

$$ (0,1,2,3,4,5,8,9,6,7,10,11,12,13,14,15). $$

The first denominator is unchanged. Hence both heads retain their strict orders.

## Exact infeasibility certificate

For a vertex $x$, define the cleared evaluation row

$$ R_\pm(x)=\big(AB_\pm,x_1B_\pm,x_2B_\pm,x_3B_\pm,x_4B_\pm,x_1A,x_2A,x_3A,x_4A\big). $$

Use the following ten vertices and integer weights. The last column will certify the feasible score for $B_+$.

| Vertex | Weight | Right cleared score |
|---|---:|---:|
| 0000 | 15280061511 | 25 |
| 0001 | 18335091357 | 26 |
| 0011 | -699843495 | -20 |
| 0100 | -1295248396 | -33 |
| 0101 | -1388636097 | -170 |
| 0110 | 421929807 | 7 |
| 1000 | 192383607 | 32 |
| 1011 | -1435996937 | -19 |
| 1111 | 827171622 | 11 |
| 0010 | 8631597 | 5461 |

Write the weights as $w_j$ and the vertices as $x^{(j)}$. Direct integer arithmetic gives the nine simultaneous identities

$$ \sum_{j=1}^{10}w_j R_-(x^{(j)})=(0,0,0,0,0,0,0,0,0). $$

Every cleared left score $P_-(x)=A(x)B_-(x)S_-(x)$ therefore satisfies

$$ \sum_{j=1}^{10}w_jP_-(x^{(j)})=0. $$

It cannot have the strict sign of $w_j$ at all ten vertices, since every summand would then be positive. Because both denominators are positive, the same impossibility holds for $S_-$. Allowing zero scores on false labels does not evade it: all weighted terms would be nonnegative and the true label at $0000$ makes one term strictly positive.

## Exact feasible score

Take

$$ (c,u_1,u_2,u_3,u_4,v_1,v_2,v_3,v_4)=(25,-558,-976,-1518,214,307,0,388,-266). $$

For $B_+$ the cleared score has precisely the values in the table's last column, with the desired signs. Its full cube table is

$$ P_+=(25,26,5461,-20,-33,-170,7,-5612,32,8463,-2968,-19,5596,13889,-2800,11). $$

All entries are nonzero. Thus this gives a total Boolean function realized by two exact-model heads with denominators $A,B_+$, but by no score using the fixed denominators $A,B_-$. The impossibility covers arbitrary affine numerators for that fixed pair. It does not forbid other denominator pairs or imply any lower bound above two for this function.

## Audit

`verify_denominator_order.py` independently regenerates the rows from the affine forms, verifies all 256 pairwise order comparisons, checks the nine annihilator identities, and checks the score formula on every vertex using exact rational arithmetic. The data are in `denominator-order-certificate.json`.

`formalization/HeadComplexity/Atoms/DenominatorOrder.lean` checks the finite arithmetic with kernel reduction. Its declarations `HeadComplexity.DenominatorOrder.left_infeasible` and `right_feasible` prove the two opposing feasibility statements for the cleared numerator matrices over all real coefficient vectors. `matrices_are_evaluations`, `full_tables_are_evaluations`, and `strict_identical_orders` connect the matrices and denominator tables to the displayed formulas. `exampleFunction_computable` additionally realizes the right score with two exact-model heads. The algebraic normalization of arbitrary affine numerators and the non-strict false-label argument are the written proofs above. All audited declarations use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
