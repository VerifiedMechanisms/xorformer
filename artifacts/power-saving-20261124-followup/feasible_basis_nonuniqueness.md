# Actual unit bases do not determine the Boolean table

## Statement and scope

Even for one genuine original head, a full basis of actual cube rows at prescribed values in $\lbrace-1,+1\rbrace$ does not determine the remaining labels. This remains false when both certificates satisfy $|S(x)|\geq1$ on the entire cube, lie in one fixed coefficient box, have strictly positive denominator slopes, and have the same raw numerator coefficient signs.

The counterexample rules out uniqueness of the truth-table extension of a feasible active basis. It does not rule out a weaker upper bound on the number of extensions. It does not exhibit a truth table with small margin in every representation. The examples themselves have bounded integer coefficients and good margin.

The exact statements are kernel-checked in `formalization/HeadComplexity/Research/OneHeadFeasibleBasisNonuniqueness.lean`, namespace `HeadComplexity.OneHeadFeasibleBasisNonuniqueness`. The accompanying two-head example is in `Research/FeasibleBasisNonuniqueness.lean`. The original `FracAtom`, `fracComputable`, and worst-case definitions are unchanged.

## One head in dimension six

Use coordinates $x_1,\ldots,x_6\in\lbrace0,1\rbrace$. Define

$$ \begin{aligned} B_0(x)&=1+x_1+2x_2+x_3+x_4+x_5+x_6,\cr A_0(x)&=11-9x_1-18x_2-9x_3-9x_4-9x_5+11x_6,\cr B_1(x)&=1+x_1+4x_2+x_3+x_4+x_5+x_6,\cr A_1(x)&=15-13x_1-28x_2-13x_3-17x_4-13x_5+19x_6. \end{aligned} $$

Both denominators have positive constant and strictly positive slopes, so both ratios $S_k=A_k/B_k$ are admissible original one-head scores. In the normalized bias-plus-zero-constant-numerator coordinates, their coefficient vectors are

$$ c_0=(11,-20,-40,-20,-20,-20,0),\qquad c_1=(15,-28,-88,-28,-32,-28,4). $$

Thus $|c_{k,i}|\leq88$ for both certificates. The common ordered basis consists of the following actual cube points:

$$ (000111,001000,001101,010001,010011,100000,101011). $$

Both scores take the ordered values

$$ (1,1,1,1,-1,1,-1) $$

on this basis. The seven rows of the normalized feature map $(1,x_1/B_k(x),\ldots,x_6/B_k(x))$ are linearly independent for each denominator. Exact inverse certificates prove this in Lean; no numerical rank test is used in the formal proof.

On all $64$ cube vertices, both scores satisfy $|S_k(x)|\geq1$. At the fourth-coordinate singleton $v=(0,0,0,1,0,0)$, however,

$$ S_0(v)=1,\qquad S_1(v)=-1. $$

Their raw numerator slope signs are identical, namely $(-,-,-,-,-,+)$. Consequently fixing this sign chamber in addition to the active basis still does not determine the label extension. The independent exact rational checker verifies that $v$ is the only vertex where the two tables disagree.

The decisive failed inequality for deformation to the constant denominator is also explicit. The unique affine interpolant to the common unit data is

$$ L(x)=3-2x_1-4x_2-2x_3-2x_4-2x_5+2x_6. $$

For $f=\mathrm{sign}(S_1)$, the required full-cube unit inequality at $v$ would be $f(v)L(v)\geq1$, whereas its left side equals $-1$. Full feasibility at a positive affine denominator therefore does not imply feasibility at the constant-denominator interpolation endpoint.

## Two heads in dimension three

A second, smaller cube example shows the same obstruction for seven normalized coefficients. Let

$$ \begin{aligned} T_0(x,y,z)&=3+\frac{4x+(4/3)y-12z}{1+x+y+2z}+\frac{-12x-(32/3)y+4z}{1+2x+3y+z},\cr T_1(x,y,z)&=-3+\frac{-6x-6y-24z}{1+x+y+z}+\frac{28x+28y+32z}{1+3x+3y+z}. \end{aligned} $$

Every denominator has strictly positive slopes, so every summand is an admissible original head. On the seven nonzero cube vertices in lexicographic order both scores equal

$$ (1,1,-1,1,-1,1,-1). $$

Their normalized basis determinants are $1/806400$ and $1/1209600$, respectively. On the entire cube both have absolute score at least one, and all normalized coefficients have magnitude at most $32$. At the origin their scores are $3$ and $-3$.

## Feasible branches persist for the two-head example

For the two-head example, the seven selected rows are all cube vertices except the origin. Each basis matrix is invertible, and every denominator slope is strictly positive. Hence under sufficiently small arbitrary perturbations of its six denominator slopes, the basis interpolation coefficients vary continuously and all denominators stay admissible. The only unselected score starts at $3$ or $-3$, so its absolute value remains greater than one and its sign persists. Enlarging the coefficient box from $32$ to $33$ keeps both neighborhoods inside one box.

Thus two distinct feasible truth-table branches occur on open sets of denominator parameters for the same actual unit basis. This continuity argument is a written consequence of the kernel-checked exact data. A uniqueness assertion restricted to generic feasible branches already fails for two heads.

## Verification record

The principal Lean declarations in each namespace are `original_score`, `basis_values`, `full_cube_unit_slack`, `coefficient_box`, `basis_injective`, and `original_computable`. The one-head namespace also proves `score_ratio`, `singleton_disagreement`, and `numerator_slope_signs`. The two-head namespace proves `origin_disagreement`.

`check_feasible_basis_examples.py` independently checks all vertices, exact rational determinants, coefficient boxes, and the constant-denominator interpolant. Its output is `feasible-basis-exact-certificates.json`. The finite computation is corroboration; the listed Lean declarations are kernel proofs using explicit rational arithmetic and linear-combination certificates.

The build log and transitive axiom output are `feasible-basis-nonuniqueness-build.txt` and `feasible-basis-nonuniqueness-axioms.txt`. Every audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

A capacity proof using feasible active bases must bound their additional branches. Counting one branch per basis, or one branch per numerator-sign chamber, is not valid.
