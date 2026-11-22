# Pseudoproduct Synthesis and the Head Model

## The construction in the literature

[Selezneva's construction, as reproduced with a proof in Sergeev, Theorem 13.3, pages 152 to 155](https://igorssergeev.github.io/papers/S-book_eng_280525.pdf), expresses every Boolean function as the XOR of $O(2^n/n^2)$ pseudoproducts. A pseudoproduct is a product of affine Boolean functions, with the affine operations taken over the field with two elements. It is the indicator of an affine subspace, or is identically zero.

The construction covers coefficient indices in the Boolean polynomial by products of positive and negative radius-one hemispheres, then eliminates the covered coefficients in a prescribed order. The covering step uses [Cooper, Ellis, and Kahng's asymmetric covering-code construction](https://people.math.sc.edu/cooper/codes.pdf). These are coefficient-space operations over a finite field. The output operation is XOR.

The cited original is S. N. Selezneva, *Order of the length of Boolean functions in the class of exclusive-OR sums of pseudoproducts*, Moscow University Computational Mathematics and Cybernetics 40(3), 123 to 127 (2016). The proof inspected here is the full reproduction in Sergeev's book, downloaded from the author's public repository. No uninspected original proof is being claimed as audited.

## An exact obstruction to a constant-cost transfer

**Theorem.** There is no absolute constant $C$ such that every pseudoproduct on every Boolean cube has attention-head complexity at most $C$ in the manuscript's model.

**Proof.** For each positive integer $n$, the affine Boolean function

$$ p_n(x)=x_1\oplus\cdots\oplus x_n $$

is itself a pseudoproduct with one factor. The manuscript's parity lower bound gives $H^{\ast}(p_n)\geq n$. To see the relevant mechanism directly, clearing the positive denominators of an $H$-head score produces a polynomial of input degree at most $H$. A strict polynomial sign representation of parity has degree at least $n$: if its degree were less than $n$, its product with the parity character would have zero uniform average by character orthogonality, whereas strict sign agreement would make that average strictly positive, up to a fixed global sign. Thus $H\geq n$. Choosing $n\gt C$ proves the claim. $\blacksquare$

Consequently, the number of pseudoproducts cannot be substituted for the number of heads. XOR of their outputs also differs from a threshold of a real sum. The synthesis theorem therefore supplies neither the requested lower bound nor a conflicting upper bound for the unchanged head model.

## Status

This literature route is blocked at the required translation between models. The obstruction above rules out a constant number of heads for each individual pseudoproduct. A different global translation would need a substantive proof; none is asserted here. The asymptotic refutation remains unproved.
