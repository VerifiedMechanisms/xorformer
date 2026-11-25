# Partial-label grid compilation and quantitative exceptional-set repair

## A positive partial-label theorem

Fix $\eta\in(0,1)$. For all sufficiently large $n$, let $E\subseteq\lbrace0,1\rbrace^n$ have cardinality $M$ and let arbitrary labels be prescribed on $E$. There is an original admissible score $T$ with signed gap at least one on $E$, full-cube amplitude at most $\exp(C_\eta n^2\log(n+1))$, and width at most

$$ C_\eta\left(\frac{2^n\log^4(n+1)}{n^2}+\sqrt{2^nM}n^{-1+\eta/2}\log^2(n+1)\right). $$

The first term is not claimed optimal, especially for very small $M$. Values outside $E$ are arbitrary. This is a written construction from the inspected remote affine-plane decoder and rank gluing; the entire theorem is not kernel checked. The quantitative patching implication below is kernel checked separately.

The distinction from a sparse value compiler is essential: unspecified grid entries may receive arbitrary labels. This permits a small covering alphabet and avoids the exact-zero layer-gating obstruction.

## Completing a partial grid from a small alphabet

Consider an $r$ by $s$ partial sign matrix, with $s\leq r$, containing $m$ prescribed entries. For every fixed $\eta\gt0$, it has a complete ternary extension represented by an exact strict reverse-grid module, zero on both axes, using

$$ O_\eta\left(\log^2(r+1)+\sqrt mr^{\eta/2}\right) $$

original heads. Its full-cube amplitude is at most exponential in a polynomial of $r+s$. Swapping the two coordinate blocks permits the convention $s\leq r$.

Choose a power of two $q$ whose square is within a fixed factor of

$$ \max\left(C_\eta\log^2(r+1),\sqrt{m r^\eta}\right). $$

If this quantity exceeds $r$, use blocks of one row and $q^2=O(r)$ instead. An alphabet of three words then gives an arbitrary complete matrix with $O(r)$ heads, which satisfies the asserted bound. We may therefore assume $q^2\leq r$ and partition the rows into at most $q^2$ blocks of size $a=\lceil r/q^2\rceil$.

Remove columns with more than $T=q^2r^{-\eta}$ prescribed entries. There are at most $m/T$ such columns. Each costs at most nine heads by the two-head column identity and exact axis repair in `sparse_grid_compilation_and_outside_gap.md`.

Choose one common random permutation of the rows and use its block partition for every remaining column. A fixed block-column occupancy satisfies, for a fixed positive integer $k$,

$$ \Pr[\text{occupancy}\geq k]\leq\binom ak\left(\frac{2T}{r}\right)^k=O_k(r^{-\eta k}). $$

There are at most $r^2$ block-column pairs. Choose a fixed integer $k=k_\eta$ with $\eta k\gt3$. A suitable partition then has fewer than $k$ prescribed positions in every such pair. If $T\lt1$, all nonempty columns were removed and this step is vacuous.

There is a family of $O_k(\log(a+1))$ binary words of length $a$ that realizes every prescribed assignment on at most $k$ coordinates. To see this, choose independent uniform words: a particular assignment on at most $k$ positions is matched by each word with probability at least $2^{-k}$, and there are at most $\sum_{j=0}^k\binom aj2^j\leq(k+1)(2a)^k$ assignments. A union bound gives the claimed family size. Increase $C_\eta$ so that this family, together with the zero word, has at most $q$ elements.

For every block-column choose a word matching all its prescribed entries. On removed columns choose the zero word. Thus every block has its own alphabet of at most $q$ words. The arbitrary-alphabet interface of `Results/AffinePlaneCompiler.lean` gives $2q^2+1$ strict grid heads before axis repair and at most $6q^2+6$ afterward. Add the removed-column modules. The total is

$$ O_\eta\left(q^2+\frac{m r^\eta}{q^2}\right)=O_\eta\left(\log^2(r+1)+\sqrt mr^{\eta/2}\right). $$

Unprescribed entries in removed columns may be zero; other unprescribed entries are completed signs. All prescribed entries retain their exact sign and a unit gap after a common fixed rescaling. The quantitative Cauchy and axis-repair estimates in `universal_log_width_quantitative_margin.md` apply without change because the completed values belong to $\lbrace-1,0,1\rbrace$.

## A sparse product cover with controlled total incidence

Split the coordinates into blocks of sizes $a=\lfloor n/2\rfloor$ and $b=n-a$. Exclude vertices for which either block has more than three quarters of its coordinates equal to one. The number excluded is at most

$$ 2\cdot2^n\theta^{\lfloor n/2\rfloor},\qquad \theta=2/3^{3/4}\lt1. $$

This follows from the exponential-moment bound with parameter three for a fair binomial random variable. Each remaining vertex has at least $a/4$ and $b/4$ open upward parents in the two blocks, hence at least $n/12$ in each block for large $n$.

Select each possible block center independently with probability $p=240\log(n+1)/n$, independently between the two blocks. Their Cartesian product is the product-star module family. Let $J$ be the number of modules and let $m_j$ count prescribed vertices of $E$ on module $j$'s product grid. Write $R$ for the number of nonexcluded prescribed vertices not covered. Then

$$ \mathbb E J=2^n p^2,\qquad \mathbb E\sum_jm_j\leq M n^2p^2,\qquad \mathbb E R\leq2M(n+1)^{-20}. $$

The incidence estimate counts every prescribed vertex on every selected grid that contains it. This is deliberate: assigning a vertex to only one module would leave the other same-rank modules free to give a wrong sign there.

A union bound on three Markov inequalities yields a selection satisfying simultaneously

$$ J\leq6\cdot2^np^2,\qquad \sum_jm_j\leq6Mn^2p^2,\qquad R\leq12M(n+1)^{-20}. $$

If an expectation is zero, its random variable is identically zero and that condition requires no Markov argument. Empty modules can be discarded. Apply the partial-grid compiler to every remaining module, requiring the correct sign at all of its prescribed grid incidences. Cauchy-Schwarz gives

$$ \sum_j\sqrt{m_j}\leq\sqrt{J\sum_jm_j}=O\left(\sqrt{2^nM}\frac{\log^2(n+1)}n\right). $$

The total module width is therefore bounded by the displayed theorem budget.

## Whole-cube realization and norm control

Localize each grid module to its center downset using the genuine coherent-denominator construction from `universal_log_width_quantitative_margin.md`. Its local norm and numerator bounds can all be absorbed into $B=\exp(C_\eta n\log(n+1))$. The number of centers is at most $2^n$ after discarding repetitions. Use the rank weights and outside penalty from that note, with a common ratio at least $8\cdot2^nB$ and penalty at least $8\cdot2^nB$ times the largest rank weight.

At a covered prescribed vertex, there is a designated module whose grid contains it and whose rank is exactly two larger than its Hamming weight. Every other module of that same rank is correct there or vanishes on an axis. Every lower-rank module whose downset contains it vanishes on an axis. Higher-rank terms form a geometric tail, and all outside-downset leakage has a uniformly small total. Hence a fixed rescaling gives signed gap at least one on every covered prescribed vertex.

This argument needs no sign claim at vertices outside $E$. The total full-cube amplitude is at most $\exp(C_\eta n^2\log(n+1))$, by the same rank-batching calculation already audited in the quantitative universal compiler note.

There remain at most

$$ 12M(n+1)^{-20}+2\cdot2^n\theta^{\lfloor n/2\rfloor} $$

prescribed vertices. Correct their values individually by mixed-vertex indicator approximations. `LinearCylinderMargin.lean` supplies at most $n+1$ heads per indicator with bounded total amplitude $\exp(O(n\log(n+1)))$, uniformly to any required accuracy. Use the exact desired correction coefficient at each remaining vertex, of magnitude at most one plus the current whole-cube norm. Choose the individual approximation errors so their total full-cube error is at most $1/4$, then rescale once. This preserves all previously established gaps, corrects the remaining vertices, and retains the stated exponential norm bound. The additional width is absorbed by the first theorem term for all sufficiently large $n$.

## Quantitative exceptional-set patching in the original model

Let $S$ strictly represent the full truth table, have actual amplitude $D$, and satisfy $f(x)S(x)\geq\tau D$ outside $E$, where $0\lt\tau\leq1$. Suppose $T$ has unit signed gap on $E$ and full-cube amplitude at most $B\geq1$. Set

$$ \epsilon=\frac{\tau D}{2B}. $$

The genuine concatenated score $S+\epsilon T$ has signed gap at least $\epsilon$ everywhere. On $E$ this follows from the original strict score and the unit patch gap. Outside $E$, the signed score is at least $\tau D-\epsilon B=\tau D/2\geq\epsilon$. Its amplitude is at most $D+\epsilon B\leq3D/2$. Thus its full-cube relative margin is at least

$$ \frac{\tau}{3B}. $$

This implication is `HeadComplexity.ExceptionalMarginRepair.relativeMargin_ge_of_exceptional_patch` in `Research/ExceptionalMarginRepair.lean`. It permits arbitrary signed cancellation and uncontrolled patch signs outside $E$; only the full-cube amplitude bound is used.

## Remaining access gap

If a width $H=c2^n/n^{3/2}$ representation had relative signed gap at least $\exp(-\mathrm{poly}(n))$ outside at most $O(nH)$ vertices, the partial compiler would cost

$$ O_\eta\left(2^n n^{-5/4+\eta/2}\log^2(n+1)+2^n n^{-2}\log^4(n+1)\right) $$

heads and yield a full-cube margin $\exp(-\mathrm{poly}(n))$. For $\eta\lt1/2$, this comparison width has sublinear truth-table entropy in the audited margin-sensitive count. Such an access theorem would therefore suffice for the benchmark lower bound, even though the comparison width can exceed the original width by a small power of $n$.

No such almost-everywhere quantitative margin theorem has been proved. That premise would already suffice through approximate polynomial counting without patching; the construction here additionally supplies an original-head representation of the entire table with controlled relative margin, rather than weakening the missing premise. The fact that a fixed-denominator linear program has at most $O(nH)$ exactly active constraints does not bound the number of vertices with merely tiny slack. The abstract recycling counterexample in `active_margin_improvement_and_recycling_gap.md` shows why repeated local improvement is also insufficient by itself. The present result proves a patching construction under an explicit quantitative exception-set hypothesis, not that every narrow truth table admits that hypothesis.

There is also a concrete original-head obstruction to extracting this premise merely by optimizing coefficients with denominators fixed. For $n\geq3$, take majority on the first three bits and fix

$$ B_\epsilon(x)=\epsilon\left(1+\frac1n\sum_{i=4}^n x_i\right)+x_1+x_2+x_3,\qquad \epsilon\gt0. $$

Every numerator refit, arbitrary bias, and any number of repeated copies of this denominator combine into an affine ratio $A/B_\epsilon$. If it strictly has the majority labels and its original amplitude is $D$, then $|A/B_\epsilon|\leq D$ everywhere. Fix the remaining coordinates and write $A(000)=-u$. The three singleton values are $-v_i\lt0$. Positivity on each pair gives $v_i+v_j\lt u$, so $0\lt v_i\lt u$. The triple value is $2u-v_1-v_2-v_3\gt0$. Hence every nonzero first-three-bit pattern has numerator magnitude at most $2u$. At the zero pattern, $u\leq2\epsilon D$. Everywhere else $B_\epsilon\geq1$, proving

$$ 0\lt\frac{f(x)S(x)}D\leq4\epsilon $$

on the designated $7/8$ of the cube with at least one of the first three bits equal to one. This quantifies over every fixed-denominator representation, including its optimal coefficient refit. A different genuine positive affine denominator gives a one-head repair: take $A(x)=2(x_1+x_2+x_3)-3$ and $B(x)=1+(100n)^{-1}\sum_{i=1}^n x_i$. All denominator slopes are strictly positive, so the original positive-affine-ratio constructor applies. Since $1\leq|A(x)|\leq3$ and $1\leq B(x)\leq101/100$, the repaired relative margin is at least $100/303\gt1/4$. A constant denominator with zero numerator slopes on unused coordinates would not itself satisfy the original one-head constructor for $n\gt3$. Thus the example blocks the frozen-denominator access argument, while leaving the required unrestricted choice of denominators fully open.

## Verification status

An independent agent audited the local covering-array completion, common row partition, random product-cover expectations, simultaneous Markov bounds, total-incidence count, rank gluing, residual vertex corrections, and amplitude budget. The written proof passed. The source decoder and quantitative local bounds are the inspected remote construction identified in `universal_log_width_quantitative_margin.md`; this note does not claim a local rebuild of that remote universal theorem.

`lake build HeadComplexity.Research.ExceptionalMarginRepair` completed successfully with 3285 jobs. Both declarations in `AuditExceptionalMarginRepair.lean` have exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Original definitions and admissibility conditions are unchanged.
