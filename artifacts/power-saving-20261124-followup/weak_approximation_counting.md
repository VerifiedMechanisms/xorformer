# A small agreement advantage suffices for comparison counting

## Finite theorem

Let $N=2^n$, and fix a finite comparison class $G$ of Boolean truth tables. Suppose

$$ |G|\leq\exp(L),\qquad \varepsilon\geq0,\qquad L\lt2\varepsilon^2N. $$

If every truth table computed by $H$ original heads agrees with some member of $G$ on at least $(1/2+\varepsilon)N$ inputs, then $H\lt W(n)$.

The class $G$ is fixed before choosing the original truth table. The approximating member may depend on the whole table. Every original representation, including arbitrary signed cancellation and target-dependent denominators, remains in scope. The theorem does not assert that such approximations exist.

The declaration is `HeadComplexity.WeakApproximationCounting.worstCase_gt_of_weak_approximation`, in `formalization/HeadComplexity/Research/WeakApproximationCounting.lean`.

## Hamming-ball estimate

Fix a table $g$ and let $d(f,g)$ denote Hamming distance. Write $Z(f,g)=N-2d(f,g)$. Independence of the choices of $f$ at the $N$ inputs gives

$$ \sum_f\exp(tZ(f,g))=(\exp(t)+\exp(-t))^N\leq2^N\exp(Nt^2/2). $$

The last step uses $\cosh(t)\leq\exp(t^2/2)$. If $d(f,g)\leq(1/2-\varepsilon)N$ and $t\geq0$, its summand is at least $\exp(2\varepsilon tN)$. Choosing $t=2\varepsilon$ proves

$$ |B(g,(1/2-\varepsilon)N)|\leq2^N\exp(-2\varepsilon^2N). $$

No integrality assumption on the displayed radius is needed; the ball is defined by the corresponding real inequality for its integer distance. A union over $G$ contains at most

$$ 2^N\exp(L-2\varepsilon^2N)\lt2^N $$

tables. Under the approximation premise, that union contains every original width $H$ table. A missing table proves the stated bound against the original `worstCaseHeadComplexity`.

The finite inequalities are checked as `card_agreementBall_le`, `card_nearbyTables_le`, and `card_nearbyTables_lt`.

## Direct use of the margin-sensitive formula

Choose $\gamma\gt0$ and an integer $d\geq0$ with

$$ \exp(-(d+1)/(n+1))\leq\gamma/2,\qquad p=1+3(n+1)K\leq N. $$

The previously checked finite count supplies the exponent

$$ L=K\big(\log2+(n+1)\log(n+1)\big)+p\log\left(\frac{4e(2d+2)N}{p}\right). $$

The declaration `worstCase_gt_of_weak_margin_repair` combines this formula with the condition $L\lt2\varepsilon^2N$. Its predicate `HasWeakMarginRepair` requires each original width $H$ truth table to have an approximating table with a genuine width $K$ representation and full-cube relative margin at least $\gamma$. Thus all admissibility and margin hypotheses remain explicit.

## Prospective asymptotic budget

Suppose a future construction provides $K=O(n^aH)$, agreement advantage $\varepsilon\geq c_0n^{-b}$, and margin $\gamma\geq\exp(-n^q)$ for fixed constants $a,b,q\geq0$ and $c_0\gt0$. At $H=O(N/n^{2-\delta})$, the finite formula has

$$ L=O\left(Nn^{a+\delta-1}\log n\right),\qquad 2\varepsilon^2N\geq2c_0^2Nn^{-2b}. $$

Therefore the strict budget holds eventually if

$$ a+2b+\delta\lt1. $$

For the aimed $\delta=1/2$, constant width overhead and any advantage $n^{-b}$ with $b\lt1/4$ would suffice at polynomial-exponent margin. This asymptotic substitution is a written consequence of the finite formula. No such unrestricted approximation construction is established here. A target-independent universal approximation argument with the same budget would be impossible by the proved counting inequality itself.

## Verification

The module build passed with 4029 jobs. All seven declarations in `WeakApproximationAudit.lean` depend transitively only on `propext`, `Classical.choice`, and `Quot.sound`. The finite counting theorem is unconditional. The original-model lower bounds retain their explicit approximation hypotheses. No original model definition is changed.
