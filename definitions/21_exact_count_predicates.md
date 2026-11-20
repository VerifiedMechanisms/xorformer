# Definition 1.21. Exact-count predicates

Let $n,k$ be integers with $n\geq1$ and $0\leq k\leq n$. Using [Hamming weight (Definition 1.17)](17_symmetric_functions.md) $|x|$, the **exact-count predicate** $\mathrm{EXACT}_{n,k}:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ is

$$ \mathrm{EXACT}_{n,k}(x)=\begin{cases} 1 & |x|=k, \cr 0 & |x|\neq k. \end{cases} $$

The counts $k=0,n$ are the **endpoint counts**. The counts $1\leq k\leq n-1$ are the **internal counts**; there are none when $n=1$.
