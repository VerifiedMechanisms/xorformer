# Definition 1.18. Symmetric thresholds

Let $n,t$ be integers with $n\geq1$ and $1\leq t\leq n$. Using [Hamming weight (Definition 1.16)](16_symmetric_functions.md) $|x|$, the **symmetric threshold** $T_{n,t}:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ is

$$ T_{n,t}(x)=\begin{cases} 1 & |x|\geq t, \cr 0 & |x|\lt t. \end{cases} $$

The standard threshold families are

$$ \mathrm{OR}_n=T _{n,1}, \qquad \mathrm{AND}_n=T _{n,n}, \qquad \mathrm{MAJORITY}_n=T _{n,\lceil n/2\rceil}. $$

Here majority outputs one on a tie when $n$ is even.
