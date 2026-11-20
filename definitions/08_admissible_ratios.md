# Definition 1.8. Admissible ratios

Let $n\in\mathbb{Z}_{\geq1}$, $A,C\in\mathbb{R}^n$, and $b,d\in\mathbb{R}$. The coefficient tuple $(A,b,C,d)$ is **admissible** when:

1. $C^\top x+d\gt0$ for every $x\in\lbrace0,1\rbrace^n$.
2. The entries of $C$ are all strictly positive, all strictly negative, or all zero.
3. If $C=0$, the entries of $A$ are all strictly positive, all strictly negative, or all zero. Otherwise $A$ is unrestricted.

The numerator constant $b$ is arbitrary.

An **admissible ratio** $R$ is the function specified by such a tuple:

$$ R(x)=\frac{A^\top x+b}{C^\top x+d}, \qquad x\in\lbrace0,1\rbrace^n. $$

Admissibility is a condition on the coefficient tuple specifying the ratio.
