# Definition 1.16. Symmetric functions

Let $n\in\mathbb{Z}_{\geq1}$. The **Hamming weight** of an input $x\in\lbrace0,1\rbrace^n$ is

$$ |x|=\sum_{i=1}^{n}x_i. $$

A Boolean function $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ is **symmetric** if it depends only on Hamming weight: there is a function $F:\lbrace0,1,\ldots,n\rbrace\to\lbrace0,1\rbrace$ such that

$$ f(x)=F(|x|). $$

We use $F$ for this sequence of labels indexed by weight.
