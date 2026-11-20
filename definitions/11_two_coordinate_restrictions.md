# Definition 1.11. Two-coordinate restrictions

Let $n\in\mathbb{Z}_{\geq2}$ and choose distinct coordinates $i,j\in\lbrace1,\ldots,n\rbrace$. Write $I=\lbrace1,\ldots,n\rbrace\setminus\lbrace i,j\rbrace$ and fix an assignment $\xi:I\to\lbrace0,1\rbrace$ to the other coordinates.

For free bits $(a,b)\in\lbrace0,1\rbrace^2$, the **restricted input** $x^{(a,b)}\in\lbrace0,1\rbrace^n$ is defined by

$$ x_k^{(a,b)}=\begin{cases} a & k=i, \cr b & k=j, \cr \xi_k & k\in I. \end{cases} $$

For any set $Y$ and function $F:\lbrace0,1\rbrace^n\to Y$, its **two-coordinate restriction** $F_{\mathrm{res}}$ is

$$ F_{\mathrm{res}}(a,b)=F(x^{(a,b)}). $$

The coordinates $i,j$ and assignment $\xi$ remain fixed throughout the restriction. When $n=2$, the set $I$ is empty and there are no fixed coordinates.
