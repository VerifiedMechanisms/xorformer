# Checkerboard restrictions

Let $n\in\mathbb{Z}_{\geq2}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. A [two-coordinate restriction](10_two_coordinate_restrictions.md) $g(a,b)=f(x^{(a,b)})$ is a **checkerboard restriction** if there exists $c\in\lbrace0,1\rbrace$ such that

$$ g(0,0)=g(1,1)=c, \qquad g(0,1)=g(1,0)=1-c. $$

The two diagonals have opposite labels, with both choices of $c$ allowed. The function $f$ **contains a checkerboard restriction** if some choice of the free coordinates and fixed assignment has this property.
