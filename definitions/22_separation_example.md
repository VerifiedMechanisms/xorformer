# Definition 1.22. Separation example

For a ten-bit input $z\in\lbrace0,1\rbrace^{10}$, encode its two blocks of five bits as sign vectors:

$$ x_i=1-2z_i, \qquad y_i=1-2z_{5+i}, \qquad i\in\lbrace1,\ldots,5\rbrace. $$

Thus $x,y\in\lbrace-1,+1\rbrace^5$. Write the inverse encoding as

$$ z(x,y)=\left(\frac{1-x_1}{2},\ldots,\frac{1-x_5}{2},\frac{1-y_1}{2},\ldots,\frac{1-y_5}{2}\right). $$

Define the quadratic polynomial

$$ Q(x,y)=\left(\sum_{i=1}^{5}x_i\right)\left(\sum_{j=1}^{5}y_j\right)-3\sum_{i=1}^{5}x_i y_i. $$

The **separation example** is the Boolean function $f_{10}:\lbrace0,1\rbrace^{10}\to\lbrace0,1\rbrace$ specified by

$$ f_{10}(z(x,y))=1\quad\Longleftrightarrow\quad Q(x,y)\gt0. $$
