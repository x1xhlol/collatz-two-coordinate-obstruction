# First diagonal entries for compatible triangular digit matrices

**Claim.** Consider the full forward eleven-rule system with nonnegative
two-coordinate affine interpretations and every symbol matrix satisfying
`M[0][0] ≥ 1`. Suppose the five digit matrices `A,B,E,F,G` are all upper
triangular, or all lower triangular. If all eleven rules are weakly
decreasing, then the first diagonal entry of every digit matrix is **1**.
The boundary matrices `C,D` need not be triangular. Affine offsets do not
enter this necessary condition.

This is a restriction on weak matrix models, not a termination
certificate. It does not assert that all matrix entries or affine offsets
are fixed.

## The common first diagonals

The matrix inequalities are

\[
AD\ge D,\quad BD\ge GD,
\]
\[
AE\ge EA,\quad AF\ge EB,\quad AG\ge FA,\quad
BE\ge FB,\quad BF\ge GA,\quad BG\ge GB,
\]
\[
CE\ge CB,\quad CF\ge CA^2,\quad CG\ge CAB,
\]

where comparisons are entrywise. Set `P=A+B` and `Q=E+F+G`.
The sum of the six nonnegative swap deficits is `PQ−QP`. Its trace
is zero, so every diagonal entry of every individual swap deficit is zero.

For either common triangular orientation, diagonal entries multiply as
scalars. The first-diagonal equality in `AG=FA` gives `G₀₀=F₀₀`, that in
`BE=FB` gives `E₀₀=F₀₀`, and that in `AF=EB` gives `A₀₀=B₀₀`. Cancellation
is valid because all five first diagonal entries are positive. Write

\[
A_{00}=B_{00}=t\ge1,\qquad
E_{00}=F_{00}=G_{00}=s\ge1.
\]

All appearances of equality above concern the diagonal entries only; the
complete swap matrices need not be equal.

## Upper-triangular digits

Write

\[
A=\begin{pmatrix}t&\alpha\\0&u\end{pmatrix},\quad
B=\begin{pmatrix}t&\beta\\0&v\end{pmatrix},\quad
G=\begin{pmatrix}s&\gamma\\0&y\end{pmatrix}.
\]

The `(0,0)` entry of `CG≥CAB` is
`C₀₀(s−t²)≥0`, hence `s≥t²`.

Suppose `s>t`. The `(0,0)` entry of `BD≥GD` gives

\[
(\beta-\gamma)D_{10}\ge(s-t)D_{00}>0.
\]

Thus `D₁₀>0` and `β>γ`. The `(1,0)` entries of `AD≥D` and
`BD≥GD` then imply, respectively,

\[
u\ge1,\qquad v\ge y.
\]

Now the `(0,1)` entry of `CG≥CAB` reads

\[
C_{00}(\gamma-t\beta-\alpha v)+C_{01}(y-uv)\ge0.
\]

Since `y−uv≤0` and `C₀₀>0`, this forces

\[
\gamma\ge t\beta+\alpha v\ge\beta,
\]

contradicting `β>γ`. Consequently `s≤t`. Together with `t²≤s`
and `t≥1`, this gives `t=s=1`.

This upper-triangular argument uses no second-diagonal swap identities.

## Lower-triangular digits

Write

\[
A=\begin{pmatrix}t&0\\\alpha&u\end{pmatrix},\quad
B=\begin{pmatrix}t&0\\\beta&v\end{pmatrix},\quad
E=\begin{pmatrix}s&0\\\varepsilon&w\end{pmatrix},
\]
\[
F=\begin{pmatrix}s&0\\\varphi&x\end{pmatrix},\quad
G=\begin{pmatrix}s&0\\\gamma&y\end{pmatrix}.
\]

The `(0,0)` entry of `BD≥GD` is `(t−s)D₀₀≥0`, so `t≥s`.
It remains to exclude `t>1`. Assume this; then `s≤t<t²`.

The `(0,0)` entry of `CF≥CA²` gives

\[
C_{00}(s-t^2)+C_{01}\bigl(\varphi-(t+u)\alpha\bigr)\ge0.
\]

Its first term is strictly negative. Therefore

\[
C_{01}>0,\qquad \varphi>(t+u)\alpha.\tag{1}
\]

Using `C₀₁>0`, the `(0,1)` entries of the three boundary inequalities
give

\[
w\ge v,\qquad x\ge u^2,\qquad y\ge uv.\tag{2}
\]

Their `(0,0)` entries also give

\[
\varepsilon\ge\beta,\qquad
\gamma>t\alpha+u\beta.\tag{3}
\]

The second-diagonal swap equalities include

\[
ux=wv,\qquad uy=xu,\qquad vx=yu.\tag{4}
\]

If `u=0`, equations (2) and (4) give `wv=0` and `w≥v`, hence
`v=0`. The `(1,0)` swap inequality `AG≥FA` gives

\[
t\varphi\le(s-x)\alpha\le s\alpha\le t\alpha,
\]

so `φ≤α`, contrary to (1), which gives `φ>tα≥α`.

Suppose instead `u>0`. Since `x≥u²>0`, equations (4) imply

\[
u=v=r>0,\qquad w=x=y=h\ge\max(r,r^2).\tag{5}
\]

The `(1,0)` entry of `BD≥GD` is now

\[
(\beta-\gamma)D_{00}+(r-h)D_{10}\ge0.
\]

Because `h≥r` and `D₀₀>0`, this gives `β≥γ`.
If `r≥1`, (3) gives `γ>tα+rβ≥β`, a contradiction.
Thus only `0<r<1` remains.

The `(1,0)` entry of `AE≥EA` gives

\[
(t-r)\varepsilon\le(s-h)\alpha\le(t-r)\alpha.
\]

Here `t−r>0`, and the last inequality follows from `s≤t` and `h≥r`.
Consequently `ε≤α`. Combining this with (3) and `β≥γ` gives

\[
\gamma\le\beta\le\varepsilon\le\alpha.
\]

Finally `AG≥FA` yields

\[
t\varphi\le(s-h)\alpha+r\gamma
\le(s-h+r)\alpha\le s\alpha\le t\alpha.
\]

Thus `φ≤α`, again contradicting (1), since `t+r>1`.
This excludes `t>1`. Therefore `t=1` and `1≤s≤t` gives `s=1`.

The proof includes zero off-diagonal entries and arbitrary nonnegative
real coefficients. It uses `C₀₀,D₀₀>0` but makes no triangularity
assumption on either boundary matrix.

## Reversed rules

The same necessary condition holds when every rule word is reversed.
Given a weak matrix model for the reversed system, transpose each symbol
matrix. For a word `w=s₁⋯sₖ`,

\[
\bigl(M_{s_k}\cdots M_{s_1}\bigr)^{\mathsf T}
=M_{s_1}^{\mathsf T}\cdots M_{s_k}^{\mathsf T}.
\]

Transposition preserves entrywise inequalities and first diagonal
entries, and exchanges the common upper and lower orientations. The
transposed matrices therefore give a forward weak matrix model to which
the proof applies. This argument concerns only the matrix parts; no
transposition assertion about affine offsets is needed.
