# A two-coordinate certificate cannot have all five digit matrices irreducible

This is an unbounded analytic obstruction for the full mixed-base Collatz rewriting system. It applies to nonnegative **real** matrix coefficients as well as natural coefficients. It does not exclude every two-coordinate certificate: reducible digit-matrix cases remain.

Use the rule names in [rewriting-rank-obstructions.md](rewriting-rank-obstructions.md). Write \(A,B,E,F,G\) for the matrices of the five digit symbols \(a,b,e,f,g\), and \(C,D\) for the two boundary matrices. Every matrix is nonnegative, and every first diagonal entry is at least one. Affine offsets can be arbitrary nonnegative vectors; the obstruction below already occurs in the matrix inequalities, before offsets or strictness are considered.

**Theorem.** If all eleven rules are weakly oriented by two-coordinate affine interpretations, at least one of \(A,B,E,F,G\) is reducible. Equivalently, at least one of these five \(2\times2\) matrices has a zero off-diagonal entry.

No bound on the coefficients is imposed. The theorem does not assume the Collatz conjecture or a bound on numerical trajectories.

## 1. Aggregate irreducibility makes every swap matrix inequality exact

The six swap matrix inequalities are
\[
\begin{array}{lll}
AE\ge EA,&AF\ge EB,&AG\ge FA,\\
BE\ge FB,&BF\ge GA,&BG\ge GB.
\end{array} \tag{1}
\]
Put \(P=A+B\) and \(Q=E+F+G\). Summing gives
\[
PQ\ge QP. \tag{2}
\]
If either \(P\) or \(Q\) is irreducible, (2) is an equality. Indeed, for an irreducible nonnegative matrix \(P\), its positive left and right Perron vectors \(u,v\) give
\[
u^{\mathsf T}(PQ-QP)v=0.
\]
The commutator is entrywise nonnegative and every weight \(u_i v_j\) is positive, so every entry vanishes. The argument with \(Q\) irreducible is identical.

Each difference in (1) is nonnegative and their sum is zero. Thus every difference is zero. In particular, under the theorem's contrary assumption that all five digit matrices are irreducible, we have the exact relations
\[
\boxed{AE=EA,\quad AF=EB,\quad AG=FA,\quad
BE=FB,\quad BF=GA,\quad BG=GB.} \tag{3}
\]

The aggregate observation also holds in higher dimensions. The classification below specifically uses dimension two.

## 2. Classification needed from the exact relations

For this section assume all five matrices are nonnegative, irreducible, \(2\times2\), and have positive first diagonal entries. In dimension two, irreducibility means both off-diagonal entries are positive. Each matrix therefore has a positive simple Perron eigenvalue, a positive left and right Perron vector, and another real eigenvalue of strictly smaller absolute value. The last strictness follows also from its positive trace, which excludes a second eigenvalue equal to the negative Perron eigenvalue.

We prove that (3) has only the following alternatives:

1. All five matrices share a positive left Perron vector and a positive right Perron vector. Their Perron eigenvalues are \(\alpha\) for \(A,B\), and \(\beta\) for \(E,F,G\).
2. All five matrices are nonsingular and share a positive **left** Perron vector. For some \(\mu,\nu>0\), the binary eigenvalues are \((2\mu,\mu)\), the ternary eigenvalues are \((3\nu,\nu)\), and
   \[
   E=\frac{2\nu}{\mu}A-\nu I,\qquad
   F=\frac{\nu}{\mu}(A+B)-\nu I,\qquad
   G=\frac{2\nu}{\mu}B-\nu I. \tag{4}
   \]

### 2.1 All five matrices nonsingular

The relations \(AG=FA\) and \(BE=FB\) give
\[
F=AGA^{-1}=BEB^{-1}.
\]
Thus \(E,F,G\) have the same trace and determinant. Taking determinants in \(AF=EB\) gives \(\det A=\det B\). The remaining identities give
\[
AB=EB^2E^{-1},\qquad BA=GA^2G^{-1}.
\]
Consequently,
\[
\operatorname{tr}(AB)=\operatorname{tr}(A^2)=\operatorname{tr}(B^2).
\]
Since \(\operatorname{tr}A,\operatorname{tr}B>0\) and their determinants agree, their traces agree as well. Hence \(A,B\) have the same characteristic polynomial.

If \(A=B\), invertibility immediately gives \(E=F=G\). The commuting irreducible pair \(A,E\) has common positive left and right Perron vectors, yielding alternative 1.

Suppose \(A\ne B\), and put \(N=B-A\). The trace identities imply
\[
\operatorname{tr}N=\operatorname{tr}(N^2)=\operatorname{tr}(AN)=0.
\]
Thus \(N\) is nonzero nilpotent of rank one. Write \(N=uv^{\mathsf T}\), where \(v^{\mathsf T}u=0\). From \(v^{\mathsf T}Au=\operatorname{tr}(AN)=0\), the line
\[
\operatorname{im}N=\ker N=\mathbb Ru
\]
is invariant under \(A\), hence also \(B\). Their distinct eigenvalues imply that \(E\), which commutes with \(A\), preserves this line; similarly \(G\) preserves it because it commutes with \(B\). The displayed similarity formula for \(F\) then shows that \(F\) preserves it as well. Its annihilating left line is also common to all five matrices.

The common right line is either the positive Perron line for all five matrices, or is sign-changing and has a positive annihilating left Perron vector for all five. Positivity of a Perron vector and uniqueness of its eigenline justify this dichotomy.

If the common right line is the Perron line, choose a basis in which
\[
A=\begin{pmatrix}\alpha&x\\0&\kappa\end{pmatrix},\quad
B=\begin{pmatrix}\alpha&x+d\\0&\kappa\end{pmatrix},\quad d\ne0,
\]
and
\[
E=\begin{pmatrix}\beta&y\\0&\tau\end{pmatrix},\quad
F=\begin{pmatrix}\beta&y+e\\0&\tau\end{pmatrix},\quad
G=\begin{pmatrix}\beta&y+g\\0&\tau\end{pmatrix}.
\]
Here \(|\kappa|<\alpha\) and \(|\tau|<\beta\). Subtracting the \(AE=EA\) offset equation from the other equations in (3) gives
\[
\alpha e=\beta d,\quad
(\tau-\beta)d=\kappa e,\quad
\alpha g=\kappa e,\quad
(\alpha-\kappa)g=(\beta-\tau)d.
\]
Eliminating \(e,g,\tau\) gives
\[
\kappa(2\alpha-\kappa)=0.
\]
The root \(\kappa=2\alpha\) contradicts Perron dominance; the root \(\kappa=0\) would give \(\tau=\beta\), also a contradiction. Thus this common-right case is impossible when \(A\ne B\).

In the common-left Perron case, use the transposed triangular shape instead:
\[
A=\begin{pmatrix}\alpha&0\\x&\kappa\end{pmatrix},\quad
B=\begin{pmatrix}\alpha&0\\x+d&\kappa\end{pmatrix},\quad d\ne0,
\]
with ternary matrices having lower-left entries \(y,y+e,y+g\) and diagonal entries \(\beta,\tau\). The corresponding four equations are
\[
\kappa e=\tau d,\quad
(\beta-\tau)d=\alpha e,\quad
\kappa g=\alpha e,\quad
(\alpha-\kappa)g=(\beta-\tau)d.
\]
They force \(g\ne0\): otherwise \(e=0\), then \(\tau=0\), then \(\beta=0\), which is impossible. Consequently \(\alpha=2\kappa\); substituting back gives \(\beta=3\tau\). Set \(\mu=\kappa>0\), \(\nu=\tau>0\). The baseline equation \(AE=EA\) gives \(y=2\nu x/\mu\), and the other equations give
\[
e=\nu d/\mu,\qquad g=2\nu d/\mu.
\]
These are precisely (4), so alternative 2 holds.

### 2.2 A binary matrix is singular

First suppose \(A\) is singular and \(B\) is nonsingular. An irreducible singular nonnegative \(2\times2\) matrix is strictly positive and rank one, so write
\[
A=ua^{\mathsf T},\qquad u,a>0,
\qquad\alpha_A=a^{\mathsf T}u.
\]
The equality \(AF=EB\) forces \(E\) to have rank one. Since \(A,E\) commute and are positive rank-one matrices, \(E=tA\) for some \(t>0\). Also \(F=BEB^{-1}\), so its Perron eigenvalue is \(\beta=t\alpha_A\).

From \(AG=FA\), equality of nonzero rank-one products gives
\[
Fu=\beta u,\qquad a^{\mathsf T}G=\beta a^{\mathsf T}.
\]
In particular \(\rho(G)=\beta\). Because \(B,G\) commute and \(G\) is irreducible, \(a^{\mathsf T}\) is also a left Perron vector of \(B\); write its eigenvalue as \(\alpha_B\). Then \(AF=EB\) implies
\[
a^{\mathsf T}F=t\alpha_B a^{\mathsf T}.
\]
The left vector is positive, so \(t\alpha_B=\rho(F)=t\alpha_A\). Hence \(\alpha_A=\alpha_B=:\alpha\).

Apply \(BE=FB\) to \(u\). It says \(F(Bu)=\beta Bu\), so uniqueness of the positive right Perron line of \(F\) gives \(Bu=\alpha u\). Applying \(BF=GA\) to \(u\) then gives \(Gu=\beta u\). Thus all five matrices share \(u,a^{\mathsf T}\) as positive right and left Perron vectors, with the claimed common binary and ternary eigenvalues.

The case \(B\) singular and \(A\) nonsingular follows by the symmetry \(A\leftrightarrow B\), \(E\leftrightarrow G\) of (3).

If both binary matrices are singular, write \(A=ua^{\mathsf T}\), \(B=vb^{\mathsf T}\), with all four vectors positive. The identities \(AG=FA\) and \(BE=FB\) make \(u,v\) positive right Perron vectors of \(F\), so they are proportional. Rescale to write \(B=ub^{\mathsf T}\).

Those identities also show that \(\rho(E)=\rho(F)=\rho(G)=:\beta\). From \(AG=FA\) and \(BG=GB\), both \(a^{\mathsf T}\) and \(b^{\mathsf T}\) are positive left Perron vectors of \(G\); hence \(B=tA\). Now \(AE=EA\) and \(AF=EB\) give \(a^{\mathsf T}F=t\beta a^{\mathsf T}\), forcing \(t=1\). The same equations show that the common left and right Perron vectors are shared by all five matrices. This again yields alternative 1.

### 2.3 Binary matrices nonsingular, ternary matrices singular

The similarity relations imply that \(E,F,G\) are all positive rank-one matrices with a common Perron eigenvalue \(\beta\). Write their positive right factors initially as \(u,z,v\), respectively.

From \(AF=EB\), we get \(Az\) proportional to \(u\). From \(AG=FA\), we get \(Av\) proportional to \(z\). Hence \(A^2v\) is proportional to \(u\). But \(A\) commutes with \(E\), so \(u\) is its positive Perron vector. Invertibility of \(A\) gives \(v\) proportional to \(u\), and then \(z\) is proportional to \(u\) as well.

Normalize the rank-one factorizations as
\[
E=ue^{\mathsf T},\qquad F=uf^{\mathsf T},\qquad
G=ug^{\mathsf T},\qquad
e^{\mathsf T}u=f^{\mathsf T}u=g^{\mathsf T}u=\beta.
\]
Commutation with \(E,G\) makes \(u\) a right Perron vector of \(A,B\). Evaluating \(AF=EB\) on \(u\) shows their eigenvalues agree; call the common value \(\alpha\).

The relations \(AG=FA\) and \(BF=GA\) give
\[
f^{\mathsf T}A=\alpha g^{\mathsf T},\qquad
g^{\mathsf T}A=\alpha f^{\mathsf T}.
\]
Thus \(f^{\mathsf T}-g^{\mathsf T}\) would be a left eigenvector of \(A\) with eigenvalue \(-\alpha\) unless it vanishes. The positive first diagonal entry excludes that eigenvalue, so \(f=g\). The identities \(AF=EB\), \(BE=FB\) give the same argument for \(B\), forcing \(e=f\). Hence all five matrices share the positive right vector \(u\) and positive left vector \(e^{\mathsf T}\), giving alternative 1.

This exhausts the singular cases and proves the classification.

## 3. The boundary and dynamic inequalities exclude both alternatives

The required full-system matrix inequalities are:
\[
BD\ge GD,\qquad CE\ge CB,\qquad CF\ge CA^2,
\qquad CG\ge CAB. \tag{5}
\]
Alternative 1 uses the first and third, while alternative 2 uses the first, second, and fourth.

### Common positive left and right Perron vectors

Let \(w^{\mathsf T},v\) be the common positive left and right vectors in alternative 1. Multiplying \(BD\ge GD\) by \(w^{\mathsf T}\) gives
\[
(\alpha-\beta)w^{\mathsf T}D\ge0.
\]
The first entry of \(w^{\mathsf T}D\) is positive because \(w_1>0\) and \(D_{11}\ge1\), so \(\alpha\ge\beta\).

Applying \(CF\ge CA^2\) to \(v\) gives
\[
(\beta-\alpha^2)Cv\ge0.
\]
The first coordinate of \(Cv\) is positive because \(C_{11}\ge1\), so \(\beta\ge\alpha^2\). Therefore \(\alpha\ge\alpha^2\). But irreducibility gives
\[
\alpha=\rho(A)>A_{11}\ge1,
\]
a contradiction.

### The exceptional common-left family

Let \(w^{\mathsf T}>0\) be its common left Perron vector. Let \(v_a,v_b>0\) be the right Perron vectors of \(A,B\), normalized by
\[
w^{\mathsf T}v_a=w^{\mathsf T}v_b=1.
\]
Their two eigenvalues and (4) give the exact projector formulas
\[
\begin{aligned}
A&=\mu I+\mu v_aw^{\mathsf T},&
B&=\mu I+\mu v_bw^{\mathsf T},\\
E&=\nu I+2\nu v_aw^{\mathsf T},&
G&=\nu I+2\nu v_bw^{\mathsf T}.
\end{aligned} \tag{6}
\]
The dynamic inequality projected by \(w^{\mathsf T}\) gives
\[
2\mu\ge3\nu. \tag{7}
\]
Put
\[
u=(Cv_a)_1>0,\qquad v=(Cv_b)_1>0.
\]
Evaluate \(CE\ge CB\) on \(v_a\). Formula (6) gives
\[
3\nu u\ge\mu(u+v).
\]
Together with (7), this yields \(u\ge v\).

Next evaluate \(CG\ge CAB\) on \(v_b\). It gives
\[
3\nu v\ge2\mu^2(u+v).
\]
Using (7) once more,
\[
\mu\le\frac{v}{u+v}\le\frac12.
\]
But \(2\mu=\rho(A)>A_{11}\ge1\), so \(\mu>1/2\). This is the second contradiction.

The proof uses neither integrality nor affine offsets. It therefore establishes the theorem for the stated nonnegative-real relaxation and all natural matrix interpretations contained in it.

## What remains

Any full-system two-coordinate candidate, even before requiring a strict rule, must have at least one reducible digit matrix. The exact-swap deduction in section 1 still applies whenever either aggregate \(A+B\) or \(E+F+G\) is irreducible, so some mixed-support cases inherit additional structure. They have not all been classified here.

No conclusion about higher-dimensional natural matrices, top rewriting, or arctic interpretations follows from this two-coordinate classification. Those require their own arguments.
