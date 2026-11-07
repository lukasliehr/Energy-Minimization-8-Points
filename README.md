# Energy minimization for eight points on the sphere

This repository contains a Lean 4 formalization as well as numerical certificates of results from the paper
**Energy minimization for eight points on the sphere** by **Liudmyla Kryvonos**,
**Lukas Liehr** and **Mitchell A. Taylor**.

![The Coulomb-optimal square antiprism on the unit sphere.](Visualization/square-antiprism.gif)

The animation shows $X(a_1)$ with $a_1\approx0.314089367889$. The two
squares lie at heights $\pm\sqrt{a_1}$; the view from above shows their
relative rotation by $\pi/4$. The configuration is fixed while the viewing
direction changes. Its Coulomb energy is approximately $19.675287861233$.

## Lean-verified statements

In order to state the formalized result we define for eight distinct points $Y=(y_1,\ldots,y_8)$ on the unit sphere
$S^2\subset\mathbb{R}^3$ the quantities
```math
\begin{aligned}
E_s(Y)&=\frac1s\sum_{1\le i\lt j\le8}\lVert y_i-y_j\rVert^{-s},\qquad s>-2,\ s\ne0,\\
E_0(Y)&=-\sum_{1\le i\lt j\le8}\log\lVert y_i-y_j\rVert.
\end{aligned}
```
For $s\gt0$ the factor $1/s$ does not change the minimizers; for $s\lt0$ it turns
minimizing $E_s$ into maximizing the sum of the distance powers.
For $0\lt a\lt1$, let $X(a)$ be the square antiprism formed by two squares
at heights $\pm\sqrt a$, each of radius $\sqrt{1-a}$, with relative
rotation $\pi/4$. Congruence means equality up to an orthogonal
transformation and a permutation of the points. We provide a Lean verification of the following statement.

**Theorem.** The following two statements hold.

**(i) Global optimality for all exponents.** For each $s\gt-2$, the function
$a\mapsto E_s(X(a))$ has a unique stationary parameter $a_s\in(0,1)$,
with $a_0=(2\sqrt{58}-13)/7$. For every $s\gt-2$ and every configuration
$Y$ of eight distinct points on $S^2$, $E_s(Y)\ge E_s(X(a_s))$, with
equality if and only if $Y$ is congruent to $X(a_s)$. Moreover, the minimal
logarithmic ($s=0$) and Coulomb ($s=1$) energies are

```math
\begin{aligned}
E_0(X(a_0))={}&-12\log 2-6\log(1-a_0)-4\log(1+6a_0+a_0^2),\\
E_1(X(a_1))={}&\frac{4\sqrt{2}+2}{\sqrt{1-a_1}}
+\frac{8}{\sqrt{2-\sqrt{2}+(2+\sqrt{2})a_1}}\\
&+\frac{8}{\sqrt{2+\sqrt{2}+(2-\sqrt{2})a_1}}.
\end{aligned}
```

**(ii) Completely monotone potentials.** There exist a smooth function
$f:(0,\infty)\to\mathbb{R}$ and a configuration $Y$ of eight distinct
points on $S^2$ such that
$(-1)^k f^{(k)}(t)\gt0$ for every integer $k\ge0$ and every $t\gt0$,
$\lim_{t\downarrow0}f(t)=\infty$, and

```math
\sum_{1\le i\lt j\le8}f\bigl(\lVert y_i-y_j\rVert^2\bigr)
\lt\sum_{1\le i\lt j\le8}f\bigl(\lVert x_i(a)-x_j(a)\rVert^2\bigr)
\qquad\text{for every }a\in(0,1),
```

where $x_1(a),\ldots,x_8(a)$ are the vertices of $X(a)$.
Thus no square antiprism minimizes the energy associated with $f$.

> [!NOTE]
> The two proved theorems depend only on `propext`, `Classical.choice`
> and `Quot.sound`. **No** `native_decide` was used.

## Computer-assisted proof for all nonnegative exponents

The Lean proof of global optimality in (i) for $s\ge0$, in [LeanCode/AllS](LeanCode/AllS),
covers $[0,97]$ by 30 cells, each with an exact certificate checked by the Lean kernel, and
treats $s\ge97$ by an analytic argument with exact algebraic certificates.
The certificates carried by the Lean proof, with their Python checkers, are
in [LeanCode/CertificatesLean](LeanCode/CertificatesLean).

The directory [Certificates_All_s](Certificates_All_s) contains an independent
computer-assisted proof that $X(a_s)$ is the unique global minimizer, up to congruence,
for every real $s\gt0$ and for logarithmic energy at $s=0$. The proof uses
exact interval certificates on 111 closed intervals covering $[0,124]$,
together with an analytic argument and exact computational checks for
$s\ge124$. The certificate data and
[verification records](Certificates_All_s/verification)
are included. Instructions for reproducing the computations are in
[CAP.md](Certificates_All_s/CAP.md).

## Computer-assisted proof for negative exponents

The Lean proof of global optimality in (i) for $-2\lt s\lt0$, in
[LeanCode/Negative_s](LeanCode/Negative_s), subtracts an exactly summable centroid term from the
energy and covers $q=(s+2)/2\in[0,1]$ by five cells, each with an exact certificate checked by the
Lean kernel. The certificate data are part of the Lean source. At $s=-2$ the minimizers are exactly
the configurations with centroid zero, so uniqueness fails there.

## Lean entry points

- [Showcase.lean](Showcase.lean): the definitions and two theorem statements,
  with `sorry` in place of the proofs.
- [Showcase_WithProofs.lean](Showcase_WithProofs.lean): the same definitions
  and statements with complete proofs.
- [LeanCode.lean](LeanCode.lean): the complete proof library.
- [LeanCode/MainTheorem.lean](LeanCode/MainTheorem.lean): the global
  optimality results.
- [LeanCode/AllS/ThomsonCompact/Main/Final.lean](LeanCode/AllS/ThomsonCompact/Main/Final.lean):
  global optimality for every $s\ge0$.
- [LeanCode/Negative_s/ThomsonNegative/Finalization/Verified.lean](LeanCode/Negative_s/ThomsonNegative/Finalization/Verified.lean):
  global optimality for every $-2\lt s\lt0$.
- [LeanCode/Monotonic/Proof.lean](LeanCode/Monotonic/Proof.lean): the
  counterexample for completely monotone potentials.
- [comparator.json](comparator.json): Comparator configuration for the
  two theorems and their definitions in the two showcase files.

## Repository layout

| Path | Contents |
| --- | --- |
| [LeanCode/LargeS](LeanCode/LargeS) | Global optimality for sufficiently large Riesz exponents. |
| [LeanCode/AllS](LeanCode/AllS) | Global optimality for every exponent $s\ge0$. |
| [LeanCode/Negative_s](LeanCode/Negative_s) | Global optimality for every exponent $-2\lt s\lt0$. |
| [LeanCode/Monotonic](LeanCode/Monotonic) | Counterexample for completely monotone potentials. |
| [LeanCode/Bridge.lean](LeanCode/Bridge.lean) | Coordinates of the large-exponent development in the notation of the paper. |
| [LeanCode/CertificatesLean](LeanCode/CertificatesLean) | Certificates carried by the Lean proof for every exponent $s\ge0$, with Python checkers. |
| [Certificates_All_s](Certificates_All_s) | Independent certificates and checkers for every exponent $s\ge0$. |
| [Visualization](Visualization) | Animation, video and still image. |

## Building

The project uses Lean 4.33.0. The dependencies are pinned in
[lake-manifest.json](lake-manifest.json). To compile the library and both
showcase files, run

```sh
lake exe cache get
lake build
```

`Showcase.lean` produces two expected `sorry` warnings.
A complete build compiles 16,319 modules of this repository on top of Mathlib. With 36
parallel jobs it needs up to 100 GB of memory, and the `.lake` directory needs about
66 GB of disk space.
