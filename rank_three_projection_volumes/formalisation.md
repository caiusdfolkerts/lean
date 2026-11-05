# Rank-three obstructions to coordinate projection volumes

## The two principal statements

The source paper is Caius Folkerts, *Rank-three obstructions to coordinate projection volumes*, included as `paper.pdf`. This note states the verified results, explains the mathematical choices in the Lean source, and describes their proof dependencies. The paper supplies the geometric motivation; this note describes how its principal assertions and their supporting mathematics are represented and proved.

For a nonempty compact convex set $K\subset\mathbb R^n$, let $p_{ij}(K)$ be the ordinary $(n-2)$-dimensional Lebesgue volume after deleting coordinates $i,j$, and put $p_{ii}(K)=0$. Write $\mathcal R_n$ for the range of these arrays. Theorem 1.1 states that, for every $n\ge5$, every real symmetric matrix $P$ with

$$
P_{ii}=0,\qquad P_{ij}>0\ (i\ne j),\qquad \operatorname{rank}P=3
$$

lies outside $\overline{\mathcal R_n}$. Its inertia is $(1,2,n-3)$, and it is a limit of positive hollow matrices of inertia $(1,n-1,0)$ outside the same closure. Consequently there is a nonempty open family of such strict counterexamples, where openness is relative to the space of hollow symmetric matrices.

Theorem 3.1 applies to *every* $1\le k<n$. If $I$ is a $k$-element set of deleted coordinates and $S_u=[-u/2,u/2]$, it identifies the closure of the coordinate projection tuples with

$$
\left(\frac{n!}{(n-k)!}
V_n\bigl(K[n-k],(S_{U_i})_{i\in I}\bigr)\right)_{|I|=k}.
$$

Here $K$ and the $n$ marked vectors $U_i$ are arbitrary; zero and dependent marks are permitted. Every tuple admits a representation with $\dim\operatorname{aff} K\ge n-k+1$.

## Objects whose meanings are fixed independently

`Space n` is the function space $\mathrm{Fin}\,n\to\mathbb R$, with its product Lebesgue measure and coordinate maximum norm. `Body n` is Mathlib's actual `ConvexBody (Space n)`: a nonempty compact convex set, with no interior condition built into the definition. `deleteCoordinates` is literal coordinate restriction. `coordinateVolume` measures its image; `closedProjectionLocus` is the topological closure of its range.

Mixed volume comes from the Minkowski volume-polynomial development. The identity between coordinate deletion and marked mixed volume is proved by iterated interval extrusion and product measure. The two quantities have independent definitions. Matrix rank and inertia are Mathlib's actual matrix rank and quadratic-form invariants. The affine dimension of a body is the finite rank of the direction of its affine span. The `SignatureMeaning` layer explicitly identifies the three signature indices with the counts of positive, negative, and zero coefficients in a genuine diagonalisation, using Mathlib's formal Sylvester theorem.

## The finite obstruction and the lower-dimensional branch

The paper's Corollary 2.3 excludes a nonzero vector $x\ge0$ satisfying

$$
P_{ij}x_k\le P_{ik}x_j+P_{jk}x_i
\qquad(i,j,k\text{ pairwise distinct}).                 \tag{1}
$$

The source exposes the stronger unbounded-label version: for every $n\ge5$, strict positivity, hollowness, symmetry, and $\operatorname{rank}P\le3$ exclude such a vector. The declarations are `no_nonnegative_weighted_triangles` and `corollary_two_three`, in `VolumePapers.RankThree`.

The direct proof uses the cut decomposition in Lemma 2.2. For a positive four-point metric, the six cut coefficients are nonnegative. Expanding its actual determinant after the cut substitution shows that determinant zero forces the four singleton-cut coefficients to vanish. It follows that opposite edges agree and one of the three edge values is the sum of the other two. These are the rectangle relations for squared distances.

If a five-point metric had rank at most three, every four-label principal determinant would vanish. Applying the rectangle relations to four overlapping quadruples forces the three relevant positive edge values to agree; the sum relation then makes them zero. Restricting to five labels handles every larger finite label set. This is a symbolic proof for arbitrary real matrices, not a finite numerical experiment. It proves the obstruction needed here without separately asserting the circle-realisation conclusion of Lemma 2.2.

For strictly positive weights, $D_{ij}=P_{ij}/(x_ix_j)$ is an ordinary metric. The identity $D=\operatorname{diag}(x_i^{-1})P\operatorname{diag}(x_i^{-1})$ preserves the rank bound. For merely nonnegative weights, two zero coordinates contradict (1). If exactly one coordinate vanishes, replace it by a positive number no larger than the finitely many admissible upper bounds. Inequalities with that coordinate on the right are relaxed; those with it on the left hold by construction. Thus the boundary case is retained exactly.

**The geometric source of (1).** If $K$ lies in a proper affine subspace, translate it into a hyperplane $H$, choose a Euclidean unit normal $u$, and write $U_i=\alpha_i u+b_i$, with $b_i\in H$. The actual extrusion identity is

$$
n(n-1)V_n(K[n-2],S_{U_i},S_{U_j})
=N(\alpha_i b_j-\alpha_j b_i),                         \tag{2}
$$

where $N(v)=(n-1)V_{n-1}(K[n-2],S_v)$ is a seminorm. The source treats $\alpha_i=0$ and $\alpha_j=0$ explicitly. Its seminorm inequality follows from segment inclusion and monotonicity of mixed volume.

Applying $N$ to

$$
\alpha_k(\alpha_i b_j-\alpha_j b_i)
=\alpha_j(\alpha_i b_k-\alpha_k b_i)
-\alpha_i(\alpha_j b_k-\alpha_k b_j)
$$

gives (1) with $x_i=|\alpha_i|$. A nonzero array forces a nonzero weight. The theorem `nonfull_representation_impossible` therefore excludes all proper affine dimensions, not just the hyperplane case singled out in the paper.

**Relevant source.** `reading/volume_papers/metric_obstruction.lean`, `reading/volume_papers/weighted_triangles.lean`, `reading/projection/segment_seminorm.lean`, `reading/projection/hyperplane.lean`, and `reading/projection/hyperplane_obstruction.lean`.

## Compactification in the full range $1\le k<n$

The source follows the paper's affine-normalisation strategy, but replaces its singular-value contraction by a maximal-minor construction. The replacement handles singular marked matrices directly and preserves the exact coefficient normalisation.

Affine normalisation puts a body with interior between two fixed coordinate balls. An included TauCeti theorem proves this from a maximal-volume inscribed simplex. For a marked matrix $M$, let $d_j$ be the largest absolute value of a $j\times j$ minor, with $d_0=1$. The fixed inball, monotonicity, and the actual all-segment determinant formula bound $d_k$ by the marked coefficients. Set

$$
g=\max_{0\le j<k}d_j^{1/(k-j)}\ge1.
$$

Choose an active order $r<k$, so $d_r=g^{k-r}$. When $r>0$, choose a pivot $B$ with $|\det B|=d_r$ and, after row and column permutations, write

$$
M=\begin{pmatrix}B&A\\ C&D\end{pmatrix},\qquad
G=\begin{pmatrix}g^{-1}B^{-1}&0\\-CB^{-1}&I\end{pmatrix}.
$$

Then

$$
gGM=\begin{pmatrix}I&B^{-1}A\\0&g(D-CB^{-1}A)\end{pmatrix},
\qquad g^k|\det G|=1.
$$

Cramer's rule bounds the entries of $B^{-1}A$ and $CB^{-1}$ by one. Cofactors bound $g^{-1}B^{-1}$, and bordered determinants bound the remaining Schur complement by $\max(1,d_k)$. The case $r=0$ uses the identity map.

Replacing $(K,U)$ by $(GK,gGU)$ leaves every marked coefficient unchanged: the determinant contribution and the $k$ marked scaling factors multiply to one. The transformed bodies and marks are uniformly bounded. Moreover, $G$ fixes a coordinate subspace of dimension $n-r\ge n-k+1$; the transformed body contains a fixed disk in that subspace. There are finitely many possible pivot coordinate sets. Compactness of bounded compact convex bodies and continuity of actual mixed volume give a limiting representation retaining that disk and therefore the required affine dimension.

Conversely, approximate any marked matrix by invertible matrices. The exact determinant transport, followed by a positive dilation of the repeated body, turns an invertible marked array into an actual coordinate projection array. Continuity gives the desired limit. This direction includes dependent and zero marks and bodies without interior; none are discarded by the normalisation.

| Paper assertion                | Lean endpoint in `RankThreeProjection` |
|:-------------------------------|:---------------------------------------|
| Theorem 3.1, closure formula   | `theorem31`                            |
| Theorem 3.1, dimension bound   | `theorem31_with_dimension`             |
| Renormalising any marked tuple | `theorem31_renormalize_dimension`      |
| Complementary case $k=2$       | `complementary_compactification`       |

The six formulations of Theorem 3.1 are assembled in `source/development/compactification.lean`. Their proof closure includes the actual volume-polynomial theory, the maximal-minor lemmas, and the inherited affine-normalisation theorem.

## The full-dimensional finite-measure contradiction

For a body $K$ with interior, write

$$
q(A,C)=V_n(K[n-2],A,C),\qquad S_K(A)=S(K[n-2],A).
$$

Mixed area measures are constructed from the actual support-function functional. The real Hahn--Banach theorem extends it with a proved norm bound; positivity and the Riesz representation then produce finite positive measures. Their integral formula and centering are proved from the original mixed volumes.

The essential rigidity input is this: if $q(A,A)=q(A,C)=q(C,C)>0$, there is one translation vector $v$ such that $h_A-h_C=\langle v,\cdot\rangle$ almost everywhere for every actual marked segment area measure. Comparison bodies may be lower dimensional. `SegmentAreaRigidity` records this precise intermediate assertion. The quantile and first-variation argument below supplies its proof; the final assembly supplies the proved `fullDimensionalRigidity` term.

By Lemma 2.1's Lorentz factorisation, a positive hollow rank-three matrix is the weighted evaluation matrix of distinct circle points. If $W$ has rows a basis of its kernel, the cone

$$
\{y\ge0:Wy=0\}
$$

has an extreme ray for each polygon edge. That ray vanishes precisely at the edge's two endpoints. The finite-dimensional development constructs the rays and a measurable decomposition of vector measures into them.

For a proposed actual mixed-volume representation, set $z_i(u)=\langle U_i,u\rangle$ and $\mu_i=(n-1)S_K(S_{U_i})/2$. Then

$$
P_{ij}=\int|z_j|\,d\mu_i,\qquad
\int z_j\,d\mu_i=0,\qquad z_i=0\quad\mu_i\text{-a.e.}
$$

Positive and negative parts of each kernel row define two zonotopes with the same positive self- and cross-pairings. Pairing equality gives $W\mu=0$; rigidity gives $W|z(u)|=Lu$ for one linear map $L$.

Decompose $\mu_i=\sum_e r_i^e\nu_e$. Domination confines $\nu_e$ to the common zero set of all coordinates away from the two endpoints of $e$. Centering and strict positivity give, at each endpoint, zero signed moment and strictly positive absolute moment. If $H=\operatorname{span}(U_i)$ and $m_e=\int u\,d\nu_e$, then $m_e\in H^\perp$.

A relation among the $U_i$ having one zero coefficient propagates around the cycle and vanishes identically. Hence the relation space, and thus $H^\perp$, has dimension at most one. On the other hand,

$$
Lm_e=\gamma_{ea}W_a+\gamma_{eb}W_b,\qquad
\gamma_{ea},\gamma_{eb}>0,
$$

spans a space of dimension at least $n-4$; for odd $n$ the bound improves to $n-3$. It is at least two for every $n\ge5$ (the odd bound is needed at $n=5$). This contradicts containment in $L(H^\perp)$.

The source separates the exact measure construction from this finite argument. The intermediate `full_dimensional_obstruction_from_segment_rigidity` takes rigidity explicitly. The unconditional `full_dimensional_obstruction` supplies it from the checked analytic chain.

## Rigidity through actual quantiles and first variations

The paper invokes Shenfeld--van Handel's equality theorem. This formalisation proves the precise repeated-body rigidity needed here through actual quantiles and first variations.

Translate $K$ so that $0$ is interior, and separately translate $A,C$ to contain zero. Positive AF equality first forces $q(A,T)=q(C,T)$ for every actual body $T$: expand AF for $A+sT,C$, let $s\downarrow0$, and interchange $A,C$. The actual Minkowski polynomials for $K+tA$, $K+tC$, and $K+t(A+C)/2$ consequently have identical coefficients through degree two. Their midpoint volume deficit satisfies

$$
\frac{\operatorname{Vol}(K+t(A+C)/2)
-\sqrt{\operatorname{Vol}(K+tA)\operatorname{Vol}(K+tC)}}{t^2}\longrightarrow0
\quad(t\downarrow0).                                  \tag{3}
$$

`VolumePolynomialJets`, `PolynomialContact`, and `VolumeDeficit` derive (3) from actual mixed volumes. Polynomiality or an asymptotic estimate is not a hypothesis of their final statement.

Fix a unit direction and let $z_{A,t}(\tau)$ be the actual height quantile of uniform probability on $K+tA$. Kneser--Süss and the elementary inequality

$$
\frac{(x-y)^2}{8M^2}
\le\frac{x+y}{2\sqrt{xy}}-1\qquad(0<x,y\le M)
$$

turn (3) into vanishing normalized derivative energy on each compact interval $[a,b]\subset(0,1)$:

$$
\frac1{t^2}\int_a^b(z'_{A,t}-z'_{C,t})^2\,d\tau\longrightarrow0. \tag{4}
$$

The derivative bound is derived from actual section concavity and Cavalieri's formula. For a quasiconcave section density $f$, at least one tail has density everywhere at most $f(s)$, so the smaller tail mass is at most the width times $f(s)$. In probability coordinates this gives $\min(\tau,1-\tau)z'(\tau)\le\text{width}$.

Endpoint domination requires a separate argument. Compactness and an interior ball give $K\subset K+tA\subset(1+C_At)K$ for all $t\ge0$. Direct normalized CDF comparisons, and the preceding weighted derivative bound in both tails, give a uniform bound on

$$
\left|\frac{z_{A,t}(\tau)-z_K(\tau)}t\right|,
\qquad 0<\tau<1,
$$

independent of the unit direction. Cauchy--Schwarz applied to (4) makes the normalized difference $(z_{C,t}-z_{A,t})/t$ asymptotically constant on compact probability intervals. Dominated convergence and the actual centroid derivative identify the constant as $\langle u,v\rangle$ for a *single* vector $v$, common to all directions. Translating $C$ by $-v$ removes it. The Lipschitz bounds for sine and cosine then give zero first variation of all conditional ridge-test differences. Equal first volume derivatives remove probability normalization.

## From localized variations to the marked area supports

Here $C$ denotes the centroid-translated comparison body from the preceding page; it need not contain zero. The radial first-variation source treats nonsmooth $K$ and arbitrary comparison bodies. With $\rho$ the positive radial function of $K$, a continuous spatial test $\varphi$ contributes its value at the actual boundary point $\rho(u)u$. The difference of first variations is an integral of

$$
\varphi(\rho(u)u)\,w(u)
\bigl(h_A(\nabla\operatorname{gauge}_K(u))
-h_C(\nabla\operatorname{gauge}_K(u))\bigr),       \tag{5}
$$

with the explicit positive radial weight $w$. The support functions and gauge are those of the actual bodies. Measurability, integrability, and domination are separate lemmas in the source.

Take all sine and cosine ridge tests. Fourier uniqueness for finite positive measures, applied to the positive and negative parts of the integrable density, makes (5) vanish as a measure. The radial parametrisation is continuous and injective, so the density itself vanishes almost everywhere. If $D=\operatorname{conv}(A\cup C)$, then $h_D=\max(h_A,h_C)$. The nonnegative excess therefore has zero radial first variation. Identifying that variation with the first coefficient of the actual Minkowski polynomial gives

$$
q(D,K)=q(A,K).                                         \tag{6}
$$

This scalar identity avoids assuming an identification between a radial measure and the previously constructed area measure.

**The convex-hull amplification.** The identities

$$
(D+A)\cup(D+C)=2D,\qquad (D+A)\cap(D+C)=A+C
$$

persist after adding a common convex summand. Actual volume inclusion--exclusion and coefficient comparison give $q(D,D)+q(A,C)=q(D,A)+q(D,C)$. Write $a=q(A,A)$, $b=q(D,A)$, $m=q(A,K)$, and $k=q(K,K)>0$. Pairing equality and (6) give $q(D,D)=2b-a$ and $q(D,K)=m$. AF applied to $D+sK$ and $A+(s+1)K$, for every $s\ge0$, yields

$$
0\le (b-a-m)^2-ak-2k(b-a)(s+1).
$$

Thus $b\le a$; monotonicity gives $b\ge a$. Positive AF equality now implies $q(D,T)=q(A,T)=q(C,T)$ for every $T$. The continuous nonnegative functions $h_D-h_A$ and $h_D-h_C$ have zero integral against every actual marked area measure and hence vanish on its support. This is the strong support equality used in the rigidity argument.

**Coordinates and norms.** The analytic calculation is made in Euclidean coordinates. The original coordinate space has the maximum norm, so its dual unit sphere is different. `WeakHullTransfer` transports only (6), through an actual continuous linear equivalence and its positive Haar-volume conversion factor, and performs the area-measure amplification afterward. No unit spheres in different norms are identified. Translation reduction also explicitly adjusts the final vector for the separately translated comparison bodies.

The separate `CoordinateMeaning` layer proves that literal coordinate deletion, canonical Euclidean volume, and affine dimension agree exactly with the product-coordinate model. Its Haar factor is one. Thus `theorem11_euclidean` and `theorem31_euclidean` state the principal conclusions directly for Euclidean bodies and volumes.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The smaller topic files in `reading/` show the development before assembly; they are provided for navigation and are not an alternative build. The compiler checks the corresponding assembled development in `source/`. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.
