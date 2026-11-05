# Undecidability of mixed-volume realization

## What the formal statements mean

The object being recognized is the complete ordinary coefficient array of an actual volume polynomial. For nonempty compact convex sets $K_i\subset\mathbb R^d$, write

$$
\operatorname{Vol}_d\!\left(\sum_{i=0}^{n-1}t_iK_i\right)
=\sum_{|\alpha|=d}c_\alpha\prod_i t_i^{\alpha_i},\qquad t_i\geq0.
$$

In `VolumePolynomials.Definitions`, `Body d` is Mathlib's `ConvexBody` on $\mathrm{Fin}(d)\to\mathbb R$ and volume is product Lebesgue measure. No interior assumption is imposed on an individual body. `Realizes K c` quantifies over *every* nonnegative real weight tuple; `VolumeLocus n d` asserts the existence of such a tuple of bodies. Consequently a realization may use arbitrary compact convex sets, not just the zonoids constructed by the reduction.

The index type contains every $\alpha\in\mathbb N^n$ with $|\alpha|=d$. In degree three this includes $x_i^3$, $x_i^2x_j$, and $x_ix_jx_k$, with their ordinary polynomial coefficients. No mixed-volume normalization factors are silently dropped. The coefficient space has $\binom{n+2}{3}$ coordinates. Its dimensions at $n=12,44,91$ are respectively $364$, $15\,180$, and $129\,766$. `source/volume_polynomials/mixed_volume_basis_part01.lean` (the `PolynomialCoordinates` section) proves `exponent_multiIndexOfDegree` and `exists_coefficientPolynomial_iff`: the bounded index representation exhausts degree-$d$ monomials, and arrays correspond exactly to homogeneous polynomials. Both declarations are in `VolumePolynomials`.

| Paper | Principal Lean endpoint and exact scope |
|:---|:---|
| Theorem 1.1 | `MainResults.theorem_1_1`: co-r.e. completeness at $n=44$, including the nonnegative input subtype; undecidability and no sound, complete effective finite-certificate verifier for realizability. |
| Theorem 4.3 | `MainResults.theorem_4_3`: one dimension-uniform program, the complete rational array, and the same rational quadratic map with its full real-parameter equivalence. |
| Corollary 5.1 | `FixedSection.corollary_5_1_exists`: a fixed quadratic family on the entire $28$-coordinate probability simplex, with an undecidable rational coefficient-image promise problem in $\mathcal V_{91,3}$. |
| Theorem 6.1 | `ScalarSection.theorem_6_1`: a rational quadratic section of $\mathcal V_{12,3}$, all dyadic boundary-plane patches, and nonsemialgebraicity. The literal displayed automaton has a separate new endpoint. |

All names in this table are in the namespace `MixedVolume`. The note explains the proof dependencies actually needed by these endpoints. It does not claim the full generality of Lemma 3.1 or all of Proposition 3.2 as separately formalized results.

## The geometric encoding and its converse

The automaton data consist of $s>0$ rational row-stochastic $m\times m$ matrices $P_a$, an accepting column $f\in[0,1]^m$, and a common rational stationary probability row $\lambda$. For a word $w$, $P_w$ is the product in its given order. The condition encoded geometrically is

$$
\forall w\in\{0,\ldots,s-1\}^{*},\qquad pP_wf\leq\theta,
\quad p\in\Delta_{m-1},\quad 0<\theta<1.
\tag{1}
$$

The empty word is included. The geometric equivalence permits real $p,\theta$, even though the transition and stationary data used by the coefficient algorithm are rational.

Put $q=s+1$ and $\rho=1/(4s)$. Each word receives a distinct base-$q$ tag $t_w$, using the nonzero digits $1,\ldots,s$. The state bodies are convergent planar zonoid sums with generators

$$
v_j(w)=\rho^{|w|}a_j(w)(t_w,1),\qquad
a_j(w)=1+(P_wf)_j.
$$

The convergence estimates are proved before support functions or word sums are manipulated. The functional equations for these bodies are contractive and have unique compact convex solutions. A common stationary row gives the exact Minkowski relation

$$
\sum_j\lambda_j K_j=(1+\gamma)K_0,
\qquad \gamma=\lambda f.
$$

The deficit body exists precisely when every inequality in (1) holds. Its exposed edge in the direction assigned to $w$ records the corresponding nonnegative deficit. Distinct tags are essential: one word's violated inequality cannot be hidden by another word's edge.

The three-dimensional construction uses three axis segments, $s$ letter reference segments, one identity reference segment, $m$ state bodies, $sm$ transition images, and one deficit body. Thus

$$
N=3+s+1+m+sm+1=(s+1)m+s+5.
$$

Let $F_0$ be the canonical polynomial before the deficit body is added. The target is the formal substitution

$$
x_{B_j}\longmapsto x_{B_j}+\delta_j z,
\qquad \delta_j=\frac{1+\theta}{1+\gamma}\lambda_j-p_j.
\tag{2}
$$

If the deficit body exists, its Minkowski identity identifies this substitution with genuine volume on a nonempty open cone of weights. Polynomial identity then gives every coefficient, including coefficients at weights outside that cone.

The reverse implication starts from *an arbitrary realization* of the target array. Nonzero reference volume forces the total sum to have interior. The degree in a body variable recovers its dimension, forcing the references to be segments. Their determinant coefficients normalize the full reference configuration; vanishing widths place the remaining bodies in the required planes. Equality in the planar Minkowski inequality forces the prescribed translate relations. Contractive uniqueness then identifies the state bodies, and the exposed-edge argument recovers every word inequality.

This is where substantial convex geometry enters the dependency chain: Hausdorff limits and support functions, extrusion and projection formulas, dimension from polynomial degree, reference calibration, and the equality case of Minkowski's inequality. These are supported by local proof sources in `VolumePolynomials`, rather than being additional axioms.

**Source guide.** The geometric endpoint is `GeneralRealization.realization_iff_cutpoint` in `source/mixed_volume/general/realization_forward.lean`. The supporting modules establish the geometric encoding and its converse. The coefficient identification needed to turn it into Theorem 4.3 is the next stage.

## Exact rational moments and the entire volume

The coefficient calculation is finite rational mathematics, although the bodies are defined by infinite sums. The proof develops precisely the moment identities required by the construction. It supplies a direct route to Theorem 4.3 without assuming a general recognizable-weight summation theorem.

The first moments are

$$
M_j=\sum_w a_j(w)\rho^{|w|},\qquad
X_j=\sum_w a_j(w)\rho^{|w|}t_w.
$$

Splitting a word into the empty word or its first letter yields linear systems whose matrices are $\rho\sum_aP_a$ and $(\rho/q)\sum_aP_a$. The first has maximum absolute row sum $1/4$; the second is smaller. The pair-moment table determining mixed planar areas has $m^2$ entries and matrix

$$
\frac{\rho^2}{q}\sum_a P_a\otimes P_a.
$$

Terms with different first letters have prescribed determinant signs because their tag intervals are ordered. Their source term therefore depends only on the already determined $M$ and $X$. The table includes diagonal pairs, hence ordinary areas as well as mixed areas.

For every system $x=Tx+b$, the row bound proves that $I-T$ is nonsingular. The real solution is identified with the rational expression

$$
x=\frac{\operatorname{adj}(I-T)b}{\det(I-T)}.
$$

The nonzero denominator and equality with the actual geometric moment are proved. A rational solution is not introduced merely as a presumed fixed point. The common result is `RationalSystems.real_solution_is_rational`.

Most reference widths are linear combinations of $M$ and $X$, because their linear functionals have constant sign on the tag cone. The exceptional letter--identity pairing requires

$$
H_{a,j}=\sum_w a_j(w)\rho^{|w|}|a-st_w|,
\qquad a\in\{1,\ldots,s\}.
$$

The threshold $a/s$ has the constant repeating digit $a$ in base $s+1$. A different first digit fixes the sign; the same digit reproduces the absolute value at scale $1/q$. Thus $H_a$ satisfies a rational $m$-coordinate system with matrix $(\rho/q)P_a$. This accounts for every reference-pair width, including those of transition images.

The three-dimensional calculation uses a finite register of volume $V$, reference-projection areas $A_i$, and reference-pair widths $W_{ik}$. Adding reference segment $r_j$ with coefficient $u\geq0$ gives

$$
\begin{aligned}
V'&=V+uA_j,& A_i'&=A_i+uW_{ji},\\[-2pt]
W_{ik}'&=W_{ik}+u\,|\det(r_i,r_k,r_j)|.
\end{aligned}
\tag{3}
$$

Extrusion formulas justify these identities for actual compact convex bodies. The planar moments supply the initial register. Iteration gives `CanonicalArithmetic.formula`, defined over every rational algebra. Its equality with actual volume for nonnegative rational weights, followed by polynomial identity on nonnegative integer tuples, identifies the full canonical polynomial. No finite numerical experiment is used to infer this equality.

**Source guide.** `ReferenceMoments`, `ReferenceWidths`, `ReferenceRecursion`, `CanonicalArithmetic`, and `CanonicalVolume` form the arithmetic closure. `CanonicalVolume.canonicalPolynomialQ_eq` identifies the whole polynomial. Their compilation unit is `source/mixed_volume/general/geometry_arithmetic.lean`.

## One uniform program and the same quadratic map

A separate algorithm for every fixed $(s,m)$ would leave a uniformity gap. The dimension-uniform endpoint instead specifies one partial recursive program whose input contains $s,m$ and finite rational lists. It proves termination for every representation of every valid rational automaton. Behavior on invalid data need not be total.

Rational values have explicit surjective codes; lists, products, and nested lists are coded recursively. `Represented.Primitive` and `Represented.Effective` assert the existence of Mathlib primitive recursive or computable code programs *together with exact decoding equations*. This separates mathematical computability from whether Lean can evaluate a definition carrying the modifier `noncomputable`.

The moment program enumerates finite rational candidates $W=(M,X,Q,H)$ and checks their recurrence equations exactly. The predicate `UniformMoments.Correct` uses data-dependent finite ranges and rational arithmetic, with a uniform primitive-recursive verification theorem. `CertificateSearch.program` performs unbounded search through their codes. Existence follows from the rational resolvent solutions, so it terminates on valid data. Contraction proves uniqueness of all relevant entries, so every accepted candidate gives the same genuine moments. The search has no maximum state count, alphabet size, word length, or denominator.

The finite evaluator uses explicit label positions:

$$
\begin{array}{c|c}
\text{label}&\text{position, beginning at zero}\\\hline
\text{axis }i&i\\
\text{letter }a&3+a\\
\text{identity}&3+s\\
\text{state }j&s+4+j\\
\text{image }(a,j)&s+4+m+j+ma\\
\text{deficit}&s+4+m+sm
\end{array}
$$

`ExplicitLabels` proves that this is an equivalence with the abstract geometric labels. `UniformFormula.formula_eq` identifies the list evaluator with the same finite expression from Section 3, including its entire register recurrence. The equality holds at *all rational weights*; this matters because substitution (2) can produce signed weights.

Exact extraction substitutes $x_i=t^{5^i}$. A cubic monomial obtains exponent $e(\alpha)=\sum_i\alpha_i5^i$, with no collisions and $e(\alpha)<5^N$. Univariate Lagrange interpolation at $5^N$ rational nodes recovers every coefficient. The program emits $N$ and a dense rational list of length $5^N$; the ordinary coefficient $c_\alpha$ is the entry at $e(\alpha)$. This oversized output is intentional: it gives a simple uniform exact algorithm, without any efficiency claim.

For fixed rational $(P_a,f,\lambda)$, the expression is quadratic in the state-body weights, since those bodies lie in one plane. The substitution is affine in $(p,\theta)$, hence each coefficient is a rational polynomial of total degree at most two. This defines one polynomial map $\Psi$ on all of $\mathbb R^m\times\mathbb R$. `UniformQuadratic.program_matches_map` identifies the algorithm's decoded array with *this same map* at every rational $(p,\theta)$. Theorem 4.3 then gives

$$
\Psi(p,\theta)\in\mathcal V_{N,3}\quad\Longleftrightarrow\quad
\forall w\in\{0,\ldots,s-1\}^{*},\ pP_wf\leq\theta
$$

for all real probability rows and real $0<\theta<1$, including the empty-word inequality $pf\leq\theta$.

**Source guide.** `UniformMoments`, `UniformFormulaCorrectness`, `UniformInterpolation`, `UniformEncoding`, and `UniformQuadratic`; principal endpoint `MainResults.theorem_4_3`.

## The co-recursively enumerable upper bound

Hardness alone does not establish co-r.e. completeness. The upper bound needs an actual program that halts precisely on nonrealizable rational arrays. The local convex-geometric theory supplies a finite quadratic rejection characterization; the new computability layer proves that its tests and searches are Mathlib computable programs.

A rational scalar is represented by $(a,b,c)\in\mathbb N^3$ with value $(a-b)/(c+1)$. Every code has a value and every rational value has a code. For fixed $n,d$, a coefficient vector has one such entry for every ordinary degree-$d$ monomial. Its chosen finite ordering does not restrict the input domain; realizability depends only on decoded values.

The approximation chain retains the exact finite objects from the geometric proof. A list-based Fourier--Motzkin program eliminates rational inequalities. It handles arbitrary finite vertex lists, without a bound on their length or on the intermediate inequalities, and its output is proved to describe the literal convex hull. Empty and lower-dimensional hulls are included.

Finite grid-cell tests produce rational lower and upper bounds for the Lebesgue volume of a rational polytope in a known enclosing box. The bounds converge. Searching for a grid scale meeting a given positive rational tolerance therefore terminates. The development connects this mathematical termination argument to Mathlib's partial-recursive unbounded search, rather than treating a `Nat.find` expression as automatically computable.

Interpolation transfers these volume approximations to coefficient approximations. Rational hull enumeration and the proved geometric bounds give computable finite nets $N_k$ for the normalized bounded realization locus, with errors $e_k\to0$. In particular, `EffectiveNets.netList_effective` refers to the same nets whose covering and soundness properties occur in the geometric proof.

A certificate consists of a rational center $a$, positive rational radius $r$, and natural net scale $k$. The finite admission test is

$$
r>0,\qquad (r+e_k)^2<\sum_i(a_i-q_i)^2
\quad\text{for every }q\in N_k.
\tag{4}
$$

An admitted ball is disjoint from the normalized locus. For a coefficient vector $c$, put $\sigma=\sum_i c_i$ and define the homogeneous quadratic form

$$
Q_{a,r}(c)=\sum_i(c_i-\sigma a_i)^2-r^2\sigma^2.
$$

The rejection test checks for a negative coefficient, or an admitted certificate with $Q_{a,r}(c)<0$. All arithmetic comparisons are exact rational comparisons. The geometric compactness and separation argument proves both directions: no realizable array is rejected, and every nonrealizable array has a certificate. Enumerating certificate codes therefore semidecides the complement.

The endpoint `CoRE.realization_complement_re n d hd` has the hypothesis $d>0$ and allows every $n$. Its conclusion is Mathlib's `REPred` of the complement of the genuine realization predicate. Specializing to $d=3$ supplies the upper half of Theorem 1.1.

**Source guide.** The bridge consists of `EffectiveElimination`, `EliminationCorrectness`, `EffectiveGrids`, `GridCorrectness`, `RepresentedSearch`, `EffectiveNets`, and `CoRE`.

## Hardness, nonnegative inputs, and certificates

The source problem is the halting domain of Mathlib's universal partial-recursive evaluator at input zero: `MatrixMortality.Undecidability.CodeHalts`. The proof therefore reaches a standard formal model of universal computation. It does not assume an external assertion that a selected automaton problem is undecidable.

The local `MatrixMortality` library supplies the simulation chain through universal machines, tag-system encodings, word correspondence, and rational matrix representations. The seven-state automaton construction yields four letters, rational stochastic matrices, and a rational common stationary row. Its word acceptance condition has an exact equivalence with nonhalting of the source code. Applying the complete coefficient construction gives

$$
s=4,\quad m=7,\quad N=(4+1)\,7+4+5=44.
$$

`HaltingEncoding.emit` is accompanied by a primitive-recursive coding theorem and the semantic equivalence

$$
\operatorname{decode}(\operatorname{emit}(e))\in\mathcal V_{44,3}\quad\Longleftrightarrow\quad
\neg\operatorname{CodeHalts}(e).
\tag{5}
$$

Thus the geometric reduction is a computable many-one reduction, not merely a set-theoretic association of instances.

The restriction to nonnegative coefficients is implemented on the actual subtype of rational arrays with all entries nonnegative. If the emitted array contains a negative entry, it cannot be realizable. The algorithm then outputs the fixed nonnegative obstruction $x_1^3+x_2^3$, padded by zero coefficients. Its nonrealizability is proved: its two positive pure-volume terms are incompatible with the missing mixed terms. If no entry is negative, the original array is retained. This is a primitive-recursive branch and preserves (5). The restriction is not a new promise silently imposed on the unconstrained reduction.

Together with the upper bound, this proves co-r.e. completeness statement on both input domains. The formal definition requires that every co-r.e. predicate on natural numbers many-one reduce to the target. The universal halting reduction supplies this quantifier, and the same development rules out a computable membership predicate.

A sound and complete effective verifier for finite certificates of *realizability* would make realizability recursively enumerable: enumerate certificate codes and run the verifier. The nonhalting reduction excludes this. The endpoint spells out the forbidden verifier as

$$
\nexists\,\mathrm{verify}:\mathrm{ArrayCode}_{44,3}\times\mathbb N\to\mathrm{Prop}
\quad\text{computable, with}\quad
c\text{ realizable}\ \Longleftrightarrow\ \exists k\,\mathrm{verify}(c,k).
$$

This is consistent with Section 5: nonrealizability has effective certificates; realizability has no complete effective certificate system of this kind.

Point padding appends bodies equal to a point and coefficients with zero exponents on the new variables. Restricting any purported padded realization back to the original variables proves the converse. The computable padding map therefore transfers completeness, undecidability, and the certificate obstruction to every $n\geq44$ in dimension three.

**Source guide.** `Completeness`, `HaltingEncoding`, `EffectivePadding`, and `MainTheorems`; endpoints `MainResults.theorem_1_1` and `MainResults.theorem_1_1_all_n`.

## A fixed 28-state family on the whole simplex

Corollary 5.1 concerns the predicate $c\in\mathcal V_{91,3}$ for rational arrays $c$ promised to lie in $\Psi(\Delta_{27})$, where $\Psi$ is a fixed rational polynomial map of degree at most two on the probability simplex in $\mathbb R^{28}$. This makes explicit the meaning of the manuscript's phrase "rational membership of the image" indicated by its proof. Literal membership in the polynomial image is a different predicate: $\exists p\in\Delta_{27},\ c=\Psi(p)$. Its finite polynomial equations and inequalities admit Tarski's decision method.[^1] The formal predicate `FixedSection.OnImage` records this promise.

The paper invokes Rote's fixed binary automaton with cutpoint $1/28$. The present construction instead develops a fixed binary $28$-state automaton with cutpoint $1/2$ and a fixed rational accepting column in $(0,1)^{28}$. These are different supporting automata; the corollary's dimensions, domain, and decision problem are preserved.

The construction begins with one universal tag system. The varying source program affects only its initial queue; the deletion width and appendant remain fixed. The invariant forces every terminal queue to be exactly the one-letter queue $[b]$. The corresponding fixed four-pair word problem has equation

$$
U(w)M=H(q)M L(w).
$$

Here $U,L,M$ are fixed and the input occurs only in the left boundary $H(q)M$. A parsing proof covers *every* candidate tile word: a match forces complete deletion strokes and a genuine terminating tag execution. This avoids relying on an intended language of correctly encoded histories. It also avoids the short end-pair argument discussed and corrected by Rote in his Section 2.8.

Binary words are represented by base-four values using digits $1,2$ and scales $\operatorname{scale}(u)=4^{-|u|}$. The score

$$
S(u,v)=-\bigl(\operatorname{value}(u)-\operatorname{value}(v)\bigr)^2
+\operatorname{scale}(u)^2/32
$$

satisfies $S(u,v)>0\iff u=v$, with unequal lengths and the empty word included. A seven-dimensional rational matrix representation realizes this score. Uniform mixing makes the four transition matrices positive and doubly stochastic. The varying signed prefix row $v$, whose sum is zero, becomes a positive probability row through

$$
\tau=\frac{1}{1+\sum_i|v_i|},\qquad
p=(1/7,\ldots,1/7)+\tau v/14.
$$

A fixed accepting column incorporates the terminal boundary, and the acceptance value is $1/2+c\delta^{|w|}S(u_w,v_w)$ with $c,\delta>0$. All initial-row entries have exact primitive-recursive rational codes.

A four-block binary selector turns the four seven-state matrices into two $28$-state matrices. One letter applies the matrix selected by the current block; the other rotates the block. Every binary word projects to a source word, and every source word has a binary encoding. This proves the equivalence for all words, not just encoded ones. The two matrices remain doubly stochastic, so the common stationary row is uniform on $28$ states.

The geometric construction now gives $N=3\cdot28+7=91$ and a rational quadratic map $\Psi:\Delta_{27}\to\mathbb R^{129766}$ with

$$
\Psi(p)\in\mathcal V_{91,3}\quad\Longleftrightarrow\quad
\forall w,\ pP_wf\leq1/2
$$

for every real probability row $p$. The hard instances have rational rows. The coefficient-space formulation excludes even a *partial* recursive decider which may diverge away from the image but must halt correctly on every rational array in the image. A separate stronger intermediate restriction already excludes one on the image of rational parameter rows.

**Source guide.** `FixedTag`, `FixedCorrespondence`, `FixedPFA`, `BinarySelector`, `FixedSectionAll`, and `FixedCoefficientFamily`; endpoint `FixedSection.corollary_5_1_exists`.

## The twelve-body section and its boundary planes

The literal example from Section 6 of the paper has one letter and three states:

$$
P=\begin{pmatrix}5/8&1/8&1/4\\1/8&5/8&1/4\\1/4&1/4&1/2\end{pmatrix},
\qquad f=(1,0,0)^{\mathsf T},\qquad \lambda=(1/3,1/3,1/3).
$$

The vectors $\mathbf1$, $u=(1,-1,0)^{\mathsf T}$ and $v=(1,1,-2)^{\mathsf T}$ have eigenvalues $1,1/2,1/4$, and

$$
P^kf=\tfrac13\mathbf1+\tfrac12\,2^{-k}u
+\tfrac16\,4^{-k}v.
$$

For $a=(A,B,C)\in\mathbb R^3$, use the exact affine coordinates

$$
p=(1/3+C+B,\ 1/3+C-B,\ 1/3-2C),\qquad \theta=1/3-A.
$$

The Lean product-space ball $\Omega=B(0,1/12)$ lies in the region where every $p_i>0$ and $0<\theta<1$. The chosen norm is immaterial to the neighbourhood claim; this radius is a concrete sufficient bound. The full word condition is

$$
pP^kf\leq\theta\ \ (k\geq0)\quad\Longleftrightarrow\quad
a\in S:=\bigcap_{k\geq0}\{A+2^{-k}B+4^{-k}C\leq0\}.
$$

The literal quadratic coefficient map therefore satisfies the local set identity

$$
\Omega\cap\Psi^{-1}(\mathcal V_{12,3})=\Omega\cap S.
$$

`ThreeStateSection.theorem_6_1_literal_section` additionally states the degree bound, openness of $\Omega$, membership of zero, distinctness of the supporting planes, and all their local boundary patches.

To see the geometry behind those patches, put $t_k=2^{-k}$ and $H_k=\{A+t_kB+t_k^2C=0\}$. At

$$
q_k=\varepsilon(-t_k^2,2t_k,-1)
$$

the $j$th defining expression is $-\varepsilon(t_j-t_k)^2$. It is zero exactly at $j=k$; for all other $j$ its negative gap is bounded uniformly away from zero for this fixed $k$. A relatively open neighbourhood inside $H_k$ therefore remains on the boundary. Scaling $\varepsilon$ places that neighbourhood inside any prescribed positive-radius ball about zero. The formal statement quantifies over every $k$ and every such radius.

If the cone were semialgebraic, its boundary would be contained in the zero sets of finitely many nonzero defining polynomials. Their product would vanish on an open piece of every $H_k$, hence on each entire plane. Infinitely many distinct linear factors cannot divide a nonzero polynomial. Polynomial preimages preserve semialgebraicity, giving the obstruction for $\mathcal V_{12,3}$. This is a statement over the real numbers, independent of rational-input undecidability.

There are two deliberately distinguished witnesses in the project. The endpoint `ScalarSection.theorem_6_1` constructs a rational quadratic section equal to $S$ globally, proves all boundary patches, and proves nonsemialgebraicity. It establishes the paper's existential theorem. The literal branch, `ThreeStateSection.theorem_6_1_literal_section`, proves correspondence with the displayed matrix and coordinates above. The point-padding extension gives nonsemialgebraicity of $\mathcal V_{n,3}$ for all $n\geq12$.

**Source guide.** `DyadicCone`, `ScalarSection`, `All/Neighborhood`, `All/Padding`, and the new `General/ThreeStateExample` and `General/ThreeStateSection`.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.
