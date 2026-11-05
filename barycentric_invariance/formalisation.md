# Barycentric invariance and universal parameters for face rings

## What has been verified

This note describes the Lean 4 verification of Theorems 1.1--1.3 and 9.4 of Caius Folkerts' *Barycentric invariance and universal parameters for face rings*. The statements retain the coefficient rings and hypotheses described below.

| Result | Verified content |
|:--------------|:-|
| Theorem 1.1 | Verified in the pinned Lean/Mathlib environment, including the actual quotient rings, usual grading, specified weight filtration, coherence, relative kernels, and integral base change. |
| Theorem 1.2 | Verified for all commutative coefficients: actual derived Tor, finite stable filtrations, absolute and relative cohomology formulas, equivariance, both products, and the field Grothendieck-class identities. |
| Theorem 1.3 | Both directions of the uniform equivalence, including the unrestricted simplex obstruction and the original-ring positive endpoint. |
| Theorem 9.4 | All three assertions are verified: the exact factorial scalar ideal, the actual $H^1$ cyclic obstruction module, and the universal annihilator. |

The project pins Lean 4.35.0 and Mathlib commit

`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The checked roots include every supporting result used for these four theorems. The later exposition distinguishes the paper's statements from alternative proofs developed in Lean; it does not claim every further extension in the paper.

### The mathematical objects are the original ones

Let $P$ be a finite simplicial poset with minimum $0$. The formal predicate requires every interval $[0,F]$ to be a Boolean lattice. The vertices of a face are its actual atoms, not merely labels identifying faces with the same vertex set. This matters for simplicial posets which are not simplicial complexes.

Over an arbitrary commutative ring $K$, the original face ring is the quotient by the usual straightening relations, with $u_0=1$; the barycentric ring is the Stanley--Reisner quotient by incomparable pairs of nonzero faces. The names are `FaceRing` and `BarycentricRing`. For a rank bound $d$, the same polynomial ring $A_K=K[z_1,\ldots,z_d]$ acts by the literal rank sums

$$
z_i\longmapsto\theta_i=\sum_{\operatorname{rk}F=i}u_F,
\qquad
z_i\longmapsto\gamma_i=\sum_{\operatorname{rk}F=i}v_F.
$$

## The verified coherent comparison: Theorem 1.1

The verified package `TheoremOneComparison` is produced by `theorem_1_1`. Its source is `source/theorem12.lean` (the `PaperComparison` section). Its parameter equivalence is an equivalence of the actual quotient rings as modules over $A_K$. The displayed direction in the paper is available as `theoremOneParameterModuleEquiv`. An equivalence of coordinate spaces alone is not the final statement.

For a face $F$, write $V_F$ for its atoms and put

$$
R_F=K[x_v:v\in V_F],\qquad
B_F=K[\operatorname{Sd}[0,F]].
$$

Restrictions kill variables and face generators outside a smaller face. The constant stalk at $0$ is retained. Explicit standard-monomial coordinates prove

$$
R_K(P)\simeq\varprojlim_F R_F,
\qquad
B_K(P)\simeq\varprojlim_F B_F.
$$

These identifications are constructed from the original presentations; they are not definitions replacing those presentations. In Lean, `CoherentEquiv` contains actual stalk equivalences and all restriction squares. Its `sectionEquiv` is the induced inverse-limit equivalence.

The local source has an explicit free basis over its rank parameters, indexed by vertex orderings and descent data. The coefficient basis is the genuine chain-monomial basis. The proof develops the required straightening and triangularity arguments over $\mathbb Z$, instead of assuming freeness from a cited theorem. Boundary representatives and parameter linearity then extend compatible comparisons through the face ranks.

### The two gradings have distinct jobs

The ordinary degree of a rank-$i$ generator is $i$. The comparison and its inverse preserve the resulting usual quotient grading. Independently, the rank-weight filtration uses

$$
w_i=i(2d-i).
$$

For incomparable faces of ranks $a,b$, with meet rank $c$, every straightening term lowers the weight by

$$
w_a+w_b-w_c-w_{a+b-c}=2(a-c)(b-c)>0.
$$

The formal proof uses these exact weights. It identifies the filtration defined from weighted polynomial representatives with the filtration described in standard-basis coordinates. Thus the associated graded map is the prescribed chain-monomial comparison, rather than an arbitrary graded isomorphism chosen after the fact.

### Relative kernels and coefficient change

A lower ideal $Q$ determines an actual restriction map. The relative module is its kernel, equivalently the ideal spanned by standard monomials whose carrier is outside $Q$. Coherence proves preservation of every such kernel, and the checked development also identifies the conventional quotient presentation of a nonempty lower ideal.

Integral coefficient maps are specified on standard monomials. Actual tensor-product equivalences identify $K\otimes_{\mathbb Z}R_{\mathbb Z}(P)$ with $R_K(P)$, and similarly on the barycentric side. The base-change theorem asserts that the comparison commutes with these maps. Merely proving existence separately for each $K$ would be weaker than this statement.

## The Tor statement and its relative meaning

The formal statement of Theorem 1.2 retains arbitrary commutative coefficients, the action of a finite automorphism group $G$, both homological and internal degrees, and the specified rank weights. For each internal degree $j$, it gives a finite $G$-stable filtration with

$$
\operatorname{gr}\operatorname{Tor}^{A_K}_m(R_K(P),K)_j
\simeq
\bigoplus_{\substack{S\subseteq[d]\\\sum_{s\in S}s=j}}
\widetilde H^{\,|S|-m-1}\bigl((\operatorname{Sd}P)|_S;K\bigr).
$$

The right-hand groups are reduced *cohomology*, with their augmented degree $-1$ term. The shift $|S|-m-1$, and the sum of the actual ranks in the condition on $j$, are both essential.

The full check includes the relative formula and its nonunital product. Equivariance and multiplication are proved for the same comparison map; they are not merely existence assertions about unrelated isomorphisms.

### From the derived functor to an explicit complex

The coefficient ring $K$ is the $A_K$-module obtained by setting every $z_i$ to zero. The development connects the derived-functor Tor object to the actual Koszul complex for the universal parameters. Its degree-$m$ term has coordinates indexed by the $m$-element subsets $I\subseteq[d]$; its differential is the signed sum of multiplication by the corresponding rank parameters. This comparison is needed: defining an unrelated vector space and naming it "Tor" would not establish the theorem.

The filtration on a coordinate with exterior index $I$ is the coefficient rank weight plus $\sum_{i\in I}w_i$. Its internal degree is the coefficient degree plus $\sum_{i\in I}i$. The filtered parameter-module comparison of Theorem 1.1 gives lifts of associated graded cycles. Consequently the canonical map between associated graded homology and homology of the associated graded complex is an isomorphism. The associated graded complex is identified with the barycentric Koszul complex through the canonical coefficient comparison.

The barycentric complex is multigraded by rank colors. Nonsquarefree color components are contracted explicitly. A squarefree component with support $S$ is identified, with its signs and augmentation, with the cochains of the rank-selected order complex. This accounts for the displayed cohomological shift and the direct sum.

### The empty lower ideal is not silently changed

For a $G$-stable lower ideal $Q$, the left side uses the genuine kernel of restriction and the right side uses the corresponding relative augmented cochain complex. The empty lower ideal gives the void subcomplex and the whole relative face module. The lower ideal consisting only of $0$ gives a complex containing its empty face, and is different. The predicate `rankColoredSubcomplex` explicitly includes the condition $0\in Q$; this prevents an unintended empty face in the void case.

Over a field, the source assembly further uses the actual finite internal degree pieces and short exact sequences of $G$-modules to pass from the filtration to the identity in the representation Grothendieck group. Equality of dimensions alone would not suffice.

## Multiplication and the canonical associated graded map

The multiplication assertion in Theorem 1.2 needs more than the existence of a filtered module isomorphism. The comparison of Theorem 1.1 need not preserve multiplication. The source proof therefore treats multiplication in the actual Koszul differential graded algebra and proves compatibility for the canonical associated graded comparison.

For a commutative coefficient algebra $B$, the total Koszul algebra can be written either as

$$
B\otimes_K\bigwedge_K(K^d)
\quad\text{or as}\quad
\bigwedge_B(B^d).
$$

The development uses actual exterior algebras and identifies their homogeneous components with the subset-coordinate Koszul terms. On an ordered exterior monomial, the differential is

$$
d\bigl(b\,e_{i_1}\wedge\cdots\wedge e_{i_m}\bigr)
=\sum_{a=1}^{m}(-1)^{a-1}\theta_{i_a}b\,
e_{i_1}\wedge\cdots\widehat{e_{i_a}}\cdots\wedge e_{i_m}.
$$

The formula agrees with the previously defined coordinate differential. The exterior product supplies the shuffle signs; intersecting exterior supports give zero.

### Products are defined before comparison maps

Products on cycles and on their quotient by boundaries are obtained from the differential graded algebra. The source includes a map from each coordinate homology group into the total algebra homology and proves it injective by homogeneous projection. Products in coordinate homology are the products induced by these actual chain operations.

Coefficient multiplication and the exterior product preserve internal degree additively. They preserve the weight filtration additively as well. These are proved for the existing ordinary-degree and weight submodules, not for new gradings chosen to make the assertions hold. For every fixed lower ideal $Q$, the actual restriction ideal $I_Q$ also has a generally nonunital product. Its ideal-valued Koszul cycles multiply, and explicit ideal-valued primitives prove that boundaries form an ideal. Projecting these primitives to the required internal degree gives products on the genuine relative Tor groups; no injection into absolute homology is assumed. All three gradings add under these products.

On the associated graded coefficient rings, the chain-monomial map is multiplicative. Its lifts may have a product defect, but that defect is proved to lie in strictly smaller weight. The corresponding coordinate Koszul comparison therefore preserves the quotient product. At the homology level, bounded cycle representatives prove the commutative multiplication square for the canonical map

$$
\operatorname{gr}H(C)\longrightarrow H(\operatorname{gr}C).
$$

The product on the right is independently induced by the associated graded chain product. It is not defined by transporting a product across the desired isomorphism.

The chain comparison is `originalAssociatedBarycentricHomology_multiplicative`. The endpoints `theorem_1_2_multiplicative` and `theorem_1_2_relative_multiplicative` use independently defined barycentric cycle products followed by the colored cochain equivalence. Their explicit representative formulas identify multiplication with the actual exterior product. Equivariance and multiplication are two identities for the same displayed $K$-linear equivalence.

## The factorial-unit construction: Theorem 1.3

Put $D=(d-1)!$, where $d\geq1$. The positive statement requires coherent graded parameter-module comparisons for every simplicial poset of rank at most $d$, equivariant for every automorphism group, whenever $D$ is a unit in $K$. It does not assume that the automorphism group order is a unit.

The verified proof reduces the equivariant construction to one symmetric simplex template. If $d!$ is a unit, an integral nonequivariant coherent family can be summed over all vertex permutations and then normalized. If $D$ is a unit but $d!$ is not, $d$ is prime: for composite $d$, write $d=ab$ with $1<a,b<d$; both $a$ and $b$ divide $D$, hence are units. Thus only prime top rank needs a different construction.

### The integral prime template

Let $p$ be prime and let $C_p$ act on its $p$ vertices by translation. Every nonempty proper face has a free $C_p$-orbit. Choose an ordinary graded boundary lift on one face of each orbit and transport it around the orbit. At the top face, the proof develops an integral equivariant lifting argument rather than dividing by $p$.

The polynomial monomials of degree $n$ have exponent vectors $a:C_p\to\mathbb N$ with $\sum a=n$. A nonidentity translation can fix such a vector only when it is constant. If $p\nmid n$, all orbits are free. If $p\mid n$, there is one constant vector $\delta$; the augmentation kernel has the difference basis $x^a-x^\delta$ for $a\ne\delta$, again freely permuted. Over $\mathbb F_p$, the compressed diagonal retraction has exactly these degreewise kernels. Their explicit coinduced descriptions supply the relative extension step. Integral correction of the remaining averaging defect gives a coherent normalized $C_p$-equivariant family over $\mathbb Z$.

Summing this family over $\mathfrak S_p/C_p$ preserves coherence, parameter linearity, and degree, and changes the constant scalar to

$$
[\mathfrak S_p:C_p]=(p-1)!.
$$

This relative trace uses no division. Base change to $K$ and multiplication by the inverse of $D$ give the normalized full symmetric template.

### From one simplex to arbitrary simplicial posets

Embed the actual finite vertex set of each face into the template's vertex set. Two such embeddings differ by an ambient permutation; full symmetry proves that the transported map is independent of the embedding. Template coherence then proves naturality under every vertex inclusion. This yields an actual coherent family on $P$, equivariant under every order automorphism of $P$.

Bijectivity is proved separately by face-rank induction. Proper-face restrictions have kernels exactly the multiples of the top parameter on both sides. A graded lift of an actual boundary isomorphism is bijective by induction on ordinary degree. At rank zero, a normalized linear map is the unique map of constant stalks. No previously invertible full-face map, leading-term condition, or circular isomorphism hypothesis is used. The verified endpoint is `theorem_1_3_positive_original`. The literal uniform equivalence is `theorem_1_3_uniform_iff`.

## The unrestricted nonunit obstruction

The negative direction has a different proof from the paper's projectivity argument. It proves the same application needed for Theorem 1.3 directly on the actual polynomial and barycentric rings. In particular, the hypothetical isomorphism is not required to preserve grading, restrictions, constants, or multiplication.

Suppose $D=(d-1)!$ is not a unit in a commutative ring $K$. Some prime $p<d$ is a nonunit. A maximal ideal containing $p$ gives a residue field $k$ of characteristic $p$. Put $r=d-p>0$, and let a $p$-cycle move the first $p$ vertices while fixing the remaining $r$. Evaluate the moved variables at $1$, and the fixed variables at independent indeterminates $b_1,\ldots,b_r$ over $k$. The elementary symmetric parameter values are the coefficients of

$$
(1+T^p)\prod_{i=1}^{r}(1+b_iT).
$$

Equivalently, the coefficient in rank $n$ is

$$
c_n=e_n(b_1,\ldots,b_r)
+\begin{cases}e_{n-p}(b_1,\ldots,b_r),&n\geq p,\\0,&n<p.\end{cases}
$$

Explicit squarefree-monomial coefficients prove that the positive active ranks are exactly $S=[1,r]\cup[p,p+r]$. Distinct ordinary degrees prevent cancellation. Every successive gap from $0$ through these ranks to $d$ is less than $p$.

### Why the relevant flags have free orbits

An active flag is an actual nested collection of vertex subsets having the ranks in $S$. If a nonidentity cycle fixed it, each successive difference would be a union of cycle orbits. Its cardinality is less than $p$, so it could contain no moved vertex. The top face is the full vertex set, a contradiction. This is the checked prime-cycle flag lemma. The checked proof connects it to the actual flag indexing set in the barycentric monomial expansion.

Suppose $f:R\simeq_K B$ were an equivariant parameter-module isomorphism. Let $v=f(1)$ and let

$$
\ell:B\longrightarrow k[b_1,\ldots,b_r],\qquad
\ell=\operatorname{ev}\circ f^{-1}.
$$

Then $v$ is fixed, $\ell(v)=1$, and $\ell(\gamma_i x)=c_i\ell(x)$. The product of all active color sums in the actual barycentric ring is the sum of the corresponding flag monomials $m_\mathcal F$. Consequently

$$
\prod_{i\in S}c_i
=\ell\!\left(\prod_{i\in S}\gamma_i\,v\right)
=\sum_{\mathcal F}\ell(m_\mathcal Fv)=0.
$$

The last equality groups terms into free orbits of size $p$; equivariance makes the summand constant on each orbit. The left side is nonzero in the polynomial domain $k[b_1,\ldots,b_r]$, giving the contradiction.

This avoids assuming that an invariant direct summand is nonprojective, or that a specialized ring is a free group representation. The result is `factorial_nonunit_no_simplex_comparison`, with the equivalent parameter-equivalence formulation `factorial_nonunit_no_equivariant_parameterEquiv`. Both are included in the successful full Theorem 1.3 check.

## The exact scalar obstruction: Theorem 9.4

Immediately after Theorem 1.3, the paper announces a stronger integral claim, proved as Theorem 9.4. If $E_K$ is the module of coherent graded parameter-linear maps on the rank-$d$ simplex and $\epsilon$ records the constant scalar, it asserts

$$
\epsilon(E_K^{\mathfrak S_d})=(d-1)!K.
$$

The maps have the paper's direction $R_K\longrightarrow B_K$. Their generator-intertwining condition is genuine polynomial-parameter linearity, by `isParameterLinear_iff_X`. For a nonunit scalar they need not be invertible, so reversing that direction would be a substantive alteration. The theorem also identifies the cyclic comparison-obstruction module with $K/(d-1)!K$, and gives a universal annihilator statement for arbitrary face posets and actions. The unit/nonunit criterion alone cannot recover factorial multiplicities. The formalization proves the necessary inclusion separately, over every commutative coefficient ring.

### A trace-one identity in the actual parameter fiber

Compose an invariant parameter-linear map $R\to B$ with the quotient evaluation sending the top face variable to $1$ and all proper face variables to $0$. The resulting functional $\ell:R\to K$ satisfies $\ell(1)=C$ and descends to the literal quotient $K[x_1,\ldots,x_r]/(e_1,\ldots,e_{r-1},e_r-1)$. Its negative coordinate roots satisfy $\prod_i(T-\xi_i)=T^r+1$. When $r$ is a unit, differentiation at each root shows that every pairwise root difference is a unit. Thus the Vandermonde determinant $\Delta$ is a unit, and its alternating expansion gives

$$
a=\frac{\xi_2\xi_3^2\cdots\xi_r^{r-1}}{\Delta},
\qquad \sum_{\sigma\in\mathfrak S_r}\sigma(a)=1,
\qquad \ell(1)=r!\ell(a).
$$

The determinant and quotient calculations are checked in `source/theorem94.lean` (the `ScalarVandermondeTrace` section) and `source/theorem94.lean` (the `ScalarPowerFiber` section), including the derivative and unit identities. No unproved splitting-algebra or Chinese-remainder assertion is used.

Apply this divisibility at rank $d$ after inverting $d$, and at rank $d-1$ after inverting $d-1$. With $D=(d-1)!$, the checked localization argument gives powers $d^aC\in DK$ and $(d-1)^bC\in DK$. Those powers are coprime, so Bezout gives $C\in DK$. This argument allows nilpotents and zero divisors. Functionals are extended on the actual polynomial monomial basis; no assertion that invariants commute with base change is needed. The final theorem `ScalarFamilies.scalar_factorial_dvd` extracts both rank functionals from the actual coherent simplex family with its literal permutation action.

### The obstruction is actual first group cohomology

Let $E_K^0=\ker\epsilon$. A normalized ordinary comparison $\Phi$ from Theorem 1.1 gives the cocycle $g\mapsto g\Phi-\Phi$ in $E_K^0$. The checked class $o_P$ belongs to Mathlib's actual $H^1(G,E_K^0)$. It is independent of $\Phi$, and the development proves

$$
\operatorname{ann}_K(o_P)=\epsilon(E_K^G),\qquad
K/\epsilon(E_K^G)\simeq K o_P.
$$

These are `comparisonObstruction_annihilator` and `comparisonObstructionSpanEquiv`. On the rank-$d$ simplex with its full symmetric action, necessity and sufficiency give exactly $DK$. For arbitrary bounded-rank $P$, the construction proves $DK\subseteq\operatorname{ann}_K(o_P)$.

## Integral prime-orbit data and scalar sufficiency

The exact scalar ideal requires normalized integral families for free cyclic $p$-groups. For each maximal prime power $q=p^a\mid d$, coset trace gives scalar $d!/q$; integer Bezout gives $D=(d-1)!$. Traces preserve the actual $R\to B$ restriction squares.

### The verified integral moment retraction

On one prime orbit, index vertices by $\mathbb F_p$. For an exponent vector $a$, put $|a|=\sum_t a_t$. If $p\mid|a|$, set $m=|a|/p$ and

$$
M(a)=\sum_{t\in\mathbb F_p}t\,(a_t-m),\qquad
w(s)=\mathbf1_{s=0}-\mathbf1_{s=1}.
$$

Here $M(a)\in\mathbb F_p$ and $w$ is integer-valued. Send $x^a$ to $w(M(a))y^m$ if $p\mid|a|$, and to zero otherwise; thus $(\prod_t x_t)^m\mapsto y^m$. For $0<i<p$, translating the $i$-element subsets by $i^{-1}$ pairs the moment sums, killing multiplication by $e_i$ integrally, without dividing in $K$.

For $V=\mathbb F_p\times W$, multiply the orbit formulas to obtain $E:R_V\to R_W$. The parameter identity is

$$
E(e_i f)=
\begin{cases}
e_{i/p}\,E(f),&p\mid i,\\
0,&p\nmid i.
\end{cases}
$$

Over every commutative ring, $E$ preserves constants, divides degree by $p$, commutes with restriction to full orbits, and intertwines orbit permutations and translations; see `source/theorem94.lean` (the `CyclicMomentWeights` section) through `source/theorem94.lean` (the `CyclicOrbitMomentDegree` section).

### The coherent prime-power construction

The actual barycentric quotient $\pi:B_V\to B_W$ kills nonfixed face variables and sends $\mathbb F_p\times F$ to $F$. Its kernel basis consists of chains containing a nonfixed face. Every nontrivial cyclic $p$-subgroup contains the order-$p$ subgroup, while a chain stabilizer fixes each face by rank. The homogeneous kernel bases have free orbits, hence give coinduced modules. Relative injectivity applies to $K$-split sequences, with actual coefficient projections onto homogeneous fixed-face and simultaneous boundary kernels supplying the retractions. Unrestricted injectivity over $K[G]$ is not assumed.

Induct on the group order. The quotient by its order-$p$ subgroup acts freely on the orbit set, giving a normalized comparison $\psi$ there. Construct components by face rank, retaining $\pi\Phi=\psi E$ on stable faces. The restriction identities give boundary compatibility. The combined boundary--$\pi$ kernel is the top variable times $\ker\pi$, so corrections preserve both prescriptions. Nonstable faces have trivial stabilizers. Degree induction gives bijectivity; the empty face is handled separately. The endpoint is `exists_cyclicPrimePower_comparisonFamily`.

Tracing, combining scalars, and transporting to bounded-rank posets give `theorem_9_4_scalarIdeal`, `theorem_9_4_obstructionModule`, and `theorem_9_4_universalAnnihilator` in `ScalarFamilies`.

This proves Theorem 9.4 without assuming Theorem 9.1's stronger induced-cyclic-order naturality, which is not claimed here. Further extensions of the paper are outside these principal-theorem files; no unproved appendix result is admitted as an axiom.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.
