# Sublattice resolutions and Betti preservation in all powers

The development starts with monomial ideals indexed by a finite sublattice and obtains formulas for their powers from predecessor colons. The same constructions control multiplicative Tor, transfer Betti numbers from initial ideals, and retain integral torsion and arbitrary coefficient change. This note explains those constructions and their connection to the paper’s objects. Theorem numbers refer to `paper.pdf`; principal declaration names use `FourPapers.Sublattice` unless otherwise indicated.

The main statements include all positive powers, literal mixed products, actual derived Tor, and genuine free resolutions. Their hypotheses remain explicit: first-power Betti equality is required for the corresponding transfer conclusion, substitution preserves minimality for minimal multigraded source resolutions, and the finite quotient-depth formula requires a positive row count. The proof uses direct Rees-homology generation in place of the standalone Proposition 2.5, an ordered leading-coordinate filtration in place of Lemma 3.3, and direct graph-family cycle lifts in place of Lemma 9.2. The Hasse-derivative comparison of Lemma 4.2 is proved for the sublattice initial ideals needed in the argument.

## The mathematical objects

Fix row sizes $n_1,\ldots,n_d$ and a finite nonempty sublattice $E\subseteq\prod_{r=1}^d[n_r]$, with coordinatewise meet and join. Let $N=\sum_{r=1}^d n_r$ be the number of variables. Set

$$
S=k[x_{r,j}],\qquad u_a=\prod_{r=1}^{d}x_{r,a_r},\qquad
 I_E=(u_a:a\in E).
$$

The Lean type `FiniteTuple` $n$ is the finite product of the row index sets. `FiniteVariable` $n$ is their disjoint union; its universe lift changes no variables, as the explicit equivalence `finiteVariableEquiv` proves. The definitions use zero-based finite indices. Adding one recovers the row-interval notation $[n_r]$ above; the ternary coordinates in Section 10 use $0,1,2$ directly.

The ideal `finiteSublatticeIdeal` $n\ E$ is literally the ideal spanned by these products in `MvPolynomial`. Exponent families provide finite coordinates for calculation. Their relation to actual ideals is proved: `finitePowerFamily_ideal` identifies the family used for the $m$th power with the ordinary ideal power $I_E^m$. Similarly, `finiteChainCoefficientFamily_ideal` identifies the coefficient ideal of a chain with the sum of the actual predecessor colons. These identifications prevent a convenient combinatorial model from replacing the objects in the theorem without justification.

**Tor and gradings.** The Betti numbers are dimensions of homogeneous submodules of Mathlib’s derived tensor functor $\operatorname{Tor}^S_p(M,k)$, with the variables acting by zero on $k$. The project constructs the polynomial Koszul resolution and proves the comparison with this derived functor. Homogeneous inclusions have proved retractions, so the degree pieces really embed in Tor. Finiteness is established before dimensions are used to detect vanishing.

Fine degrees range over $\mathbb Z^{\{(r,j)\}}$, and ordinary internal degrees range over $\mathbb Z$. A fine piece with any negative coordinate vanishes; an ordinary piece of negative degree also vanishes. These are consequences of the actual grading, not conventions imposed on a Betti function. The natural-degree intermediate formulas include the required componentwise shift bounds; the integer-degree endpoints use ordinary subtraction and retain every multichain. Homological degrees are nonnegative, with the usual vanishing in negative homological degrees implicit in the chain-complex convention.

## The chain formula and first-power transfer

For $a\in E$, let $C_a=(u_b:b<_{\mathrm{lex}}a):u_a$. For a multichain $w=(a_1\leq\cdots\leq a_m)$, write

$$
C_w=\sum_{s=1}^{m}C_{a_s},\qquad
 \sigma(w)=\sum_{s=1}^{m}\deg u_{a_s}.
$$

Repetitions are allowed. The combined declaration `theorem12` states both assertions of *Theorem 1.2, p. 3*:

$$
\beta^S_{p,\alpha}(I_E^m)
   =\sum_{w}\beta^S_{p,\alpha-\sigma(w)}(S/C_w),\qquad m\geq1,
$$

and generation of the actual Rees Koszul homology algebra by its Rees-degree-one classes and the unit. The generation assertion concerns multiplication of actual homology classes; it is not inferred from a dimension formula.

The paper’s dependency chain in Section 2 is formalised in four steps. Predecessor ratios reduce to coordinatewise predecessors by taking a meet. A monic presentation of the Rees algebra gives a unique standard form indexed by multichains and residual monomials. In Rees degree one, the fine filtration is minimal. Finally, the generators of $C_w$ separate into disjoint crossing blocks, each already occurring at one member of $w$. The resulting tensor products of Koszul complexes produce the required products of first-degree classes.

**Multiplicative propagation.** `proposition31` retains an arbitrary bigraded algebra over the polynomial ring, finite-dimensional homogeneous components, and a homogeneous multiplicative filtration that is exhaustive and separated. Its associated algebra is the literal associated graded construction. The two comparison hypotheses are exactly the first-auxiliary-degree Betti equality and generation of the associated Koszul homology in auxiliary degree one. No cycle-lifting hypothesis is added. The proof constructs leading-cycle lifts from equality of finite homology dimensions. Products supply lifts in all auxiliary degrees; finite weight descent proves the generation conclusion. Projection to each homogeneous component gives equality in every individual Tor degree. This supplies the paper’s degeneration argument through explicit filtered linear algebra.

**Symbolic powers.** For *Theorem 4.1, p. 9*, the formalisation constructs the finite network associated to the join-irreducibles of $E$. Integer cut packing identifies ordinary powers with the intersection of powers of the minimal monomial primes. The symbolic-power definitions use localization and contraction; equality with the monomial-cover formula is proved. The Hasse-derivative comparison from *Lemma 4.2, p. 11* is proved in every characteristic for sublattice initial ideals, the case used below. Its general standalone form is not asserted.

`theorem43` then proves, for a homogeneous ideal $J$ with $\operatorname{in}(J)=I_E$ and every $m\geq1$, the unconditional identities

$$
J^{(m)}=J^m,\qquad \operatorname{in}(J^m)=I_E^m.
$$

Under the paper’s first-power Betti equality it also proves all-power Betti equality and Rees-homology generation. The integer and finer-graded endpoints preserve every compatible grading refining ordinary degree. Thus the numerical comparison remains conditional exactly where the paper makes it conditional; the ideal identities do not acquire that extra hypothesis. The application to a general term order works directly with its well-ordered leading-coordinate filtration. This alternate proof avoids the global integer-weight construction of Lemma 3.3; the standalone existence assertion of that auxiliary lemma is not needed in the formal dependency chain.

## Finite formulas, mixed powers, and substitution

**Strict supports and polynomial behaviour.** In *Corollaries 5.1–5.2, p. 12*, a strict support of length $r$ occurs in a length-$m$ multichain in $\binom{m-1}{r-1}$ ways. The formalisation proves this counting identity and groups the chain formula by these supports. Its coefficients are the actual quotient Betti numbers. In particular, for every integer normalised degree $q$,

$$
\beta_{p,dm+q}(I_E^m)
   =\sum_{r=1}^{|E|}c_{p,q,r}\binom{m-1}{r-1},
 \qquad c_{p,q,r}\in\mathbb N.
$$

The project proves equality with the corresponding rational polynomial, the generating-series identity, and nonnegativity of every forward difference. Projective dimension and depth mean the genuine categorical projective dimension and the Ext-defined depth at the homogeneous maximal ideal. They are related to Tor by proved resolution and duality arguments before their monotonicity is deduced.

*Corollary 5.3, p. 13* includes the bound on the first occurrence of a nonzero strand and the injection induced by multiplication by the minimum generator. The latter is a statement about the actual induced map on Tor. It is proved by an explicit chain retraction and a comparison with the polynomial multiplication map, including normalisation of the chosen generator’s scalar.

**Coloured families.** For $I_1,\ldots,I_r$, the auxiliary ideal $\sum_c z_cI_c$ converts compatible coloured sublattices to one ordinary sublattice. In Rees degree $|\mathbf m|$ and colour degree $\mathbf m$, there are no exterior $z$-terms: such a term would require a coefficient of colour degree smaller than its Rees degree. The checked diagonal comparison therefore recovers the Koszul complex of the literal product $\prod_cI_c^{m_c}$. Same-colour predecessor ideals give the coefficient quotients in the mixed formula. All exponent vectors, including zero, are retained.

For transfer to ideals $J_c$, Theorem 5.5 assumes one order giving the stated initial identity for every mixed product, and the separate first-power Betti equalities. Corollaries 5.6–5.7 provide finite and nested criteria for these identities. The conclusions include the mixed Betti formula and unit-colour generation. Grouping strict supports gives the polynomial statement for normalised ordinary Betti entries; the fine-degree formula retains the individual multichain shifts. Primary components coming from absent colours are retained when needed, and unit components are removed before asserting primaryness. The prefix applications include graph prefixes, determinantal prefixes, and principal lattice prefixes. Corollary 7.2 later gives the same mixed decomposition over every commutative coefficient ring, with torsion retained.

**Positive homogeneous regular sequences.** For *Corollary 5.8, pp. 17–18*, the map $S\to R$ sending $x_{r,j}$ to $f_{r,j}$ is proved free from the regular-sequence hypothesis. Scalar extension uses the literal tensor carrier $R\otimes_S M$, proved to agree with Mathlib’s standard functor. Base change preserves the resolutions of the actual ideal powers; positivity keeps minimal differential entries in the homogeneous maximal ideal. The matrix entries, augmentation, and fine shifts are explicitly regraded by $\deg x_{r,j}=\deg f_{r,j}$. The multiplicative comparison uses the actual Koszul homology rings, identified with Tor by the checked Koszul resolution. Separate lemmas prove compatibility with Rees-degree projections, yielding degree-one generation and propagation. Pairwise disjoint positive monomial substitutions are included with their regularity proved.

The construction splits the actual fine Koszul strands over the coefficient field, then transfers the polynomial diagonal resolution. Contractions outside a finite box bound the surviving basis, and differential entries lie in the variable ideal. `corollary58_powerFreeResolution` gives a finite minimal resolution of every substituted power; base change also preserves any given minimal multigraded source resolution. The resolution statements allow arbitrary target variable types. The multiplicative and propagation statements use finitely many target indeterminates, as in the manuscript.

## Closed graphs, higher minors, and integral complexes

**Closed graphs.** `theorem11_integer_bettiEquality` compares the actual powers of

$$
J_G=(x_i y_j-x_j y_i:\{i,j\}\in E(G),\ i<j),\qquad
 I_G=(x_i y_j:\{i,j\}\in E(G),\ i<j)
$$

over every field, for every positive power and every integer internal degree. The input is the original closed labelling. Connectedness, nonempty edge set, and an interval labelling are not additional hypotheses. The proof groups connected components into consecutive blocks while preserving the order within each component, transports both actual ideals by the same variable permutation, and proves that the induced Koszul comparison preserves ordinary degree and exterior signs.

The first-power equality used in the paper from Peeva’s theorem is proved in the project by explicit parameter-family cycle lifts and filtered homology comparison. The all-power result then follows from Theorem 4.3. This keeps the graph proof independent of the later integral all-power construction. Corollaries 6.2–6.4 add preservation in the natural vertex grading and the component-row grading, field independence, and the linear-strand formula for arbitrary closed graphs.

**Unit interval determinant ideals.** Lemma 6.1 decomposes each predecessor ideal into its linear part and a residual variable restriction of the original unit interval ideal, with the two parts supported on disjoint variables. The finite cutoff is proved equal to the first qualifying maximal interval clique (`facetCutoff_eq_first_maximalInterval`). The recursion is proved in the retained smaller polynomial ring, including the indicated variable restrictions. The ambient generating-family presentation is identified with this smaller-ring ideal by `retainedGeneratorFamily_ideal`. It supplies field independence and the support congruence in every monomial power. For at least three rows, this congruence excludes adjacent homological degrees at the same internal degree. Theorem 4.3 supplies the all-power initial identities; the filtered no-cancellation argument then proves the Betti comparison directly in each power.

The determinant generators, their diagonal leading terms, the Laplace relations, and the requisite Gröbner basis are proved in Lean. The diagonal-initial-ideal theorem cited from the literature is therefore not an unverified import. The row convention in the source is $d+1$; its hypothesis $2\leq d$ is exactly the paper’s “at least three rows.” The two-row case uses the separately established graph comparison.

**The integral strengthening.** Write $S_{\mathbb Z}=\mathbb Z[x_{r,j}]$. *Theorem 7.1, p. 24* gives a chain homotopy equivalence over $\mathbb Z$, in every integer fine degree,

$$
K_{S_{\mathbb Z}}(I_E^m)_\alpha\simeq
 \bigoplus_wK_{S_{\mathbb Z}}(S_{\mathbb Z}/C_w)_{\alpha-\sigma(w)}.
$$

Its parameter-family version is also formalised for every signed weight with the stated initial ideal. The source constructs actual chain maps, their compatibility with the differential, and homotopies. It does not replace an integral complex by its ranks over fields. Acyclic free kernels are contracted, first-power block maps are lifted, and their products give the full comparison. Consequently the homotopies survive arbitrary coefficient base change. The endpoint for Tor covers every commutative coefficient ring, including the zero ring, and Corollary 7.2 performs the same construction on the mixed diagonal.

## Cellular resolutions, families, and torsion

**The cellular complex.** In *Theorem 8.1, p. 27*, let $P$ be the join-irreducible poset of $E$, and put $h=|P|$. Integer order-reversing maps $P\to\{0,\ldots,m\}$ index the minimal generators of $I_E^m$. The affine braid triangulation of the dilated order polytope supplies the faces and their least-common-multiple labels. The differential uses the oriented face signs and the quotient of the two labels. The augmentation has the actual ideal power as its target.

The project proves exactness of the divisor strands, finite freeness, length at most $h$, and compatibility of every term, differential, and augmentation with arbitrary coefficient change. A maximal lattice chain attains the projective-dimension bound. The special fibre is identified with the corresponding Hibi algebra, giving analytic spread $h+1$. With $M=\max\{1,h\}$, the normalised integer Betti support is nondecreasing and stabilises for $m\geq M$, and

$$
\operatorname{pd}(I_E^m)=h,\qquad \operatorname{reg}(I_E^m)=dm+c_{E,k}\qquad(m\geq M).
$$

For $d\geq1$, the Ext-defined quotient depth is $N-h-1$. The zero-row convention is handled separately: then $I_E=S$ and $S/I_E=0$, whose depth is infinite. The source proves this counterexample to an unrestricted finite-depth formula. The accompanying manuscript makes the positive-row condition explicit. Its substitution statement likewise specifies *minimal multigraded* source resolutions; see the worked example below.

**A universal graph resolution.** Put $R_0=\mathbb Z[z]$ and $S_0=R_0[x_1,\ldots,x_n,y_1,\ldots,y_n]$. *Theorem 9.1, p. 29* concerns the literal ideal $\mathcal J=(x_i y_j-z^{j-i}x_j y_i)$ in $S_0$, with the interval labelling specified in that section. The constructed resolution of $\mathcal J^m$ has finite free $S_0$-terms, common index sets, and common shifts. For every commutative $R_0$-algebra $A$, its matrices specialise coefficientwise to an exact free $A[x,y]$-resolution of the literal specialised ideal power. Flatness of $A$ over $R_0$ is not assumed. At $z=0$ and $z=1$, the augmentation ideals are proved equal to the displayed monomial and binomial powers. Over fields, the differential entries remain in the homogeneous maximal ideal, giving minimal resolutions with the same ranks and shifts. The formal proof constructs this graph family’s cycle lifts and contraction directly. It therefore does not require the general integral-transfer lemma stated as Lemma 9.2; that auxiliary statement is not separately formalised.

**Characteristic dependence.** Section 10 connects an incidence ideal’s squarefree Koszul strand to augmented simplicial homology by an integral, oriented nerve calculation and Alexander duality. Before duality, the strand is a reversed augmented *cochain* complex; retaining this reversal places integral torsion in the correct homological degree. The formalisation also keeps the low-degree vanishing. Proposition 10.2 constructs the stated 1087-element sublattice in $\{0,1,2\}^{30}$ and verifies the integral torsion computation. Let $\alpha_m$ be the multidegree of $\prod_{e=1}^{30}x_{e,0}x_{e,1}x_{e,2}^{m}$. For every $m\geq1$, integral Tor in this fine degree is $\mathbb Z/2$ in homological degree $13$ and zero elsewhere. Over a field of characteristic two, the fine Betti entries in homological degrees $13$ and $14$ are both one; they vanish in every other characteristic. At the first power, squarefree support shows that ordinary degree $90$ isolates precisely this fine component. Corollary 10.3 realises the homology of every finite complex on a nonempty vertex set with no cone vertices, exactly as in the paper, in the actual fine Tor of every positive power.

For Corollary 10.4, comparison of the actual integer boundary matrices and the kernel/image dimension identity prove that each characteristic excess is nonnegative before any natural-number subtraction is used. Grouping by strict supports gives the positive binomial expansion and its forward differences. Constant chains force first-power coefficient independence, while the crossing blocks propagate it. The final statement quantifies over all fields and proves that independence for some positive power is equivalent to independence for every positive power.

## A worked example: the formula and its multiplication

Over a field $k$, take one row with two columns, write its variables as $x,y$, and let $E=\{0<1\}$. Then $I_E=(x,y)\subseteq S=k[x,y]$. The predecessor colons are

$$
C_0=0,\qquad C_1=(x):y=(x).
$$

A length-$m$ multichain consists of $m-r$ zeros followed by $r$ ones, for a unique $0\leq r\leq m$. Its generator is $x^{m-r}y^r$. The chain with $r=0$ has coefficient quotient $S$; each of the other $m$ chains has coefficient quotient $S/(x)$. Theorem 1.2 therefore gives

$$
\beta_{p,j}(I_E^m)=
 \begin{cases}
  m+1,&p=0,\ j=m,\\
  m,&p=1,\ j=m+1,\\
  0,&\text{otherwise},
 \end{cases}
 \qquad m\geq1.
$$

This is the Betti table of the minimal free resolution

$$
0\longrightarrow S(-m-1)^m\longrightarrow
 S(-m)^{m+1}\longrightarrow I_E^m\longrightarrow0.
$$

With generators $g_r=x^{m-r}y^r$, its adjacent relations are $yg_r-xg_{r+1}=0$. Thus the differential has actual entries $y$ and $-x$, and the augmentation sends the $r$th basis vector to $g_r$.

**Why the source must be minimal.** The formal counterexample adds the contractible pair $T(-1)\xrightarrow{1}T(-1)$ to the resolution of $(x)$ over $T=\mathbb Q[x]$. Identity substitution preserves exactness and the unit differential, so the resulting graded free resolution is still nonminimal.

**Where the binomial coefficients appear.** There are two singleton strict supports and one support of length two. Their contributions give

$$
m+1=2\binom{m-1}{0}+\binom{m-1}{1},\qquad
 m=\binom{m-1}{0}+\binom{m-1}{1}.
$$

These are the coefficients of Corollary 5.2 in this example. They come from the coefficient quotients, before the length-$m$ chains are counted. The nonnegative coefficients explain monotonicity directly. Here $h=1$: the projective dimension is already $1$ in the first power, regularity is $m$, quotient depth is $0$, and analytic spread is $2$.

**What generation of homology means.** In the Rees algebra $S[I_Et]$, let $u=xt$ and $v=yt$. Their classes generate homological degree zero. Let $e_x,e_y$ be the exterior Koszul generators. The element

$$
z=(xe_y-ye_x)t
$$

is an actual cycle, since its differential is $(xy-yx)t=0$. It has homological degree $1$, Rees degree $1$, and internal degree $2$. The $m$ products

$$
u^{m-1-r}v^r z,\qquad 0\leq r<m,
$$

give the degree-$m$ homological basis. Their coefficient vectors are independent, and there are no boundaries in internal degree $m+1$: boundaries there would require coefficients in $(I_E^m)_{m-1}=0$. Together with the vanishing just computed, this identifies the whole homology algebra with $k[u,v]\otimes_k\Lambda_k(z)$, with the three gradings above. The product assertion thus supplies concrete classes and their multiplication, beyond the numerical identity for the table.

## Source organisation

The aggregate mathematical module is `source/sublattice_verification.lean`. The modules under `source/graph_foundation/` and `source/shared_results/` provide the polynomial, Koszul, filtration, and homological constructions. The principal applications are organised under `source/graph_results/`, `source/unit_interval_results/`, `source/mixed_results/`, `source/paper_results/`, and `source/resolution_existence/`. Filenames and imports use lowercase names; the original mathematical declaration namespaces are retained.

The default build also compiles `source/sublattice_audit.lean` and `source/verification/check_1.lean`. The strict audit records the selected endpoints’ complete kernel types and checks their exact reconstruction from the exported JSON representation. Its dependency graph includes private and unused project declarations and continues to the pinned Lean and Mathlib boundary. These checks establish the formal propositions when the build succeeds; the definitions and identification lemmas explain how those propositions represent the manuscript’s ideals, gradings, homology algebras, and resolutions.
