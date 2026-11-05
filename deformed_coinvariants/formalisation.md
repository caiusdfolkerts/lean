# The formalisation

This development proves the coinvariant results of *The Hivert–Thiéry conjecture and differential normal forms*, together with the weighted Jacobian theorem, the complete isolated-hypersurface theorem, and the complete-intersection statement in full codimension. The principal coinvariant declarations are `PaperVerification.PowerOperators.paper_theorem_1_1` and `PaperVerification.PowerOperators.paper_theorem_2_2`. They collect the printed conclusions into single statements; their constituent results are also available separately. The Jacobian results are assembled in `PaperVerification.EulerJacobian.paper_theorem_6_2`, the three `PaperVerification.JacobianDivergence.paper_theorem_6_3_*` declarations, and the two `PaperVerification.VectorEuler.paper_proposition_6_5_*` declarations.

## The polynomial quotients

Let $P_n=K[z_1,\ldots,z_n]$ and $E_i=z_i\partial_{z_i}$. The two operator families are

$$
A_k(c,\lambda)=\sum_i M_{z_i^k}(c_i+\lambda E_i),
\qquad
B_k(c,\lambda)=\sum_i(c_i+\lambda E_i)M_{z_i^k}.
$$

Here $M_f$ denotes multiplication by $f$. The formal definitions `original` and `reversed` are linear maps on `MvPolynomial`; they use the polynomial partial derivatives and preserve this order of composition. In particular,

$$
B_k(c,\lambda)(z^a)
 =\sum_i\bigl(c_i+\lambda(a_i+k)\bigr)z^{a+ke_i},
\qquad
A_k(c,\lambda)(z^a)
 =\sum_i(c_i+\lambda a_i)z^{a+ke_i}.
$$

The shift by $k$ is the effect of differentiating the multiplication factor. `component_eq_reversed` establishes this correspondence directly.

For a positive integer $m$, `tailHit c lam m` is the linear span of all $B_k(f)$ with $k\geq m$ and $f\in P_n$. `originalTailHit` makes the same construction for the $A$ family. Consequently their quotients have precisely the vector-space meaning of the paper’s sums of images. The definitions retain every index in the infinite tail. The finite presentation subsequently used in the proof is established by `tailHit_eq_firstTailHit`.

The parameter condition is also retained in full. `Nonresonant c lam m` is

$$
\sum_{i\in I}c_i+\lambda s\ne0
\quad\text{for every nonempty }I\subseteq[n]
\text{ and every integer }s\geq m|I|.
$$

The set of integers is unbounded. The declaration includes all nonempty coordinate subsets, which is essential when a boundary layer removes a variable. `Nonresonant.comap`, `Nonresonant.shift`, and `Nonresonant.lower_tail` prove the preservation properties needed by that induction.

The polynomial grading descends to the image-space quotient. Each operator of index $k$ shifts degree by $k$, and the development proves that every homogeneous component of a hit polynomial remains hit. `tailQuotientGrading` is the resulting internal grading, with piece `tailQuotientDegree`. The original-family grading is transported through the diagonal conjugation described below. Thus the grading in the final results is attached to the actual quotient and its polynomial representatives.

## The weighted tail theorem

Theorem 2.2 is proved over every field $K$, for every $n\geq0$ and $m\geq1$, under the stated nonresonance condition. Its basis has index set

$$
\mathcal A_{n,m}
 =\{z_1^{a_1}\cdots z_n^{a_n}:0\leq a_i<m+i-1\}.
$$

Lean indexes the variables by `Fin n`, so the corresponding bound is `a i < m + i.val`. The subtype `ArtinIndex n m` records exactly these exponents. Its cardinality is

$$
|\mathcal A_{n,m}|=\prod_{j=m}^{m+n-1}j.
$$

The definition `paper_theorem_2_2_basis` constructs a basis of the deformed quotient indexed by this finite set. Its companion `paper_theorem_2_2_basis_apply` proves that the vector attached to an exponent is the quotient class of `monomial a.val 1`. This identity is included in the proposition-valued theorem `paper_theorem_2_2_monomial_basis` and in the combined statement. It gives a precise correspondence between the asserted basis and the manuscript’s monomials.

The proof establishes spanning and a matching lower bound independently. The spanning argument handles the differential operators directly. The lower bound compares polynomial families of finite complexes with ordinary complete intersections. Once both bounds agree, the surjective map from the Artin span to the quotient is an isomorphism.

### The finite complex and the lower bound

The coordinate characteristic polynomial gives a recurrence of length $n$. For every later exponent, it expresses $z_i^\ell$ in terms of $z_i^m,\ldots,z_i^{m+n-1}$ using symmetric polynomial coefficients. Applying the post-multiplication Euler operators gives

$$
B_\ell=\sum_{j=m}^{m+n-1}B_jM_{R_{\ell j}}.
$$

The location of the multiplication map on the right is part of `reversed_tail_recurrence`. Taking images gives the exact equality between the infinite tail and the images of the first $n$ operators.

The commutator calculation is

$$
[B_i,B_j]=\lambda(j-i)B_{i+j}.
$$

`reversed_commutator` proves it over a commutative coefficient ring. Using the recurrence to express the error term in the first $n$ operators produces the deformed syzygy map. `tailMap_comp_syzygyMap` verifies that the two maps compose to zero. At slope zero they become multiplication by the weighted power sums and their ordinary Koszul relations; `zero_slope_exact_of_regular` proves the required exactness from regularity.

The matrix-specialization results formalise Lemma 2.1. A matrix over a domain has rank at every specialization at most its fraction-field rank. For a complex exact at one fiber, the two generic ranks have a sum bounded by the dimension of the middle space. Exactness forces the specialized lower bounds on those ranks to be equalities. This makes the rank of the first map at every fiber at most its rank at the exact fiber, so its cokernel has at least the comparator’s dimension. `RankSpecialization.polynomial_rank_le_at_exact_parameter` supplies the polynomial-parameter version.

The ordinary comparison uses independent generic coefficient variables in the same characteristic as $K$. The support and Vandermonde argument proves that the weighted power sums have only the origin as their common zero. The commutative-algebra development passes from finite homogeneous quotient dimension to a regular sequence, proves the relevant Koszul exactness, and computes the complete-intersection length. The comparison is made separately in every polynomial degree. `tailQuotient_finrank_ge` then sums these inequalities through the quotient’s actual grading; it does not impose a fixed degree cutoff.

### The coordinate filtration and the upper bound

Write $\pi=z_1\cdots z_n$. Full-support monomials are divisible by $\pi$; the others lie on the coordinate boundary. For $m=1$, the characteristic identity expresses multiplication by $\pi$ followed by the scalar Euler operator

$$
c_{[n]}+\lambda(E+n)
$$

as a sum of operator images. Its eigenvalue on degree $d$ is $c_{[n]}+\lambda(d+n)$, which is nonzero by nonresonance. Therefore every full-support polynomial is hit.

The boundary quotient $P_n/\pi P_n$ has the coordinate filtration

$$
F_i=(z_{i+1}\cdots z_n)(P_n/\pi P_n).
$$

A monomial belongs to the layer indexed by its largest zero coordinate. Removing that coordinate and extracting the displayed factor identifies the layer with a polynomial space in $n-1$ variables, shifted in degree by $n-i$. The remaining coefficients are $c_j$ for $j<i$ and $c_j+\lambda$ for $j>i$. The missing coordinate’s operator contribution lands in the preceding layer. The formal boundary-lifting lemmas prove this error-term assertion and the induced spanning statement.

For larger $m$, the full-support contribution reduces to tail index $m-1$ with every coefficient shifted by $\lambda$. The boundary contribution again reduces the number of variables. These two reductions supply the induction on the variable count and tail index. `tailHit_sup_artinSpan_eq_top` states the resulting spanning theorem for the full image space and the exact Artin span.

The finite upper bound and the independent lower bound yield

$$
\dim_K Q^B_{n,m}(c,\lambda)=\prod_{j=m}^{m+n-1}j.
$$

The graded basis then computes every coefficient of the Hilbert series:

$$
\operatorname{Hilb}(Q^B_{n,m};q)
 =\prod_{j=m}^{m+n-1}[j]_q,
\qquad [j]_q=1+q+\cdots+q^{j-1}.
$$

`paper_theorem_2_2_hilbert_polynomial` expresses this as equality of formal power series over the integers, using the paper’s exact product range. The empty-variable case has empty product $1$ and is included in the statement.

## Equivariance over the original field

For every subgroup $G\leq S_n$ fixing the coefficient tuple, the variable-permutation action preserves the tail image space and its grading. The target comparator is

$$
P_n/(h_m,h_{m+1},\ldots,h_{m+n-1}),
$$

where the $h_j$ are complete homogeneous symmetric polynomials in all $n$ variables. Both sides carry the actual induced permutation actions.

Nonresonance supplies the characteristic hypothesis needed for semisimple representation theory. If $\operatorname{char}K=p>0$, no coefficient can occur on $p$ coordinates: the corresponding subset sum, together with a sufficiently large multiple of $p$, would violate nonresonance. It follows that the coefficient stabilizer, and hence $G$, has order invertible in $K$. This implication is proved by `Nonresonant.isUnit_stabilizer_card`; the theorem does not add a separate hypothesis that the group order be invertible.

The equivariant lower bound is obtained by applying the complex comparison to intertwining-map spaces. Its generic coefficients are constant on $G$-orbits, and the generic ordinary weighted powers remain regular. The complete homogeneous sequence is also shown regular over every field. Its generator degrees agree with those of the weighted-power sequence, so the corresponding homogeneous Koszul resolutions give the same comparison dimensions.

The reconstruction remains over the given field $K$. In particular, $K$ need not be algebraically closed or a splitting field for $G$. Hom-space comparisons and semisimple reconstruction give equivalences on each homogeneous degree; the grading assembly joins these into a representation equivalence of the whole finite quotient. `paper_theorem_2_2_graded_representation` includes preservation of degrees in both directions.

When all coefficients coincide, the same argument permits the comparator

$$
P_n/(p_m,p_{m+1},\ldots,p_{m+n-1}).
$$

Here nonresonance already rules out the small positive characteristics that could destroy regularity of the power sums. `paper_theorem_2_2_equal_coefficient_power_sums` provides this version.

The proposition `GradedRepresentationEquivalent` used in the combined theorem means the existence of an actual `Representation.Equiv` for which membership in each source homogeneous piece is equivalent to membership in the corresponding target piece. Accordingly, the final representation claim contains both an intertwiner and the grading correspondence, beyond a numerical character or dimension identity.

## Returning to the original operators

The additional condition for the $A$ family is

$$
c_i+\lambda a\ne0\qquad(0\leq a<m).
$$

Together with the singleton instances of nonresonance, it ensures that every factor $c_i+\lambda a$ with $a\geq0$ is nonzero. The diagonal map

$$
T(z^a)=\left(\prod_i(c_i+\lambda a_i)\right)z^a
$$

is therefore an equivalence. `diagonalEquiv_original` proves the intertwining identity $TA_k=B_kT$ for all polynomials and all operator indices. The image-space correspondence gives an equivalence of the two genuine tail quotients. The map preserves each monomial line, polynomial degree, and the action of every coefficient-stabilizing permutation.

Transporting the reversed-family basis requires a small normalization: the inverse image of a monomial class is a nonzero scalar multiple of its original class. The original-family basis construction rescales these vectors and proves that its final values are precisely the original monomial classes. Thus `paper_theorem_2_2_original_monomial_basis` has the same literal-basis assertion as its reversed-family counterpart. The original Hilbert and graded-representation statements follow with the same coefficient, field, and tail-index parameters.

## The Hivert–Thiéry theorem and sharpness

For $c_i=1$, $m=1$, and $\lambda=\alpha$, the original operators are the paper’s $D_{\alpha,k}$. The set

$$
E_n=\left\{-\frac rs:1\leq r\leq n,\ s\geq r\right\}
$$

is defined by `exceptionalSet`. In characteristic zero, `nonresonant_one_iff` proves that exclusion from this exact set is equivalent to the full subset nonresonance condition. The low-exponent condition is automatic when $m=1$.

The complete homogeneous comparator in this case is identified with the ideal generated by the elementary symmetric polynomials. `completeHomogeneousIdeal_one_eq_ordinaryCoinvariantIdeal` proves the ideal equality. The induced equivalence respects the quotient maps, homogeneous pieces, and permutation actions. Combining it with Theorem 2.2 yields an equivalence for the full group $S_n$ and the literal Artin basis

$$
\{z_1^{a_1}\cdots z_n^{a_n}:0\leq a_i<i\}.
$$

The converse is proved separately. For an excluded value $\alpha=-r/s$, with $2\leq r\leq n$ and $s\geq r$, the polynomial

$$
(z_1+\cdots+z_r)^{s-1}(z_1-z_2)
$$

is annihilated by every adjoint of the original positive-index operators. The formal differentiation covers every index, including those at which the derivatives vanish. The Fischer pairing, with monomial weights $a!$, is proved nondegenerate and equivariant; its adjointness identity uses the original operators themselves.

The orbit of this witness gives a standard subrepresentation in degree $s$. The ordinary coinvariant degree representation has no standard constituent in degrees $s\geq r$. The development proves this latter assertion through the stabilizer-invariant description and the bridge from complete to elementary coinvariants. If the original Artin classes spanned at this parameter, the specialization and dimension arguments would force the relevant degree representation to agree with the ordinary comparator, contradicting the injected standard representation.

Restriction to the first $r$ variables carries a hypothetical Artin spanning statement in $n$ variables to the smaller quotient. Every exceptional fraction with numerator one can be rewritten as $-2/(2s)$ when $n\geq2$, so this obstruction covers the entire exceptional set, including its nonreduced representations. `paper_theorem_1_1_artin_necessity` proves the converse, and `original_artin_spanning_iff` records the exact criterion for every $n\geq2$.

`paper_theorem_1_1` combines the basis, the graded full-symmetric-group equivalence, and this necessity assertion. Its field-general form holds over every characteristic-zero field and specialises directly to the paper’s complex statement.

## Weighted Jacobian operators

Let $F\in K[x_1,\ldots,x_N]$ be weighted homogeneous of positive degree $h$, with positive integral weights $w_i$, and write $W=\sum_iw_i$. The Jacobian operators are

$$
B_{t,i}(g)=F_i g+tF\partial_i g,
\qquad F_i=\partial_iF.
$$

`EulerJacobian.operator` defines these maps, `hit` forms their image span, and `coefficientIdeal` is the ordinary ideal generated by the multiplication coefficients. The central Euler identity is

$$
\sum_i w_i B_{t,i}(x_i g)
 =F\bigl[h+t(E_w+W)\bigr]g.
$$

On a monomial of weighted degree $d$, the bracket is multiplication by $h+t(W+d)$. When this scalar is nonzero in every occurring degree, the identity puts every multiple of $F$ in the image span. The relation $F_i g=B_{t,i}(g)-tF\partial_i g$ then puts every Jacobian multiple there too. Euler homogeneity also gives the reverse inclusion. The result is equality of the actual vector subspaces

$$
H_t(F)=(F_1,\ldots,F_N).
$$

`occurringDegrees w` is defined using nonzero weighted homogeneous polynomials. `mem_occurringDegrees_iff` identifies it with the degrees attained by monomials, and `nonresonance_iff` translates the monomial scalar condition into the paper’s exact exclusion

$$
t\notin\left\{-\frac{h}{W+d}:P_d\ne0\right\}.
$$

Thus degrees absent from the weighted polynomial ring introduce no extra excluded parameters. `jacobian_hit_eq_of_nonresonant` proves the result over every characteristic-zero field. `paper_theorem_6_2` gives the literal complex-polynomial statement, including all variable counts: a nonzero polynomial of positive weighted degree itself implies that the variable set is nonempty. No isolated-critical-point hypothesis is needed for this equality.

## Every exceptional hypersurface fibre

For Theorem 6.3, work over $\mathbb C$ and assume that there are at least two variables and that $F$ has an isolated critical point at the origin. Write

$$
J(F)=(F_1,\ldots,F_N),\qquad K_F=P/J(F),
\qquad\Theta_F=\{X:X(F)=0\}.
$$

The formal hypothesis `IsolatedCriticalPointAtOrigin F` concerns the actual common zeros of the partial derivatives. `gradient_regular_of_isolated` derives regularity of the gradient sequence from this hypothesis and positive weighted homogeneity. The endpoint therefore requires no supplied regular sequence, dimension calculation, or choice of a Milnor basis.

The proof first works with the divergence quotient $V_F=P/\operatorname{div}\Theta_F$. Koszul exactness identifies the tangent fields with boundaries of the gradient sequence. The divergence of those boundaries gives the literal equality

$$
\operatorname{div}\Theta_F
 =\sum_{i<j}(F_j\partial_i-F_i\partial_j)(P).
$$

`divergenceSpace_eq_paper_relations` proves this equality with the ordered index set printed in the paper. The left side supports the vector-field calculations; the right side is the denominator in the final canonical defect statement.

Multiplication by $F$ preserves this relation space and acts injectively on $V_F$. The injectivity proof constructs a tangent vector field from an assumed relation $Fu=\operatorname{div}X$. After expressing $X$ as a Koszul boundary, subtracting a normalized Euler field produces another tangent field whose divergence is a nonzero scalar multiple of the homogeneous polynomial $u$. Positive weights make the scalar nonzero. Homogeneous decomposition extends the argument to arbitrary polynomials.

The Milnor reduction then proves $V_F/FV_F\simeq K_F$. `homogeneous_milnor_basis_lifts` combines this reduction, injectivity of the potential action, and the bounded grading to prove that every chosen homogeneous lift of every homogeneous Milnor basis is a basis of $V_F$ over a polynomial parameter ring. A proved transcendence statement identifies that parameter ring with the actual subalgebra $\mathbb C[F]\subseteq P$. `paper_theorem_6_3_basis_lifts` gives the resulting basis over `Algebra.adjoin ℂ {F}`, with each basis vector equal to the specified polynomial class.

At a resonant parameter $t=-h/(W+d)$, multiplication by $F$ maps $P$ onto the image of $J(F)$ in $P/H_t(F)$. Its kernel is the sum of $\operatorname{div}\Theta_F$ and the range of a scalar Euler operator. This operator has precisely one zero eigenvalue, in degree $d$; its range is the kernel of the actual degree-$d$ projection. Consequently the canonical map is

$$
J(F)/H_t(F)\simeq (V_F)_d,
\qquad [Fp]\longmapsto[p_d].
$$

`exceptionalDefectEquiv_apply_potential` proves this formula on every polynomial representative. `paperHamiltonianDefectEquiv` gives the same map with the ordered Hamiltonian denominator. Since the representative on the left is $Fp_d$, the defect lies entirely in polynomial target degree $h+d$.

The basis consists of the classes $F^jv_i$, with degree $jh+\deg v_i$. Counting these towers proves the formal-power-series identity

$$
\operatorname{Hilb}(P/H_t(F);q)
 =\operatorname{Hilb}(K_F;q)
  +q^{h+d}[u^d]\frac{\operatorname{Hilb}(K_F;u)}{1-u^h}.
$$

`paper_formula_6_1` is this coefficient-extraction formula. Its correction coefficient may vanish, so the statement computes the defect at every candidate resonance without asserting that each one changes the quotient. `paper_theorem_6_3_scalar` combines it with the full nonresonant equality, the relation-space identification, freeness over $\mathbb C[F]$, and the canonical resonant defect. The tower index ranges over every nonnegative integer; the argument uses no finite truncation of the polynomial ring.

For equivariance, a finite group acts through arbitrary invertible linear coordinate changes preserving the weights and $F$. `JacobianLinearAction` defines the polynomial action by inverse-matrix substitution and proves naturality of contraction by the chain rule and naturality of divergence by the trace identity for the transformed derivative matrix. Stability of the Jacobian ideal, Hamiltonian relation space, and hit space follows from these calculations.

A homogeneous Milnor section is constructed by averaging. Its images generate an equivariant tower decomposition, giving the printed formula

$$
J(F)/H_t(F)\simeq_G\bigoplus_{j\geq0}(K_F)_{d-jh},
$$

with the entire source defect in target degree $h+d$. The implementation uses an integer grading whose piece at $-e$ represents ordinary weight $e$. `milnor_tower_piece` proves the translation and proves that terms of negative ordinary degree vanish. The construction also proves exactness of the natural sequence

$$
0\longrightarrow J(F)/H_t(F)\longrightarrow P/H_t(F)
\longrightarrow K_F\longrightarrow0
$$

and supplies an actual homogeneous equivariant section. `paper_theorem_6_3_equivariant` assembles the decomposition, injectivity, exactness, surjectivity, and splitting. Every action in these assertions is induced by the given coordinate representation.

## Complete intersections in full codimension

For $N\geq1$, Proposition 6.5 concerns a positive weighted homogeneous regular sequence $F_1,\ldots,F_N$ in $N$ variables. Give the target $M=\bigoplus_a Pe_a$ the grading $\deg e_a=-h_a$, where $h_a=\deg F_a$, and put

$$
\mathbf F=\sum_a F_ae_a,\qquad
A_i=\sum_a\frac{\partial_iF_a}{h_a}e_a,\qquad
B_{t,i}(g)=A_i g+t\mathbf F\partial_i g.
$$

The definitions `VectorEuler.coefficientSpace` and `VectorEuler.hit` are the actual images of these coefficient and differential maps. The regular-sequence hypothesis first gives a finite homogeneous quotient and then finiteness of $P$ over the literal subalgebra $K[F_1,\ldots,F_N]$. The formal proof of Jacobian injectivity uses derivations: in characteristic zero, a derivation that vanishes on a subalgebra over which the domain is finite must vanish everywhere. Applying this to a polynomial tangent field proves that the normalized Jacobian map has zero kernel. This is derived from the given regular sequence and is not added as an assumption.

The Euler reduction therefore has no tangent-divergence term. Away from $t=-1/(W+d)$ for an occurring degree $d$, it gives $H_t=J_F$. At resonance the potential map itself induces the equivalence

$$
P_d\simeq J_F/H_t,\qquad p\longmapsto[\mathbf Fp],
$$

and the entire defect has target degree $d$. `regularDefectEquiv_canonical` proves the representative formula. Whenever $P_d\ne0$, this equivalence proves an actual failure of equality $H_t=J_F$; the exceptional set is consequently exact.

`paper_proposition_6_5_scalar` includes the Hilbert identity coefficient by coefficient for every integer target degree. This retains the possible negative-degree terms in the baseline Jacobian cokernel and gives precisely the Laurent-series statement

$$
\operatorname{Hilb}(M/H_t;q)
 =\operatorname{Hilb}(M/J_F;q)+(\dim_KP_d)q^d.
$$

The canonical map commutes with every linear group action preserving the weights and each equation. `paper_proposition_6_5_equivariant` proves that identity for the actual induced actions; a finite-group hypothesis is unnecessary for this map. Both endpoint theorems hold over every characteristic-zero field, and hence include the paper's complex case.

## Source organisation and verification

The source is modular. The `Power` modules contain the actual operators, infinite-tail recurrence, Koszul comparison, coordinate filtration, graded basis, representation comparison, and exceptional-parameter obstruction. `PowerTheoremTwoTwo` and `PowerTheoremOneOne` assemble the main statements. The `EulerJacobian` and `EulerParameters` modules supply the weighted Jacobian theorem. The `Jacobian` and `Hypersurface` modules construct the Brieskorn quotient, its homogeneous basis, the canonical defect, the Hilbert formula, and the actual linear-group actions; `HypersurfaceTheoremSixThree` assembles their scalar and equivariant conclusions. The `VectorEuler` modules retain the shifted integer grading and canonical potential map, and `CompleteIntersectionCodimensionFull` derives their full-codimension consequences from regularity. Shared grading, matrix-specialization, homogeneous complete-intersection, and semisimple-representation modules support these arguments; the vendored Tau Ceti sources retain their original notices.

The default Lake target includes the mathematical development and its kernel audit. The audit identifies owned declarations by their declaring modules, rejects local axioms and unapproved transitive axioms, and requires each of the eight selected endpoints to be an actual theorem with a checked proof body. It exports lossless kernel types and dependency information to `.lake/reports/audit/kernel-dependencies.json`. It also checks the selected dependency paths for unsafe or partial declarations; imported bodies unavailable in the module interface are recorded as boundaries and checked through Lean's exported axiom summaries. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The endpoint correspondence above explains which checked statements express the manuscript's objects and conclusions. Pinned Lean and Mathlib versions make the build reproducible; generated build products and diagnostic reports belong under `.lake/`.

The general normal-form results in §§3–5, including the noncommutative theorem (Theorem 5.1), and the positive-dimensional complete-intersection theorem (Theorem 6.4) are not yet formalised; I am working on these over the next few days.
