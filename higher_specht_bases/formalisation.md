# Higher Specht bases for Springer and Δ-Springer rings

This guide explains the formal statements and their correspondence with the manuscript.

## The objects and the exact scope

Write $\lambda\vdash k\leq n$, put $m=n-k$, and pad $\lambda'$ by zeroes to length $n$. For a commutative coefficient ring $R$, the source uses the actual polynomial ring $R[x_1,\ldots,x_n]$ and the ideals

$$
\begin{split}
J_{n,\lambda}^{R}
&=\bigl(e_d(Y):1\leq d\leq |Y|,\
d>|Y|-\textstyle\sum_{j=n-|Y|+1}^{n}\lambda'_j\bigr),\\
I_{n,\lambda,s}^{R}
&=J_{n,\lambda}^{R}+(x_1^s,\ldots,x_n^s),\qquad
A_{n,\lambda}^{R}=R[x]/J_{n,\lambda}^{R}.
\end{split}
$$

These are `untruncatedIdeal`, `griffinIdeal` and `UntruncatedRing`; $Y$ ranges over subsets of the $n$ variables. When $k=n$, the untruncated quotient is `SpringerRing`. The empty partition is retained: $J_{n,\varnothing}=0$. Finite power bounds are positive and satisfy $s\geq\ell(\lambda)$.

Tableaux use French diagrams. Lean labels entries and rows from zero; the paper labels entries from one. The cocharge convention and row word are fixed explicitly. The action is variable relabeling, $\sigma\cdot x_i=x_{\sigma(i)}$; it descends to each permutation-stable quotient. The unnormalized Young symmetrizer first symmetrizes rows and then alternates columns. Thus `higherSpechtPolynomial` is the prescribed $F_T^S$, with its exact coefficient normalization. The multiplier is

$$
E_\eta=\prod_{j=1}^{m} e_j^{\,\eta_j-\eta_{j+1}},
\qquad \eta_{m+1}=0.
$$

The finite-$s$ indices retain both standard tableaux $S,T$ of the same shape, $\operatorname{ctype}(S|_k)\unrhd\lambda$, $\operatorname{des}(S)<s$, and $\eta\subseteq m\times(s-\operatorname{des}(S)-1)$. The degree is $\operatorname{cc}(S)+|\eta|$. A claim of `IsSpecifiedBasis` supplies a Lean `Basis` whose value at each index is the specified coset $[E_\eta F_T^S]$. This fixes the representatives as well as independence and spanning. For fixed $S,\eta$, varying $T$ gives the stated Specht copy.

Ordinary differential harmonic spaces and Frobenius formulas are over $\mathbb C$. The prescribed quotient bases and their standard-polytabloid Specht copies extend to fields of characteristic zero or greater than $n$; the integral lattice uses $\mathbb Z[1/n!]$. These are distinct coefficient statements. Integral monomial freeness, and the geometric and homological conclusions over fields, have no small-characteristic exclusion.

Corollary 4.3 permits every homogeneous symmetric multiplier with nonzero $m_\eta$ coefficient and remaining monomial-symmetric terms strictly below $\eta$ in dominance. The formal expansion criterion includes the monomial and Schur choices and retains the fixed-copy action.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Theorem 1.1 | `springer_basis_target`; `FinalStatementAudit.theorem_1_1_copies` |
| Theorem 4.1 | `theorem_4_1`; `FinalStatementAudit.theorem_4_1_basis` |
| Corollary 4.3 | `corollary_4_3_on_admissible_multipliers` |

## The pairing and its algorithmic witness

The central calculation is the triangularity criterion of Lemma 3.1. If $b$ is a distinguished exponent, $\alpha$ is the witness exponent and $r=\alpha-b$, the integral coefficient functional is

$$
\Lambda_b(f)=\sum_{\tau\in C(U)}
\operatorname{sgn}(\tau)\,[x^{\tau\alpha-r}]f.
$$

Negative exponents contribute zero. The source keeps this functional separate from ordinary differentiation. Their comparison contains the exact factor $\prod_i\alpha_i!/\prod_i r_i!$; this factor is not silently discarded.

For a fixed shape and right tableau $T$, Theorem 3.2 orders left tableaux by the squared norm and successive initial-column sums. The endpoint `theorem_3_2_selected_family` allows every finite selection, including the empty set, supplies an ordering with a specified tie rule, and states the vanishing of every entry below the diagonal. Its diagonal is exactly

$$
|\operatorname{Stab}_{R(T)}(a)|\,
|C(U)\cap C(T)\cap\operatorname{Stab}(r)|\,
\frac{\prod_i\alpha_i!}{\prod_i r_i!}.
$$

Nonvanishing is asserted over every characteristic-zero field, and positivity over $\mathbb Q$. The prefix-order statement matters: a different order that happened to give independence would not by itself identify the matrix in the paper.

**The deterministic witness in Section 2.3.** The definition selects the first terminating step count and defines the state by the literal iterate `labeledCatRun` of `labeledCatStep`. Its invariants are proved from this execution. The identity `columnInsertion_state` exposes the run; `columnInsertion_agrees_with_completed_run` identifies it with every completed run, including its filling and rejection counts. After the pending queue is empty, further steps fix the state.

Termination supplies the step count. The completed-run comparison identifies the entire labeled output, so the exponents in the pairing come from the paper's acceptance and rejection decisions. They are not chosen merely to satisfy the resulting inequalities.

**The dependency architecture.** The principal basis arguments use three strands of mathematics:

Explicit tableaux, cocharge, cyclic insertion, greedy catabolism, word moves and restriction to an initial alphabet.

Polynomial annihilation, rearrangement inequalities, support bounds and the coefficient and apolar pairings.

Integral standard monomials, permutation/tableau counts and Specht-module multiplicity spaces.

These strands meet in the full basis theorems. The source includes the dimension counts and irreducible-copy arguments; these conclusions are not additional premises in the principal statements. The parameter and geometric theories then build on those bases. Mathlib supplies the general algebraic framework, while the included TauCeti sources supply additional combinatorial, graded and homological machinery.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Theorem 3.2 | `theorem_3_2_selected_entry`; `theorem_3_2_selected_family` |
| Lemma 6.4 | `lemma_6_4_griffin_integral`; `lemma_6_4_untruncated_integral` |

## Common harmonic spaces, sums and intersections

**One family for many ideals.** For fixed positive $n,s$, Theorem 5.2 asserts a single family of polynomial Specht submodules, independent of the partition used to define a quotient. Each submodule has the indicated shape and degree. Directness is expressed by `iSupIndep`; equality with a harmonic space is an equality of actual submodules of the polynomial ring. Theorem 6.6 gives the untruncated family for every $n$: no global finiteness restriction is imposed, but only finitely many indices occur in each degree.

The representation in each copy is the ordinary complex Specht module of the indicated shape. `source/higher_specht/verified/remaining04_geometry_complete.lean` (the `ComplexYoungIdeal` section) identifies that module with the actual Young-symmetrizer left ideal: character orthogonality gives a one-dimensional Young image, and a nonzero image vector yields an intertwiner that is an equivalence by equal dimensions. `source/higher_specht/verified/remaining04_geometry_complete.lean` (the `CommonSpechtSemantics` section) proves an exact equivalence between the common-copy predicate and an irreducible invariant polynomial subspace carrying this ordinary Specht representation.

Eligibility selects summands. Ideal intersections correspond to unions of eligible indices; ideal sums correspond to intersections. The endpoints allow every finite nonempty family and every finite nested expression, with no bound on the family size or nesting depth. Literal families use `Finite` and `Nonempty` index types. They include the prescribed quotient bases, graded Frobenius characters, Specht-copy identifications and distributive laws. Corollaries 5.5 and 5.6 specialize this construction to Springer ideals. Corollary 5.7 additionally constructs a triangular change of multiplicity coordinates, independent of the right tableau: ineligible modified polynomials belong to the ideal itself. The change is defined over $\mathbb Z[1/n!]$, with Specht lattices over that ring and irreducible Specht modules over fields of characteristic zero or greater than $n$.

For Corollary 6.7, the vector-space basis and Frobenius-series statements allow partition leaves of different sizes. Its additional parameter-freeness conclusion requires a common size $k$; the common parameter ring is described in “A free family over the elementary parameters” below.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Theorems 5.2, 6.6 | `theorem_5_2_actual_specht`; `theorem_6_6_actual_specht` |
| Corollary 5.3 | `GriffinIdealExpression.corollary_5_3_basis`; `GriffinIdealExpression.corollary_5_3_frobenius` |
| Corollaries 5.5, 5.6 | `corollary_5_5_actual_specht`; `corollary_5_6_basis` |
| Corollary 5.7 | `corollary_5_7_localized`; `corollary_5_7_field` |
| Corollary 6.7 | `UntruncatedIdealExpression.corollary_6_7_basis`; `UntruncatedIdealExpression.corollary_6_7_frobenius` |

**What the decomposition says.** For a homogeneous ideal $I\subseteq\mathbb C[x]$, the formal harmonic space is

$$
\mathcal H_I=\{h\in\mathbb C[x]: f(\partial)h=0\text{ for every }f\in I\}.
$$

The common summands live in this same polynomial ring before a quotient is chosen. Selecting eligible summands gives $\mathcal H_I$; the quotient basis is a separate assertion about the corresponding cosets. In the untruncated case the direct sum has infinitely many summands, but each homogeneous degree involves only finitely many. The degreewise finiteness is what makes its graded character a formal power series.

## The freedom to choose reference tableaux

The constructions preceding Theorem 5.2, Corollary 5.5 and Theorem 6.6 allow one standard reference tableau $T_\theta$ in each shape. The canonical common family uses the row-superstandard tableau. The source `source/higher_specht/verified/remaining04_geometry_complete.lean` (the `CommonReferenceTableaux` section) keeps the reference tableau explicit and compares the resulting actual polynomial subspaces. Its `YoungTableau` argument is a bijection from the cells to the labels, so it includes every standard tableau allowed in the paper.

**The literal vector is retained.** For a fixed left tableau and multiplier, write $G_T$ for the witness computed with the labels of $T$ and $r_T$ for its derivative order. The `finiteCommonHarmonicVectorWithTableau` and `untruncatedCommonHarmonicVectorWithTableau` definitions use

$$
h_T=\varepsilon_T^{*}\!\left(\frac{1}{r_T!}\,
\partial^{r_T}G_T\right),
\qquad r_T!=\prod_i(r_T)_i!.
$$

They retain the respective maximal prefixes and exterior exponents. The Springer specialization has a separate literal-formula theorem for (5.1), using the deterministic insertion witness, rejection counts and factorial normalization. The canonical-tableau comparison is proved from the normalized formulas.

**Covariance gives equality of the cyclic copies.** Relabeling $T$ by $\sigma\in S_n$ gives

$$
h_{\sigma T}=\sigma\cdot h_T,
\qquad
\mathbb C[S_n]h_{\sigma T}=\mathbb C[S_n]h_T.
$$

The proof follows the prefix embedding, witness, rejection exponent, normalized derivative and adjoint Young symmetrizer. The permutation `relabelPerm` carries any bijective filling to any other filling of the same shape. Each cyclic copy is the span of the actual permutation orbit of its vector, so the conclusion is equality of subspaces inside the same polynomial ring.

The three `...CommonHarmonicCopyWithTableau_eq` lemmas quantify over every index and every reference tableau. The family endpoints choose one tableau in each shape, exactly as in the paper. Their shape, degree, directness and harmonic-decomposition assertions transfer along these proved equalities. The untruncated endpoint retains local finiteness and includes $n=0$; the Springer endpoint includes the master harmonic space and assumes $n>0$; the finite theorem assumes $n,s>0$.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Theorem 5.2 | `theorem_5_2_any_right_tableaux`; `finiteCommonHarmonicVectorWithTableau_covariant` |
| Corollary 5.5 | `corollary_5_5_any_right_tableaux`; `springerCommonHarmonicVectorWithTableau_literal_formula` |
| Theorem 6.6 | `theorem_6_6_any_right_tableaux`; `untruncatedCommonHarmonicCopyWithTableau_eq` |

The reference-choice endpoints are recorded separately from the Specht-identification endpoints. The former identify the literal subspaces for every choice of reference tableaux; the latter identify their actual restricted representations. The three `actual_specht` family theorems combine both conclusions.

**From copies to Frobenius series.** The coefficients come from traces of the actual graded quotients. TauCeti identifies Specht characters with genuine Schur polynomials and proves the classical cycle-type formula. For fixed $S_n$, the $n$-variable Schur basis retains every partition of $n$, so its coefficient equivalence preserves exactly the paper's identities. This is a fixed-degree realization; the full infinite-alphabet symmetric-function Hopf algebra is not constructed. Formal power series retain every grading coefficient and the proved inverse denominator.

## A free family over the elementary parameters

The parameter ring is a formal polynomial ring, acting on the actual untruncated quotient:

$$
B_R=R[t_1,\ldots,t_m],\qquad
B_R\longrightarrow A_{n,\lambda}^{R},\quad t_j\longmapsto[e_j].
$$

Here `ElementaryParameterRing` carries the *weighted* grading $\deg t_j=j$. The quotient retains $\deg x_i=1$, so this parameter map is graded. Calling the source a polynomial ring does not assume that its image is algebraically independent; injectivity is a separate conclusion.

**The prescribed higher Specht basis.** Over a characteristic-zero field $R$, Theorem 6.1 removes the rectangle bound on $\eta$. Every weakly decreasing nonnegative sequence $\eta$ with at most $m$ parts gives $E_\eta$, and the differences $\eta_j-\eta_{j+1}$ range over all parameter-monomial exponents. Thus the vector-space family $[E_\eta F_T^S]$ becomes a finite free $B_R$-basis consisting of the unchanged $[F_T^S]$ with eligible prefix. Its rank is

$$
\operatorname{rank}_{B_R} A_{n,\lambda}^{R}
=\frac{n!}{\prod_i\lambda_i!}.
$$

The parameters are algebraically independent. Over every field the algebra has dimension $m$ and is Cohen--Macaulay; the all-field conclusion comes from the integral monomial basis below.

Remark 6.2 retains the *same unnormalized higher Specht basis* over every nontrivial commutative ring in which $n!$ is a unit. The field condition is exactly characteristic zero or characteristic greater than $n$, and the integral endpoint is the literal localization $\mathbb Z[1/n!]$. Its proof discharges the required finite Griffin basis assertions before using degreewise stabilization. Necessity is witnessed by the actual one-row family member $n!\cdot1$.

**The special fiber and integral lifting.** Put $\mu=\lambda\cup(1^m)$. Proposition 6.3 identifies both the ideal and the quotient at the parameter origin:

$$
J_{n,\lambda}^{\mathbb Z}+(e_1,\ldots,e_m)=I_\mu^{\mathbb Z},\qquad
A_{n,\lambda}^{R}/(e_1,\ldots,e_m)\simeq R_\mu^{R}.
$$

It also proves the matching catabolizability eligibility. Lemma 6.4 supplies integral standard-monomial bases. Corollary 6.5 lifts *any* homogeneous integral monomial basis of this Springer fiber to a $B_{\mathbb Z}$-basis, identifies its actual monomial representatives, and proves its scalar extensions. Hence finite freeness and flatness survive in every characteristic, even when the prescribed higher Specht family does not.

Over $\mathbb C$, the parameter weights produce the Frobenius denominator $\prod_{j=1}^{m}(1-q^j)$. For Corollary 6.7, a common partition size $k$ gives the same parameter ring for every leaf of a finite ideal expression; its free basis and dimension-$m$ Cohen--Macaulay conclusion retain that common-size hypothesis. Empty partitions and $m=0$ remain included.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Theorem 6.1 | `theorem_6_1_basis_and_rank`; `theorem_6_1_dimension_and_cohenMacaulay` |
| Remark 6.2 | `remark_6_2_untruncated_characteristic`; `remark_6_2_untruncated_localized` |
| Proposition 6.3 | `proposition_6_3`; `proposition_6_3_eligibility` |
| Corollary 6.5 | `integralMonomialParameterBasis_of_basis`; `corollary_6_5_allFields` |
| Corollary 6.7 | `UntruncatedIdealExpression.corollary_6_7_parameters` |

## Every fiber and the primary geometry

Let $K$ be any field. For a parameter value $a$ whose polynomial splits over $K$, write

$$
Q(t)=t^m-a_1t^{m-1}+\cdots+(-1)^ma_m
=t^{r_0}\prod_{j=1}^{h}(t-c_j)^{r_j},
$$

where the displayed nonzero roots are distinct, $r_j>0$ for $j>0$, and $\sum_{j=0}^{h}r_j=m$. Put $k_0=k+r_0$ and $\mu_0=\lambda\cup(1^{r_0})$. Theorem 7.1 is an algebra equivalence for the actual quotient by $(e_j-a_j)$:

$$
A_{n,\lambda}^{K}/(e_j-a_j)_j
\;\simeq\!
\prod_{\text{root assignments}}
\left(R_{\mu_0}^{K}\otimes_K
\bigotimes_{j=1}^{h}R_{(1^{r_j})}^{K}\right).
$$

The assignment type records exactly $k_0$ positions at zero and $r_j$ positions at $c_j$. Its cardinality is $n!/(k_0!\prod_jr_j!)$. Explicit translations and block enumerations identify the factors. The splitting-field and algebraic-closure endpoints do not assume that the parameter polynomial already splits over the original field.

**The ordered-root locus.** Proposition 7.2 works over $B'=\mathbb Z[c_1,\ldots,c_m,(\prod_jc_j\prod_{i<j}(c_i-c_j))^{-1}]$. The product is indexed by injections $[m]\hookrightarrow[n]$. Separate endpoints identify the selected coordinates with the roots, prove compatibility with variable permutations, and give the induced $S_n$-representation. Scalar extension to fields and $m=0$ are retained. The equivalence is identified with its explicit composite of parameter base change, fiber decomposition and block relabeling. Coordinate and equivariance statements refer to this same map.

**Primary components and reducedness.** Proposition 7.3 gives the actual intersection of the extended Springer ideals on $k$-element coordinate sets, over every field and over $\mathbb Z$. It includes primaryness, the coordinate radicals and irredundancy. The field support is the union of the coordinate $m$-planes. Generic multiplicity is measured by module length after localization; standard graded multiplicity comes from the Hilbert polynomial. The values are respectively $k!/\prod_i\lambda_i!$ and $n!/(m!\prod_i\lambda_i!)$.

Corollary 7.4 characterizes reducedness by $\ell(\lambda)\leq1$. For fibers, geometric reducedness is stated using `Algebra.IsGeometricallyReduced`. The étale criterion uses `Algebra.Etale` after localization at *every* prime of the parameter ring: it requires $\ell(\lambda)\leq1$, a separable residue-field polynomial and, when $\lambda$ is nonempty, nonvanishing at zero. It does not replace geometric reducedness by ordinary reducedness over an imperfect field.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Theorem 7.1 | `theorem_7_1_parameter_fiber`; `theorem_7_1_algebraicClosure` |
| Proposition 7.2 | `proposition_7_2_integral_trivialization`; `proposition_7_2_integral_trivialization_permutation`; `proposition_7_2_integral_induced_tensor` |
| Proposition 7.3 | `proposition_7_3_primary_decomposition`; `proposition_7_3_multiplicities` |
| Corollary 7.4 | `untruncated_isReduced_iff`; `parameterFiber_geometricallyReduced_iff_polynomial`; `parameter_etale_atPrime_iff_polynomial` |

## Homological invariants and characteristic

Let $n(\lambda)=\sum_i(i-1)\lambda_i$ and $\mu=\lambda\cup(1^m)$. The statements of Corollaries 7.5 and 7.6 are over every field, including small positive characteristic.

**Regularity.** The statement concerns the graded groups $\operatorname{Tor}_i^{K[x]}(A_{n,\lambda},K)$. Here the polynomial ring acts on $K$ by constant terms. A projective Koszul resolution gives the comparison `polynomialTorCoordinateEquiv` between Mathlib's derived tensor object and coordinate Koszul homology. In exterior degree $i$, internal degree $j$ means coefficient degree $j-i$. The differential preserves internal degree. The homogeneous-cycle characterization and `polynomialTorGrading_independent` identify this intrinsic grading independently of the coefficient basis used in its construction. Regularity therefore asserts both vanishing above the line $j-i=n(\lambda)+m\ell(\lambda)$ and attainment on that line:

$$
\operatorname{reg}(A_{n,\lambda})=n(\lambda)+m\ell(\lambda).
$$

**Socle, canonical module and classification.** The Springer special fiber $R_\mu$ has module socle equal to its degree-$n(\mu)$ piece, of dimension $f^\mu=\#\operatorname{SYT}(\mu)$. The canonical module has underlying module $\operatorname{Hom}_{B_K}(A_{n,\lambda},B_K)$, with action $(a\cdot\phi)(b)=\phi(ab)$. Put $W=\sum_{j=1}^m j=\binom{m+1}{2}$. Its normalization is intrinsic:

$$
\phi\in(\omega_A)_q
\quad\Longleftrightarrow\quad
\phi(A_t)\subseteq(B_K)_{t+q-W}\quad\text{for every }t\in\mathbb Z.
$$

Thus it is the graded relative dual with target $B_K(-W)$, using the parameter weights $1,\ldots,m$. Its dualizing property includes finite generation, actual finite injective dimension, the homothety isomorphism and vanishing of positive self-$\operatorname{Ext}$.

The canonical-module statement supplies $f^\mu$ homogeneous generators in degree $W-n(\mu)$ and proves that every finite generating family, including a nonhomogeneous one, has at least $f^\mu$ members. The Gorenstein predicate says that the ring is Noetherian and every prime localization has finite self-injective dimension. Complete intersection means that some regular sequence generates the original ideal, without a homogeneity premise. Both classifications give precisely: $\lambda$ is a column, including the empty partition, or $k=n$ and $\lambda=(n)$.

**The exact characteristic range.** For every admissible $n,\lambda,s$, Corollary 8.1 concerns the specified unnormalized polynomials. Their coefficient-pairing diagonal contains two subgroup orders dividing $n!$; the differentiation factorials have been removed. This yields the localized statement over $\mathbb Z[1/n!]$ and the field condition $\operatorname{char}K=0$ or $\operatorname{char}K>n$, with no condition involving $s$. Necessity uses the eligible one-row polynomial $n!\cdot1$, which vanishes in characteristic $p\leq n$. In the admissible field range, the fixed polynomial spans are equivariantly isomorphic to standard-polytabloid Specht modules and are irreducible. Over $\mathbb Z[1/n!]$ the statement is about Specht lattices. Neither assertion extends the ordinary complex differential-harmonic construction to positive characteristic.

| Paper | Lean entry points, in the namespace: `HigherSpecht` |
| --- | --- |
| Corollary 7.5 | `corollary_7_5_tor_regularity`; `corollary_7_5_tor_support` |
| Corollary 7.6 | `springer_socle_concentrated_and_type`; `corollary_7_6_canonical_module`; `corollary_7_6_gorenstein_iff`; `corollary_7_6_completeIntersection_iff` |
| Corollary 8.1 | `corollary_8_1_griffin_characteristic_all_partitions`; `corollary_8_1_springer_characteristic`; `corollary_8_1_griffin_localized`; `corollary_8_1_springer_localized` |

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.
