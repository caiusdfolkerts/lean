# Dimension and identifiability of three-sunlet models

This note accompanies the Lean project for Caius Folkerts's *Dimension and identifiability of three-sunlet models*. References such as "Theorem 4.2" refer to that manuscript. The aim is to explain what the formal objects mean, where the substantial arguments enter, and how a reader can trace each conclusion back to its hypotheses. The code treats the image as an actual algebraic image and the parameters as independent variables throughout.

## The parameter space and its image

A normalized Latin system consists of finite sets of colours $I$ and positions $\Omega$, a distinguished colour $0$, and permutations $\pi_a$ of $\Omega$. The identity colour acts as the identity permutation. For each position $b$, the map $a\mapsto\pi_a(b)$ is a bijection. Write $m=|\Omega|=|I|$ and fix a position $o$. The formal structure `NormalizedLatinSystem` records these properties, without choosing a group law or an enumeration of either set.

The five parameter families are $s,t,h:\Omega\to k$ and $u,v:I\to k$. They give the polynomial coordinate map

$$
Q_{a,b}=s_b t_{\pi_a(b)}
\bigl(u_a h_{\pi_a(b)}+v_a h_b\bigr).
\tag{1}
$$

The coordinate ring is the quotient of $k[Q_{a,b}]$ by the kernel of substitution into these polynomials. Over an infinite field this kernel is proved equal to the ideal of polynomials vanishing on the actual image. Over an algebraically closed field its zero locus is the image closure. Dimension means the Krull dimension of this quotient ring. No dimension formula enters its definition.

For a finite abelian group $G$, the original six-family coordinates are

$$
q_{a,b,c}=w_{1,a}w_{2,b}w_{3,c}
\bigl(w_{4,a+b}w_{5,a}+w_{4,b}w_{6,a}\bigr),
\qquad a+b+c=0.
$$

The index equivalence $(a,b,c)\leftrightarrow(a,b)$ has inverse $(a,b)\mapsto(a,b,-a-b)$. The parameter substitution

$$
s_b=w_{2,b},\quad t_d=w_{3,-d},\quad h_b=w_{4,b},\quad
u_a=w_{1,a}w_{5,a},\quad v_a=w_{1,a}w_{6,a}
$$

and its section $w_{1,a}=1$ prove equality of the entire polynomial images. These are identities at zero parameters too. The corresponding coordinate-ring isomorphisms justify stating the group results in the paper's Fourier coordinates.

## Dimension without a characteristic restriction

Theorem 2.3 is the general dimension statement used for Theorem 1.1. Apart from the identity colour, suppose that there are $c$ distinct derangements, divided into two families $P,N$. Each family contains at least two permutations and acts transitively. Then the dimension of (1) is $3m+2c-2$ over every algebraically closed field. The formal statement retains exactly this transitivity hypothesis. It does not require a full Latin square.

Give $h_o$ weight two, the other $h$ variables weight zero, and select opposite coefficient weights on $P$ and $N$. Every coordinate has a unique least-weight monomial. On $P$ it is the first summand except at the incoming edge to $o$; on $N$ it is the second except at the outgoing edge. A rational column relation $(S,T,H,U,V)$ in the resulting exponent matrix satisfies

$$
T_b=-S_b-H_b-V_0.
$$

With $K=S+H$, the remaining ordinary rows become

$$
S_{\pi_a b}-S_b=U_a-V_0\quad(a\in P,\ b\ne\pi_a^{-1}o),\qquad
K_{\pi_a b}-K_b=V_a-V_0\quad(a\in N,\ b\ne o).
$$

The one-omitted-edge lemma recovers the missing equations and makes their constant differences zero. Transitivity makes both functions constant. The exceptional rows then leave precisely four independent column relations.

This calculation takes place over $\mathbb Q$, even when the geometric ground field has positive characteristic. Independent rational exponent vectors give algebraically independent coordinate polynomials: different products of the selected monomials have different exponents, so the least-weight part of a nonzero polynomial relation cannot cancel. The upper bound follows from the identity coefficient $\gamma=u_0+v_0$ and three scaling freedoms. The finite-type algebra and transcendence-degree arguments linking these bounds to Krull dimension are included in the dependency chain.

For a full normalized Latin system of order $m\geq5$, the formal partition lemma supplies $P,N$, and $c=m-1$ gives $5m-4$. This proves Theorem 1.1 in all its allowed characteristics and orders. The use of exponent rank is essential: Jacobian rank alone would not justify the positive-characteristic statement.

## Normalization and uniqueness of the toric summands

On the open set where the diagonal output coordinates are nonzero, put

$$
z_b=\gamma s_b t_b h_b,\qquad k_b=s_b/s_o,\qquad
l_b=s_bh_b/(s_oh_o),\qquad U_a=u_a/\gamma,\quad V_a=v_a/\gamma.
$$

Here $a\ne0$ in the last two families, and $k_o=l_o=1$. The coordinate identity is

$$
Q_{0,b}=z_b,\qquad
Q_{a,b}=z_{\pi_a(b)}
\left(U_a\frac{k_b}{k_{\pi_a(b)}}+
V_a\frac{l_b}{l_{\pi_a(b)}}\right)\quad(a\ne0).
\tag{2}
$$

Define $F(U,k)_{a,b}=U_a k_b/k_{\pi_a(b)}$ and let $X_\Pi$ be its actual toric image closure. The secant cone is the closure of sums of two points of this cone. The uniqueness assertion quantifies over all points of $X_\Pi$, including its boundary. Restricting both competing decompositions to a parameter torus would leave a gap in the theorem.

The proof develops the sparse contact argument in Sections 4 and Appendix A. A pair supported on disjoint transitive colour families has an injective combined differential. A two-ratio finite-difference lemma and the colour deletion argument show that the contact kernel consists only of the radial direction. The support construction covers every order: the general orbit merging argument is supplemented by the order-six analysis, the order-eight regular elementary abelian exception, and the complete order-five calculation. The small certificates are proofs of the exhaustive finite cases needed by these structural arguments.

The bridge from this calculation to generic uniqueness is proved directly using function fields and derivations. It does not assume a tangential-contact criterion from the literature. The actual source field is finite and separable over the field generated by the sum coordinates. Extending coordinate derivations to an algebraic closure constrains every embedding of the source over that image field. The radial contact calculation and the resulting two-dimensional span identify the unordered pair of toric points.

To pass from function fields to an open set of geometric points, the proof constructs rational reconstruction expressions and clears their denominators. The resulting polynomial identities hold on the actual toric closures. Further numerators force every coordinate of both recovered points to be nonzero and force the two points to be distinct. A torus lifting argument uses the literal integer exponent lattice and extension of characters into the divisible group $K^\times$ over an algebraically closed field. It does not assume that this lattice is saturated.

The endpoint therefore supplies a polynomial $P$ whose nonvanishing locus in the secant cone is nonempty and Zariski dense, together with existence and uniqueness of the unordered decomposition on that locus. Density is proved as an equality of vanishing ideals, so "general" has an explicit algebraic meaning in the formal statement.

## The finite ambiguity and the entire fibre

The bijection $a\mapsto\pi_a(o)$ turns the Latin system into a loop $L$. Its abelianization is presented by generators $[b]$ with relations $[o]=0$ and $[a*b]=[a]+[b]$. This is a quotient of the free abelian group, not a finite group supplied as an extra hypothesis. The natural map from $\Omega$ is proved surjective. Loop translations give bijections between its fibres, which proves that its order $c$ is finite and divides $m$.

If two normalized parameter points represent the same toric point with every coordinate nonzero, their ratios $\rho_b=k'_b/k_b$ satisfy

$$
\rho_o=1,\qquad \rho_{a*b}=\rho_a\rho_b,
\qquad U'_a=\rho_aU_a.
$$

They are exactly characters of $L_{\mathrm{ab}}$. Over an algebraically closed field of characteristic zero there are $c$ such characters. The two components give independent character actions, and their interchange gives the semidirect product

$$
\bigl(\mathop{\mathrm{Hom}}(L_{\mathrm{ab}},K^\times)\bigr)^2\rtimes S_2.
$$

The action is inverse precomposition on the two-element index. The universal character equivalence intertwines this action, so `normalizedGaloisUniversalEquiv` identifies this literal semidirect product with the automorphism group of the normalized source field over the actual image field. All embeddings are accounted for, giving the degree $2c^2$ and the Galois property. For a nonassociative loop of prime order, $c=1$: a bijective map to its abelianization would make the original loop associative. Corollary 5.1 is stated both for field automorphisms and for actual parameter points. Over one dense open, every normalized preimage is one point or its distinct component interchange. Alternative normalized diagonal and nonidentity coefficient families remain affine in this statement; their nonvanishing follows from the output.

The continuous factors in the original fibre are recovered by the formulas

$$
\begin{align*}
s_b&=S k_b,& h_b&=H l_b/k_b,& t_b&=z_b/(\Gamma SHl_b),\\
u_a&=\Gamma U_a\ (a\ne0),&v_a&=\Gamma V_a\ (a\ne0),&
u_0&=T,\quad v_0=\Gamma-T.
\end{align*}
$$

Here $S,H,\Gamma$ are units and $T$ is arbitrary. The inverse is the normalization above, together with $S=s_o$, $H=h_o$, $\Gamma=u_0+v_0$ and $T=u_0$. These identities are proved over every commutative ring and commute with ring maps. When the output diagonals are units, their product formula forces every required original parameter to be a unit. Thus this describes the whole fibre over that open set.

The geometric statement is expressed by polynomial isomorphisms. Embed $\mathbb G_m^3\times\mathbb A^1$ in affine seven-space by

$$
x_0x_1=1,\qquad x_2x_3=1,\qquad x_4x_5=1,
$$

with $x_6$ free. For each normalized preimage the expansion formulas and their inverse are literal polynomials on this affine presentation. For example the inverse of $S$ is recovered as $z_o^{-1}(u_0+v_0)t_oh_o$, where $z_o^{-1}$ is a fixed scalar on the fibre. The proof gives equations for every component, proves that different components are disjoint, and proves that their union is the complete original affine fibre. The number of components is $2c^2$.

For the original six edge families of a group model, absorption sends $(w_1,s,t,h,w_5,w_6)$ to $(s,t,h,u,v)$, with $u_a=w_{1,a}w_{5,a}$ and $v_a=w_{1,a}w_{6,a}$. On a smaller dense principal open, every colour has a nonzero output coordinate. Hence every $w_{1,a}$ is nonzero in every affine preimage. Restoring these $|G|$ independent units gives the whole original fibre. The endpoint `GroupCoordinates.six_family_general_fiber` uses the literal six-family coordinates and gives $2|G|^2$ pairwise disjoint closed subvarieties, each polynomially isomorphic to $\mathbb G_m^{|G|+3}\times\mathbb A^1$. The inverse unit coordinates are polynomial on the fibre because a fixed nonzero output coordinate recovers them. No further restriction on the parameter fibre is imposed.

There is also a ring-level statement for the normalized geometric generic fibre. If $B\subseteq A$ are the actual coordinate image algebra and localized source algebra, $F=\mathop{\mathrm{Frac}}(B)$, and $K$ is an algebraically closed extension of $F$, then an algebra isomorphism gives

$$
K\otimes_F(F\otimes_B A)\ \cong\ K^{\,2c^2}.
$$

The source fraction field and the embedding of $B$ are constructed from the literal polynomial substitution. This statement distinguishes a split, reduced geometric fibre from a calculation that counts only its closed points.

## Rationality and sparse coordinate recovery

Rationality in Theorem 4.2 is over $\mathbb Q$. The formal result identifies the fraction field of the actual model coordinate ring with a rational function field over the ground field. First, a basis of the integral monomial lattice identifies the function field of the split toric cone with a rational field. For two copies with independent coordinates $x_i,y_i$, distinguish an index $1$. The code uses the interchange-invariant functions

$$
s=x_1+y_1,\qquad p=x_1y_1,\qquad
\alpha_i=\frac{x_i-y_i}{x_1-y_1},\qquad
\beta_i=\frac{x_1y_i-y_1x_i}{x_1-y_1}\quad(i\ne1).
$$

The denominator is nonzero by algebraic independence. The identities $x_i=\alpha_i x_1+\beta_i$ and $y_i=\alpha_i y_1+\beta_i$ show that the full paired field is generated over these invariants by $x_1$, which satisfies $T^2-sT+p=0$. Every element therefore has the form $a+bx_1$ with invariant coefficients. If it is fixed by interchange, then $b(x_1-y_1)=0$, so $b=0$. This proves equality with the *entire* fixed field, rather than just exhibiting invariant functions. Its $2d$ displayed generators are algebraically independent by the transcendence-degree calculation. The field of the actual secant is identified with this fixed field through the embedding classification. This proves rationality over the original characteristic-zero field. Restoring the independent diagonal variables in (2), and proving the exact bridge to the original substitution kernel, gives rationality of the five-family model as well.

For Theorem 6.1, take $G=\mathbb Z/m\mathbb Z$ with $m\geq6$. The retained indices are exactly the six full colour rows $0,1,2,-1,3,-2$, and the two positions $b=0,-a$ in every other nonzero colour. The code proves that these indices are distinct where required and that their total number is $8m-12$. No bounded range of moduli is substituted for the quantifier $m\geq6$.

The supports $\{1,2\}$ and $\{-1,3,-2\}$ satisfy the sparse contact hypotheses at every such order. The five-colour Jacobian calculation makes the shared torus parameters and the selected coefficients algebraic over the observed coordinate field. For an omitted colour, the two retained entries give a linear system with determinant

$$
\frac{l_{-a}}{k_a}-\frac{k_{-a}}{l_a}
=\frac{l_al_{-a}-k_ak_{-a}}{k_al_a}.
$$

Its nonvanishing is proved as a rational-function identity, including the case $a=-a$, so the omitted coefficients are algebraic as well.

Now consider any embedding of the full parameter field into an algebraically closed extension that fixes the observed coordinates. The sparse contact result aligns the two monomial summands, allowing their interchange. The complete colour-one row forces any remaining torus quotient to be a cyclic character; the two retained entries in each omitted row determine the corresponding coefficient quotients. Consequently every full model coordinate is fixed. Separability and the proved embedding criterion give equality of the observed and full coordinate fields over the original ground field. This is rational recovery of the model point despite algebraic ambiguity of its parameters.

Choosing numerators and denominators in the observed coordinate algebra gives an actual rational inverse to the literal coordinate projection, with its identities on nonempty dense open sets. The formal equivalence identifies the projection on the original substitution quotients and is defined over $\mathbb Q$.

## Orbit models and genuine network graphs

Theorem 7.1 uses a finite abelian group of order at least five and an arbitrary subgroup $B\leq\operatorname{Aut}(G)$. Parameters are identified along actual $B$-orbits in each family. With $r$ orbits, including $\{0\}$, the dimensions are

$$
5\quad(r=2),\qquad
10\quad\bigl(\{0\},H\setminus\{0\},G\setminus H\bigr),\qquad
5r-4\quad\text{otherwise},
$$

where the middle case requires $[G:H]=2$. The inverse-stable partition classification and the passage from arbitrary automorphism orbits to their coarsening by negation are both formalized. The latter matters: an arbitrary $B$-orbit need not be invariant under negation. Corollary 7.4 specializes this classification to cyclic groups and proves the precise prime/full-automorphism exception.

For Corollary 8.1 the network is an actual finite simple graph. Its leaves have degree one, other vertices degree three, it is connected, and distinct cycles are vertex-disjoint. Cycle lengths are therefore at least three. Each cycle has a reticulation decoration consisting of two distinct adjacent edges at its chosen vertex. Orientations are explicit and are proved not to affect the defining ideal after the appropriate parameter renaming.

The Fourier coordinates are sums over displayed choices and conserved edge flows for a zero-sum leaf assignment. Deleting the selected reticulation edge from each cycle gives an actual tree. Its incidence map sends edge assignments to vertex assignments with total sum zero. Summing the conservation equations across an edge cut proves injectivity. If the tree has $v$ vertices, both finite sets have $|G|^{v-1}$ elements; choosing a root identifies the latter set with $G^{v-1}$. Thus the incidence map is bijective. Every displayed choice has exactly one conserved flow, and the cut calculation identifies each edge label with the sum of the leaf labels on its side. This proves equality with the paper's one-monomial-per-choice parameterization. The graph structure carries no dimension, gluing, or decomposition assumptions.

The graph argument cuts a genuine internal bridge and adds a fresh leaf on each side. The smaller graphs retain the required properties. Their edge, cycle and triangle counts satisfy

$$
E_1+E_2=E+1,\qquad C_1+C_2=C,\qquad C_{3,1}+C_{3,2}=C_3.
$$

The terminal graph classification supplies actual vertex and incidence isomorphisms to a single edge, a three-leaf tree, or a sunlet. Local dimensions are transported through the literal polynomial coordinate maps.

The cut-edge dimension formula is developed from conserved-flow factorization, not assumed from a cited paper. Matching boundary labels gives a precise coordinate-kernel identity. The corresponding rational differential spaces lose exactly the $r$ independent grading directions. A characteristic-zero algebraic argument identifies this rank with the Krull dimension of the actual coordinate image, giving $d=d_1+d_2-r$. Together with the local calculations, graph induction yields

$$
\dim V_N^{(G,B)}=(r-1)(E-C)+1-\delta_B C_3.
$$

Here $\delta_B=1$ precisely in the two exceptional orbit types above. The Euler and degree-sum identities give $E=2n-3+3C$, and the unrestricted case is

$$
\dim V_N^G=(|G|-1)(2n-3+2C)+1.
$$

The manuscript's induction needs a small addition: the network with two leaves and one edge is itself a terminal block. Its dimension is $r$, since its Fourier coordinates provide one independent coordinate per orbit. The accompanying corrected PDF includes this base case in the proof of Corollary 8.1. The statement of Corollary 8.1 is unchanged.

## Source organisation

The mathematical modules are under `source/`, with lowercase filenames and the original declaration namespaces. The default build also compiles the checks in `source/verification/`. Generated diagnostic files are kept in `.lake/reports/`.
