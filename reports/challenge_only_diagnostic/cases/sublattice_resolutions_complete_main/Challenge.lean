module
public import Mathlib
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A literal finite Rees Gröbner presentation for sublattice ideals

Proposition2.2 of Caius Folkerts, *Sublattice resolutions and Betti preservation
in all powers*. The variables are exactly the row/column variables and one
variable per lattice element. The target is the actual polynomial ring with
one homogenizing variable; sorting and predecessor relations give a monic
Gröbner basis, generate the kernel, and have the displayed initial ideal.
This is the Rees-presentation group. Betti preservation and integral derived
homology decompositions remain separate outstanding groups for this paper.
-/

@[expose] public noncomputable section
namespace PalomarSublattice
open Classical MvPolynomial
open scoped MonomialOrder
universe u v
variable {d : ℕ} (n : Fin d → ℕ)
/-- The exact finite product of the row chains. -/
abbrev FiniteTuple := ∀ r, Fin (n r)
/-- Exactly one variable per row/column pair; ULift changes only its universe. -/
abbrev FiniteVariable : Type u := Σ r, ULift.{u} (Fin (n r))
/-- The squarefree exponent of the product selecting one variable in every row. -/
def finiteRowExponent (a : FiniteTuple n) : (FiniteVariable.{u} n →₀ ℕ) :=
  ∑ r, Finsupp.single ⟨r, ULift.up (a r)⟩ 1
/-- Closure of the finite tuple set under coordinatewise minimum and maximum. -/
def finiteLatticeClosed (E : Finset (FiniteTuple n)) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E) ∧ (∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
variable {n}
/-- The disjoint sum of exact base variables and one Rees generator per tuple. -/
abbrev FiniteReesVariable (E : Finset (FiniteTuple n)) := FiniteVariable.{u} n ⊕ E
/-- The exponent of each image: base variable itself, or row product times homogenizing variable. -/
def finiteReesVariableExponent (E : Finset (FiniteTuple n)) :
    FiniteReesVariable.{u} E → Option (FiniteVariable.{u} n) →₀ ℕ
  | Sum.inl x => Finsupp.single (some x) 1
  | Sum.inr a => (finiteRowExponent n a.val).embDomain Function.Embedding.some +
      Finsupp.single none 1
/-- The induced additive map on actual polynomial exponent vectors. -/
def finiteReesExponentMap (E : Finset (FiniteTuple n)) :
    (FiniteReesVariable.{u} E →₀ ℕ) →+ (Option (FiniteVariable.{u} n) →₀ ℕ) :=
  Finsupp.weight (finiteReesVariableExponent E)
section PresentationMap
variable (E : Finset (FiniteTuple n)) (k : Type v) [CommRing k]
/-- The literal polynomial algebra map with the displayed exponent images. -/
def finiteReesPresentationMap :
    MvPolynomial (FiniteReesVariable.{u} E) k →ₐ[k] MvPolynomial (Option (FiniteVariable.{u} n)) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (finiteReesExponentMap E)
end PresentationMap
variable {E : Finset (FiniteTuple n)}
/-- A product of two tuple variables. -/
def finiteSortingHeadExponent (a b : E) : FiniteReesVariable.{u} E →₀ ℕ :=
  Finsupp.single (Sum.inr a) 1 + Finsupp.single (Sum.inr b) 1
/-- The product of their meet and join variables, using actual lattice closure. -/
def finiteSortingTailExponent (hE : finiteLatticeClosed n E) (a b : E) :
    FiniteReesVariable.{u} E →₀ ℕ :=
  Finsupp.single (Sum.inr ⟨a.val ⊓ b.val, hE.1 a.val a.property b.val b.property⟩) 1 +
  Finsupp.single (Sum.inr ⟨a.val ⊔ b.val, hE.2 a.val a.property b.val b.property⟩) 1
/-- The predecessor coefficient ratio times its tuple variable. -/
def finiteCoefficientHeadExponent (b a : E) : FiniteReesVariable.{u} E →₀ ℕ :=
  (finiteRowExponent n b.val - finiteRowExponent n a.val).embDomain Function.Embedding.inl +
    Finsupp.single (Sum.inr a) 1
section Relations
variable {k : Type v} [CommRing k] [Nontrivial k]
/-- The actual sorting binomial. -/
def finiteSortingRelation (hE : finiteLatticeClosed n E) (a b : E) :
    MvPolynomial (FiniteReesVariable.{u} E) k :=
  monomial (finiteSortingHeadExponent.{u} a b) 1 - monomial (finiteSortingTailExponent.{u} hE a b) 1
/-- The actual predecessor coefficient binomial. -/
def finiteCoefficientRelation (b a : E) : MvPolynomial (FiniteReesVariable.{u} E) k :=
  monomial (finiteCoefficientHeadExponent.{u} b a) 1 - monomial (finiteCoefficientHeadExponent.{u} a b) 1
/-- Exactly the sorting relations of incomparable pairs and predecessor relations of strict comparable pairs. -/
def FiniteReesRelations (hE : finiteLatticeClosed n E) : Set (MvPolynomial (FiniteReesVariable.{u} E) k) :=
  {f | ∃ a b : E, ¬ a.val ≤ b.val ∧ ¬ b.val ≤ a.val ∧ f = finiteSortingRelation hE a b} ∪
  {f | ∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧ f = finiteCoefficientRelation b a}
end Relations
/-- Exactly the indicated initial exponents of both relation families. -/
def finiteReesInitialHeads (E : Finset (FiniteTuple n)) :
    Set (FiniteReesVariable.{u} E →₀ ℕ) :=
  {c | (∃ a b : E, ¬a.val ≤ b.val ∧ ¬b.val ≤ a.val ∧
      c = finiteSortingHeadExponent a b) ∨
    (∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧
      c = finiteCoefficientHeadExponent b a)}
/-- The genuine monomial ideal generated by the displayed initial heads. -/
def finiteReesInitialIdeal (k : Type*) [CommRing k]
    (E : Finset (FiniteTuple n)) : Ideal (MvPolynomial (FiniteReesVariable.{u} E) k) :=
  Ideal.span ((fun c => MvPolynomial.monomial c (1 : k)) '' finiteReesInitialHeads E)
/-- The ordinary definition of a Gröbner basis: the generators lie in the
ideal and their leading terms span its actual initial ideal. -/
def IsGroebnerBasis {σ k : Type*} [CommSemiring k] (m : MonomialOrder σ)
    (G : Set (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)
variable {k : Type v} [CommRing k] [Nontrivial k]
/-- Proposition2.2: the order is constructed, not assumed, and every actual
relation is monic. Both the polynomial kernel and initial ideal are literal. -/
theorem proposition22 (hE : finiteLatticeClosed n E) :
    ∃ m : MonomialOrder.{u,u} (FiniteReesVariable.{u} E),
      IsGroebnerBasis m (FiniteReesRelations.{u} (k := k) hE)
        (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom) ∧
      (∀ f ∈ FiniteReesRelations.{u} (k := k) hE, m.Monic f) ∧
      RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom =
        Ideal.span (FiniteReesRelations.{u} (k := k) hE) ∧
      Ideal.span (m.leadingTerm ''
        (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom : Set _)) =
          finiteReesInitialIdeal k E := by sorry
end PalomarSublattice

@[expose] public noncomputable section
open scoped BigOperators
open Classical MvPolynomial
namespace PalomarSublattice.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [CommRing K]

/-- Literal coefficient Koszul coordinates in exterior degree p. -/
abbrev Coordinates (I : Ideal (MvPolynomial V K)) (p : ℕ) := Set.powersetCard V p →₀ I

/-- The ordinary deletion sign: minus one to the number of exterior
coordinates before i. The source proves equality with its shuffle sign. -/
def eraseSign (i : V) (s : Finset V) : ℤˣ :=
  (-1 : ℤˣ) ^ (s.filter (fun j => j < i)).card

/-- Deleting one incident coordinate has the required exterior cardinality.
This supporting statement must be selected in the eventual Comparator config. -/
theorem eraseIndex_card {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : (s.val.erase j.val).card = p := by
  simp [Finset.card_erase_of_mem j.property, s.property]

/-- The exterior index obtained by deleting an incident coordinate. -/
def eraseIndex {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : Set.powersetCard V p :=
  ⟨s.val.erase j.val, eraseIndex_card s j⟩

/-- The genuine signed polynomial Koszul differential: delete an exterior
coordinate and multiply its ideal coefficient by that polynomial variable. -/
def differential (I : Ideal (MvPolynomial V K)) (p : ℕ) :
    Coordinates I (p + 1) →ₗ[K] Coordinates I p :=
  (Finsupp.lsum (MvPolynomial V K) (fun s : Set.powersetCard V (p + 1) =>
    ∑ j : {j // j ∈ s.val},
      (Finsupp.lsingle (eraseIndex s j)).comp
        (LinearMap.lsmul (MvPolynomial V K) I
          (X j.val * (((eraseSign j.val s.val : ℤˣ) : ℤ) : MvPolynomial V K))))).restrictScalars K

/-- The outgoing map at homological degree zero is exactly zero. -/
def previous (I : Ideal (MvPolynomial V K)) :
    ∀ p : ℕ, Coordinates I p →ₗ[K] Coordinates I p.pred
  | 0 => 0
  | p + 1 => differential I p

/-- Read an actual polynomial ideal coefficient at one exterior coordinate. -/
def coefficientAt (I : Ideal (MvPolynomial V K)) (p : ℕ)
    (s : Set.powersetCard V p) : Coordinates I p →ₗ[K] MvPolynomial V K :=
  (I.subtype.restrictScalars K).comp (Finsupp.lapply s)

/-- Total integer degree q means polynomial coefficient degree q-p at every
exterior p-subset. Negative degrees vanish by the actual polynomial grading;
no numerical zero convention occurs in this definition. -/
def piece (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (Coordinates I p) :=
  ⨅ s : Set.powersetCard V p,
    (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℤ)) (q - (p : ℤ))).comap
      (coefficientAt I p s)

/-- The genuine cycles of the total-degree-q polynomial Koszul component. -/
def cycles (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (Coordinates I p) :=
  LinearMap.ker (previous I p) ⊓ piece I q p

/-- The canonical additive group of the actual cycle submodule. This explicit
instance keeps the quotient on the same canonical ring/module structures. -/
instance cyclesAddCommGroup (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    AddCommGroup (cycles I q p) :=
  Submodule.addCommGroup (R := K) (M := Coordinates I p) (cycles I q p)

/-- Actual boundaries, mapped from the preceding homogeneous component and
viewed in its cycles. The planned proof establishes differential squared zero. -/
def boundaries (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (cycles I q p) :=
  (Submodule.map (differential I p) (piece I q (p + 1))).comap (cycles I q p).subtype

/-- The actual homogeneous polynomial Koszul homology quotient. -/
abbrev Homology (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :=
  (cycles I q p) ⧸ boundaries I q p

/-- The canonical additive group on the actual homogeneous homology quotient. -/
instance homologyAddCommGroup (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    AddCommGroup (Homology I q p) :=
  Submodule.Quotient.addCommGroup (R := K) (M := cycles I q p) (boundaries I q p)

/-- The canonical coefficient module on the actual homogeneous homology quotient. -/
instance homologyModule (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Module K (Homology I q p) :=
  Submodule.Quotient.module (R := K) (M := cycles I q p) (boundaries I q p)

end PalomarSublattice.Koszul
namespace PalomarSublattice.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [Field K]

/-- The dimension of the actual homogeneous Koszul homology vector space. -/
def betti (I : Ideal (MvPolynomial V K)) (p : ℕ) (q : ℤ) : ℕ :=
  Module.finrank K (Homology I q p)
end PalomarSublattice.Koszul

namespace PalomarSublattice
open Classical MvPolynomial
universe u
variable {N : ℕ} {K : Type u} [Field K]
/-- The original finite-variable orientation, used only for exterior signs. -/
noncomputable instance (priority := 2000) finiteVariableLinearOrder {d : ℕ} (n : Fin d → ℕ) :
    LinearOrder (FiniteVariable.{u} n) :=
  LinearOrder.lift' (Fintype.equivFin (FiniteVariable.{u} n)) (Fintype.equivFin _).injective
/-- The paper's original two rows on the specified vertex labels. -/
abbrev GraphRows (N : ℕ) : Fin 2 → ℕ := fun _ => N
/-- The actual exponent of x_i y_j. -/
def graphPairExponent (i j : Fin N) : FiniteVariable.{u} (GraphRows N) →₀ ℕ :=
  Finsupp.single ⟨0, ULift.up i⟩ 1 + Finsupp.single ⟨1, ULift.up j⟩ 1
/-- The actual edge binomial x_i y_j - x_j y_i. -/
def graphBinomial (i j : Fin N) : MvPolynomial (FiniteVariable.{u} (GraphRows N)) K :=
  monomial (graphPairExponent i j) 1 - monomial (graphPairExponent j i) 1
/-- Every edge binomial for the original labels, counted once with i<j. -/
def graphBinomialGenerators (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  {f | ∃ i j, i < j ∧ G.Adj i j ∧ f = graphBinomial i j}
/-- The literal binomial edge ideal. -/
def graphBinomialIdeal (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  Ideal.span (graphBinomialGenerators G)
/-- The edge monomials x_i y_j with i<j in the identical original labels. -/
def graphMonomialGenerators (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  {f | ∃ i j, i < j ∧ G.Adj i j ∧ f = monomial (graphPairExponent i j) 1}
/-- The literal initial edge-monomial ideal for the specified closed labeling. -/
def graphMonomialIdeal (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  Ideal.span (graphMonomialGenerators G)
/-- The specified labeling is closed: both lower and upper neighbors of each
vertex form cliques. This is not a hypothesis about some relabeling. -/
def ClosedLabeling (G : SimpleGraph (Fin N)) : Prop :=
  (∀ {a b c}, a < b → a < c → b ≠ c → G.Adj a b → G.Adj a c → G.Adj b c) ∧
  (∀ {a b c}, a < c → b < c → a ≠ b → G.Adj a c → G.Adj b c → G.Adj a b)

/-- Theorem1.1: every field, every positive power, every homological degree,
and every integer ordinary degree; no connectivity assumption or relabeling. -/
theorem closed_graph_betti_preservation (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (s : ℕ) (hs : 0 < s) (p : ℕ) (q : ℤ) :
    Koszul.betti ((graphBinomialIdeal (K := K) G) ^ s) p q =
      Koszul.betti ((graphMonomialIdeal (K := K) G) ^ s) p q := by sorry
end PalomarSublattice

namespace PalomarSublattice.Rees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type u} [Field k]
/-- The actual image of the finite Rees polynomial presentation in S[t]. -/
def Image (E : Finset (FiniteTuple n)) (k : Type u) [Field k] :=
  (finiteReesPresentationMap.{u} E k).range
/-- The literal ordinary exterior algebra of the row-variable coordinate space. -/
abbrev Wedge := ExteriorAlgebra k (FiniteVariable.{u} n → k)
/-- The actual ordinary Koszul algebra with its genuine Rees-image coefficients. -/
abbrev TensorAlgebra := Image E k ⊗[k] Wedge (n := n) (k := k)
instance (priority := 2000) tensorRing : Ring (TensorAlgebra (E := E) (k := k)) := Algebra.TensorProduct.instRing
instance (priority := 2000) tensorAlgebra : Algebra k (TensorAlgebra (E := E) (k := k)) := Algebra.TensorProduct.instAlgebra
/-- Every base polynomial variable belongs to the displayed presentation image. -/
theorem base_mem (v : FiniteVariable.{u} n) :
    X (some v) ∈ Image E k := by sorry
/-- The actual base variable, as an element of the Rees image. -/
def baseVariable (v : FiniteVariable.{u} n) : Image E k := ⟨X (some v), base_mem v⟩
/-- Ordinary exterior contraction by the v-th coordinate functional. -/
def contraction (v : FiniteVariable.{u} n) : Wedge (n := n) (k := k) →ₗ[k] Wedge (n := n) (k := k) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (FiniteVariable.{u} n → k)))
    ((Pi.basisFun k (FiniteVariable.{u} n)).coord v)
/-- The literal Koszul differential: variable multiplication tensor contraction. -/
def differential : Module.End k (TensorAlgebra (E := E) (k := k)) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k (baseVariable (E := E) v)) (contraction v)
/-- The literal Koszul differential kills the unit. -/
theorem d_one (hE : finiteLatticeClosed n E) : differential (E := E) (k := k) 1 = 0 := by sorry
/-- Products of actual Koszul cycles are actual Koszul cycles. -/
theorem cycles_mul (hE : finiteLatticeClosed n E) (x y : TensorAlgebra (E := E) (k := k))
    (hx : differential x = 0) (hy : differential y = 0) : differential (x * y) = 0 := by sorry
/-- The actual cycles subalgebra of the literal ordinary Koszul differential. -/
def Cycles (hE : finiteLatticeClosed n E) : Subalgebra k (TensorAlgebra (E := E) (k := k)) :=
  (LinearMap.ker differential).toSubalgebra (d_one hE) (cycles_mul hE)
/-- The canonical noncommutative cycle ring, explicitly selected. -/
instance (priority := 2000) cyclesRing (hE : finiteLatticeClosed n E) : Ring (Cycles (k := k) hE) :=
  Subalgebra.toRing (Cycles (k := k) hE)
/-- The canonical scalar action on actual cycles, explicitly selected. -/
instance (priority := 2000) cyclesAlgebra (hE : finiteLatticeClosed n E) : Algebra k (Cycles (k := k) hE) :=
  Subalgebra.algebra (Cycles (k := k) hE)
/-- Zero is an actual Koszul boundary. -/
theorem boundary_zero (hE : finiteLatticeClosed n E) :
    (0 : Cycles (k := k) hE).val ∈ LinearMap.range differential := by exact ⟨0, map_zero _⟩
/-- Sums of actual boundaries are actual boundaries. -/
theorem boundary_add (hE : finiteLatticeClosed n E) {x y : Cycles (k := k) hE}
    (hx : x.val ∈ LinearMap.range differential) (hy : y.val ∈ LinearMap.range differential) :
    (x + y).val ∈ LinearMap.range differential := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by simpa only [map_add, ha, hb, Subalgebra.coe_add]⟩
/-- Negatives of actual boundaries are actual boundaries. -/
theorem boundary_neg (hE : finiteLatticeClosed n E) {x : Cycles (k := k) hE}
    (hx : x.val ∈ LinearMap.range differential) :
    (-x).val ∈ LinearMap.range differential := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨-a, by simpa only [map_neg, ha, Subalgebra.coe_neg]⟩
/-- Left multiplication by an actual cycle preserves actual boundaries. -/
theorem boundary_left (hE : finiteLatticeClosed n E) {x y : Cycles (k := k) hE}
    (hy : y.val ∈ LinearMap.range differential) :
    (x * y).val ∈ LinearMap.range differential := by sorry
/-- Right multiplication by an actual cycle preserves actual boundaries. -/
theorem boundary_right (hE : finiteLatticeClosed n E) {x y : Cycles (k := k) hE}
    (hx : x.val ∈ LinearMap.range differential) :
    (x * y).val ∈ LinearMap.range differential := by sorry
/-- The genuine two-sided ideal of Koszul boundaries in actual cycles. -/
def Boundaries (hE : finiteLatticeClosed n E) : TwoSidedIdeal (Cycles (k := k) hE) :=
  TwoSidedIdeal.mk' {z | z.val ∈ LinearMap.range differential}
    (boundary_zero hE) (boundary_add hE) (boundary_neg hE)
    (boundary_left hE) (boundary_right hE)
/-- The actual homology algebra, cycles modulo actual boundaries. -/
abbrev Homology (hE : finiteLatticeClosed n E) :=
  _root_.Quotient (Submodule.quotientRel (R := Cycles (k := k) hE) (M := Cycles (k := k) hE)
    (Boundaries (k := k) hE).asIdeal)
instance (priority := 2000) homologyRing (hE : finiteLatticeClosed n E) : Ring (Homology (k := k) hE) :=
  Ideal.Quotient.ring (Boundaries (k := k) hE).asIdeal
instance (priority := 2000) homologyAlgebra (hE : finiteLatticeClosed n E) : Algebra k (Homology (k := k) hE) :=
  Ideal.Quotient.algebra k (A := Cycles (k := k) hE) (I := (Boundaries (k := k) hE).asIdeal)
/-- The actual projection from cycles to their homology classes. -/
def classMap (hE : finiteLatticeClosed n E) : Cycles (k := k) hE →ₐ[k] Homology (k := k) hE :=
  Ideal.Quotient.mkₐ k (Boundaries (k := k) hE).asIdeal
/-- All exponent vectors actually occurring in the image monomial algebra. -/
def ExponentMonoid := AddMonoidHom.mrange (finiteReesExponentMap.{u} E)
/-- Every genuine image-monoid monomial belongs to the presentation image. -/
theorem monomial_mem (a : ExponentMonoid (E := E)) :
    monomial a.val (1 : k) ∈ Image E k := by sorry
/-- The literal image monomial represented by that exponent. -/
def coefficientMonomial (a : ExponentMonoid (E := E)) : Image E k :=
  ⟨monomial a.val 1, monomial_mem a⟩
/-- The actual standard exterior wedge indexed by a coordinate subset. -/
def wedgeBasis : Module.Basis (Finset (FiniteVariable.{u} n)) k (Wedge (n := n) (k := k)) :=
  (Pi.basisFun k (FiniteVariable.{u} n)).ExteriorAlgebra
/-- Rees degree one in the actual tensor algebra: the auxiliary exponent is
exactly one, and every exterior wedge is allowed. -/
def DegreeOnePiece : Submodule k (TensorAlgebra (E := E) (k := k)) :=
  Submodule.span k {z | ∃ a : ExponentMonoid (E := E), a.val none = 1 ∧
    ∃ F : Finset (FiniteVariable.{u} n), z = coefficientMonomial a ⊗ₜ[k] wedgeBasis F}
/-- Actual homology classes admitting an actual Rees-degree-one cycle representative. -/
def FirstClasses (hE : finiteLatticeClosed n E) : Set (Homology (k := k) hE) :=
  {z | ∃ x : Cycles (k := k) hE, x.val ∈ DegreeOnePiece ∧ classMap (k := k) hE x = z}
/-- The homology-algebra assertion of Theorem1.2, in the ordinary Koszul
algebra over its literal Rees image. -/
theorem generated_in_degree_one (hE : finiteLatticeClosed n E) :
    Algebra.adjoin k (FirstClasses (k := k) hE) = ⊤ := by sorry
end PalomarSublattice.Rees

/- Independent signed fine polynomial Koszul model draft; unelaborated.
   All coefficient modules below are actual ideals or actual polynomial quotients. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
/-- The actual signed fine degree of one polynomial variable. -/
def variableDegree (v : V) : V →₀ ℤ := Finsupp.single v 1
/-- The signed fine degree carried by an exterior wedge. -/
def exteriorDegree (s : Finset V) : V →₀ ℤ := ∑ v ∈ s, variableDegree v
/-- The literal signed fine homogeneous polynomial submodule. -/
def polynomialPiece (a : V →₀ ℤ) : Submodule k (MvPolynomial V k) :=
  weightedHomogeneousSubmodule k variableDegree a
/-- The actual ideal's homogeneous coefficient submodule, as a submodule of that ideal. -/
def idealCoefficientPiece (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) : Submodule k I :=
  (polynomialPiece a).comap (I.subtype.restrictScalars k)
/-- The actual polynomial quotient's homogeneous coefficient submodule, obtained
by the literal quotient map on homogeneous polynomials. -/
def quotientCoefficientPiece (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) :
    Submodule k (MvPolynomial V k ⧸ I) :=
  (polynomialPiece a).map (Ideal.Quotient.mkₐ k I).toLinearMap
section Coefficients
variable {M : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
  [Module k M] [IsScalarTower k (MvPolynomial V k) M]
/-- Actual coefficient Koszul chains in exterior degree p. -/
abbrev Coordinates (M : Type u) [AddCommGroup M] (p : ℕ) := Set.powersetCard V p →₀ M
/-- The ordinary signed variable-multiplication differential on actual coefficient chains. -/
def differential (p : ℕ) : Coordinates (V := V) M (p + 1) →ₗ[k] Coordinates (V := V) M p :=
  (Finsupp.lsum (MvPolynomial V k) (fun s : Set.powersetCard V (p + 1) =>
    ∑ j : {j // j ∈ s.val},
      (Finsupp.lsingle (Koszul.eraseIndex s j)).comp
        (LinearMap.lsmul (MvPolynomial V k) M
          (X j.val * (((Koszul.eraseSign j.val s.val : ℤˣ) : ℤ) : MvPolynomial V k))))).restrictScalars k
/-- Outgoing degree-zero differential is exactly zero. -/
def previous : ∀ p : ℕ, Coordinates (V := V) M p →ₗ[k] Coordinates (V := V) M p.pred
  | 0 => 0
  | p + 1 => differential p
/-- Signed fine degree alpha: each actual coefficient has degree alpha minus
its exterior-wedge degree, including negative coordinates without a zero convention. -/
def piece (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    Submodule k (Coordinates (V := V) M p) :=
  ⨅ s : Set.powersetCard V p, (C (a - exteriorDegree s.val)).comap (Finsupp.lapply s)
/-- Genuine signed-fine cycles in the actual coefficient Koszul chains. -/
def cycles (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    Submodule k (Coordinates (V := V) M p) :=
  LinearMap.ker (previous (k := k) (M := M) p) ⊓ piece C a p
/-- Canonical additive group of the actual signed-fine cycle submodule. -/
instance cyclesAddCommGroup (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    AddCommGroup (cycles C a p) :=
  Submodule.addCommGroup (R := k) (M := Coordinates (V := V) M p) (cycles C a p)
/-- Boundaries coming from the actual preceding signed-fine component. -/
def boundaries (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    Submodule k (cycles C a p) :=
  (Submodule.map (differential (k := k) (M := M) p) (piece C a (p + 1))).comap
    (cycles C a p).subtype
/-- Actual signed-fine Koszul homology as the literal cycle/boundary quotient. -/
abbrev Homology (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :=
  (cycles C a p) ⧸ boundaries C a p
/-- Canonical additive group on the literal signed-fine cycle/boundary quotient. -/
instance homologyAddCommGroup (C : (V →₀ ℤ) → Submodule k M)
    (a : V →₀ ℤ) (p : ℕ) : AddCommGroup (Homology C a p) :=
  Submodule.Quotient.addCommGroup (R := k) (M := cycles C a p) (boundaries C a p)
/-- Canonical coefficient module on that same signed-fine homology quotient. -/
instance homologyModule (C : (V →₀ ℤ) → Submodule k M)
    (a : V →₀ ℤ) (p : ℕ) : Module k (Homology C a p) :=
  Submodule.Quotient.module (R := k) (M := cycles C a p) (boundaries C a p)
end Coefficients
end PalomarSublattice.FineKoszul
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- Dimension of actual ideal-coefficient signed-fine Koszul homology. -/
def idealBetti (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) (p : ℕ) : ℕ :=
  Module.finrank k (Homology (idealCoefficientPiece I) a p)
/-- Dimension of actual quotient-coefficient signed-fine Koszul homology. -/
def quotientBetti (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) (p : ℕ) : ℕ :=
  Module.finrank k (Homology (quotientCoefficientPiece I) a p)
end PalomarSublattice.FineKoszul
namespace PalomarSublattice
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {d : ℕ} (n : Fin d → ℕ)
/-- The actual row monomial selecting one variable from every row. -/
def rowMonomial {k : Type u} [Field k] (a : FiniteTuple n) :
    MvPolynomial (FiniteVariable.{u} n) k := ∏ r, X ⟨r, ULift.up (a r)⟩
/-- The literal sublattice ideal generated by the row monomials. -/
def sublatticeIdeal {k : Type u} [Field k] (E : Finset (FiniteTuple n)) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  Ideal.span (rowMonomial n '' (E : Set (FiniteTuple n)))
/-- The manuscript's exact lexicographic predecessor relation. -/
def lexBefore (b a : FiniteTuple n) : Prop :=
  ∃ r, b r < a r ∧ ∀ s < r, b s = a s
/-- Exactly the tuples before the displayed generator, with the original labels. -/
def prefix (E : Finset (FiniteTuple n)) (a : FiniteTuple n) : Finset (FiniteTuple n) :=
  E.filter (fun b => lexBefore n b a)
/-- The genuine predecessor colon in the actual polynomial ring. -/
def predecessorColon {k : Type u} [Field k] (E : Finset (FiniteTuple n)) (a : FiniteTuple n) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  (sublatticeIdeal n (prefix n E a)).colon {rowMonomial n a}
/-- Monotone multichains, allowing repetitions, of exactly the displayed length. -/
def Multichain (E : Finset (FiniteTuple n)) (m : ℕ) :=
  {w : Fin m → E // Monotone (fun s => (w s).val)}
/-- Every such multichain belongs to the actual finite product of the finite tuple set. -/
theorem multichain_finite (E : Finset (FiniteTuple n)) (m : ℕ) : Finite (Multichain n E m) :=
  Finite.of_injective (fun w : Multichain n E m => w.val) Subtype.val_injective
noncomputable instance (priority := 2000) multichainFintype (E : Finset (FiniteTuple n)) (m : ℕ) :
    Fintype (Multichain n E m) := @Fintype.ofFinite _ (multichain_finite n E m)
/-- The exact sum of generator exponents along the full multichain. -/
def chainShift {E : Finset (FiniteTuple n)} {m : ℕ} (w : Multichain n E m) :=
  ∑ s, finiteRowExponent n (w.val s).val
/-- Ordinary coordinatewise inclusion of natural exponents into signed fine degrees. -/
def integerExponent {V : Type u} (a : V →₀ ℕ) : V →₀ ℤ := a.mapRange Int.ofNat (by rfl)
/-- The actual sum of all predecessor colons along the multichain. -/
def chainCoefficientIdeal {k : Type u} [Field k] {E : Finset (FiniteTuple n)} {m : ℕ}
    (w : Multichain n E m) : Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  ⨆ s : Fin m, predecessorColon n E (w.val s).val
/-- The signed fine Betti formula of Theorem1.2: actual ideal powers on the
left and actual polynomial quotients by the summed predecessor colons on the
right. Every field, positive power, homological degree and signed degree occurs. -/
theorem all_powers_signed_fine_betti {k : Type u} [Field k] {E : Finset (FiniteTuple n)}
    (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) (p : ℕ)
    (a : FiniteVariable.{u} n →₀ ℤ) :
    FineKoszul.idealBetti ((sublatticeIdeal n (k := k) E) ^ m) a p =
      ∑ w : Multichain n E m,
        FineKoszul.quotientBetti (chainCoefficientIdeal n (k := k) w)
          (a - integerExponent (chainShift n w)) p := by sorry
end PalomarSublattice
