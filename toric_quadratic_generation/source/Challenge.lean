module

public import Mathlib

/-!
# Long-edge smooth lattice polytopes

This Challenge records the main normality/quadratic-generation theorem and the
polytope formulations of the two mixed decomposition theorems in Caius Folkerts,
*Quadratic generation for smooth polytopes with long edges*, Theorems 1.1–1.3,
pages 1–2 of the accompanying paper.pdf. The divisor formulations have additional
geometric content and are not asserted here. All custom mathematical definitions
are inlined below from the pinned substantive development; no project module is
imported by this statement. The Solution imports the original proof development.
-/

@[expose] public noncomputable section
open scoped Pointwise
open AddMonoidAlgebra
namespace PaperVerification.ToricExchange
variable {M : Type*} [AddCommGroup M] (A : Set M)
/-- Sum of the underlying lattice elements in a finite multiset. -/
def total (s : Multiset A) : M := (s.map Subtype.val).sum
/-- The degree and lattice sum of a multiset monomial. -/
def grade : Multiset A →+ M × ℕ where
  toFun s := (total A s, s.card)
  map_zero' := by simp [total]
  map_add' s t := by simp [total]
variable (R : Type*) [CommRing R]
/-- The homogeneous toric map before the multiset/multiplicity identification. -/
noncomputable def multisetToricMap : AddMonoidAlgebra R (Multiset A) →+* AddMonoidAlgebra R (M × ℕ) :=
  AddMonoidAlgebra.mapDomainRingHom R (grade A)
/-- The multiplicity equivalence identifies multiset monomials with Mathlib polynomials. -/
noncomputable def polynomialEquiv : AddMonoidAlgebra R (Multiset A) ≃+* MvPolynomial A R := by
  classical
  exact AddMonoidAlgebra.mapDomainRingEquiv R Multiset.toFinsupp

/-- The faithful homogeneous toric map, `X a ↦ χ^a t`, with target exponent `(a,1)`. -/
noncomputable def toricMap : MvPolynomial A R →+* AddMonoidAlgebra R (M × ℕ) :=
  (multisetToricMap A R).comp (polynomialEquiv A R).symm.toRingHom
/-- The conventional quadratic ideal in Mathlib's polynomial ring. -/
def polynomialQuadraticIdeal : Ideal (MvPolynomial A R) :=
  Ideal.span {p | ∃ a b c d : A, (a : M) + b = (c : M) + d ∧
    p = MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d}

/-- The canonical equivalence between exponent pairs `(a,k)` and `χ^a t^k`. -/
noncomputable def characterPolynomialEquiv :
    AddMonoidAlgebra R (M × ℕ) ≃+* Polynomial (AddMonoidAlgebra R M) :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (AddEquiv.prodComm : M × ℕ ≃+ ℕ × M)).trans
    (AddMonoidAlgebra.curryRingEquiv.trans (Polynomial.toFinsuppIso _).symm)
/-- The toric homomorphism with exactly the paper's target `R[M][t]`. -/
noncomputable def paperToricMap :
    MvPolynomial A R →+* Polynomial (AddMonoidAlgebra R M) :=
  (characterPolynomialEquiv (M := M) R).toRingHom.comp (toricMap A R)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)
/-- The actual set of lattice points in a real convex set. -/
def latticePoints : Set M := embedding ⁻¹' P

/-- Integer decomposition in every positive degree, for the specified lattice embedding. -/
def IntegerDecompositionProperty : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ z : M,
    (∃ x ∈ P, embedding z = (k : ℝ) • x) →
    ∃ s : Multiset (latticePoints embedding P), s.card = k ∧
      total (latticePoints embedding P) s = z

end PaperVerification.ToricExchange

namespace PaperVerification.ToricGeometry
open PaperVerification.ToricExchange
/-- The character lattice in standard integral coordinates. -/
abbrev Lattice (n : ℕ) := Fin n → ℤ
/-- Its real scalar extension in standard coordinates. -/
abbrev Ambient (n : ℕ) := Fin n → ℝ
/-- The standard inclusion of the full lattice into its real vector space. -/
def embed (n : ℕ) : Lattice n →+ Ambient n where
  toFun z i := z i
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp
/-- A full-dimensional lattice polytope, given by a finite generating set.
The generating set is not required to contain only vertices. -/
structure LatticePolytope (n : ℕ) where
  generators : Finset (Lattice n)
  nonempty : generators.Nonempty
  fullDimensional : affineSpan ℝ (convexHull ℝ ((embed n) '' (generators : Set (Lattice n)))) = ⊤

namespace LatticePolytope
variable {n : ℕ} (P : LatticePolytope n)
/-- The ordinary convex hull defining the polytope. -/
def carrier : Set (Ambient n) := convexHull ℝ ((embed n) '' (P.generators : Set (Lattice n)))

/-- An edge is a nondegenerate line segment that is an actual face of the polytope. -/
def IsEdge (v w : Ambient n) : Prop :=
  v ≠ w ∧ IsExtreme ℝ P.carrier (segment ℝ v w)

/-- Lattice length in standard coordinates, the gcd of the coordinate differences. -/
def latticeLength (v w : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i : Fin n => (w i - v i).natAbs)
/-- Every actual edge has integral endpoints and at least the stated lattice length. -/
def EdgesAtLeast (bound : ℕ) : Prop :=
  ∀ v w : Ambient n, P.IsEdge v w →
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w ∧
      bound ≤ latticeLength vZ wZ

/-- Smoothness exactly in terms of the primitive incident edge directions forming
a lattice basis. The final clause states that these are all incident edges. -/
def Smooth : Prop :=
  ∀ v ∈ P.carrier.extremePoints ℝ,
    ∃ (vZ : Lattice n) (basis : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧
        P.IsEdge v (embed n (vZ + (lengths i : ℤ) • basis i))) ∧
      (∀ w : Ambient n, P.IsEdge v w →
        ∃ i, w = embed n (vZ + (lengths i : ℤ) • basis i))

/-- The ordinary normal cone at a point, using the standard pairing. -/
def normalCone (x : Ambient n) : Set (Ambient n) :=
  {u | ∀ y ∈ P.carrier, 0 ≤ ∑ i, u i * (y i - x i)}

/-- All cones of the normal fan, including the zero cone and boundary-face cones. -/
def normalFan : Set (Set (Ambient n)) :=
  {C | ∃ x ∈ P.carrier, C = P.normalCone x}

/-- Equality of the actual normal fans. -/
def SameNormalFan (Q : LatticePolytope n) : Prop := P.normalFan = Q.normalFan

/-- Ordinary Minkowski addition of the real polytopes. -/
def minkowskiSum (Q : LatticePolytope n) : Set (Ambient n) := P.carrier + Q.carrier

/-- Full IDP of the polytope, using every positive natural dilation. -/
def HasIDP : Prop := IntegerDecompositionProperty (embed n) P.carrier
end LatticePolytope
/-- The actual subgroup 2M of the coordinate lattice. -/
def twiceLattice (n : ℕ) : AddSubgroup (Lattice n) where
  carrier := {z | ∃ w, z = w + w}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, by abel⟩
  neg_mem' := by
    rintro a ⟨u, rfl⟩
    exact ⟨-u, by abel⟩

/-- The quotient group used in the original prescribed-parity statement. -/
abbrev ParityClass (n : ℕ) := Lattice n ⧸ twiceLattice n

/-- Send a lattice vector to its actual class modulo the doubled lattice. -/
def parityClass (n : ℕ) : Lattice n →+ ParityClass n :=
  QuotientAddGroup.mk' (twiceLattice n)
end PaperVerification.ToricGeometry

namespace ToricQuadratic
open PaperVerification.ToricGeometry PaperVerification.ToricExchange
/-- Theorem 1.1. Every positive dimension, every field, all positive
dilations, and the actual kernel of `X a ↦ χ^a t` are retained. -/
theorem normal_and_quadratic
    (k : Type*) [Field k] (n : ℕ) (hn : 1 ≤ n)
    (P : LatticePolytope n) (hP : P.Smooth) (hbound : P.EdgesAtLeast n) :
    P.HasIDP ∧
      RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) k) =
        polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) k := by sorry

/-- Theorem 1.2 in its equivalent polytope form, with a genuine
quotient class in the character lattice modulo twice that lattice. -/
theorem prescribed_parity
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
      a + b = m ∧ parityClass n a = α := by sorry

/-- Theorem 1.3 in its equivalent polytope form. This is the equality
of the two actual sets of lattice points, including both inclusions. -/
theorem adjoint_decomposition
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    {m : Lattice n | embed n m ∈ P.carrier} +
        {m : Lattice n | embed n m ∈ interior Q.carrier} =
      {m : Lattice n | embed n m ∈ interior (P.minkowskiSum Q)} := by sorry

end ToricQuadratic
