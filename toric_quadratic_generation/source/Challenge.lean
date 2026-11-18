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
imported by this statement. The Solution repeats this literal statement prefix in the same fresh namespace
and proves the claims by constructing the original polytope records and applying
the original full theorems. This avoids asking Comparator to identify raw
expressions generated in different historical declaration contexts.
-/

@[expose] public noncomputable section
open scoped Pointwise
open AddMonoidAlgebra
namespace PalomarLongEdges.ToricExchange
variable {M : Type*} [AddCommGroup M] (A : Set M)
/-- Sum of the underlying lattice elements in a finite multiset. -/
def total (s : Multiset A) : M := (s.map Subtype.val).sum
/-- The grade of the empty multiset is zero. This law is separately compared. -/
theorem grade_zero : (total A 0, (0 : Multiset A).card) = (0 : M × ℕ) := by
  simp [total]
/-- Grade is additive on actual multiset sums. This law is separately compared. -/
theorem grade_add (s t : Multiset A) :
    (total A (s + t), (s + t).card) = (total A s, s.card) + (total A t, t.card) := by
  simp [total]
/-- The degree and lattice sum of a multiset monomial. -/
def grade : Multiset A →+ M × ℕ where
  toFun s := (total A s, s.card)
  map_zero' := grade_zero A
  map_add' := grade_add A
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

end PalomarLongEdges.ToricExchange

namespace PalomarLongEdges.ToricGeometry
open PalomarLongEdges.ToricExchange
/-- The character lattice in standard integral coordinates. -/
abbrev Lattice (n : ℕ) := Fin n → ℤ
/-- Its real scalar extension in standard coordinates. -/
abbrev Ambient (n : ℕ) := Fin n → ℝ
/-- The underlying ordinary coordinatewise integral-to-real inclusion. -/
def embedFn (n : ℕ) (z : Lattice n) : Ambient n := fun i => z i
/-- The coordinate inclusion preserves zero; separately compared. -/
theorem embedFn_zero (n : ℕ) : embedFn n 0 = 0 := by ext i; simp [embedFn]
/-- The coordinate inclusion preserves addition; separately compared. -/
theorem embedFn_add (n : ℕ) (z w : Lattice n) :
    embedFn n (z + w) = embedFn n z + embedFn n w := by ext i; simp [embedFn]
/-- The standard inclusion of the full lattice into its real vector space. -/
def embed (n : ℕ) : Lattice n →+ Ambient n where
  toFun := embedFn n
  map_zero' := embedFn_zero n
  map_add' := embedFn_add n
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
/-- The displayed doubled lattice contains zero; separately compared. -/
theorem twiceLattice_zero (n : ℕ) : ∃ w : Lattice n, (0 : Lattice n) = w + w := by
  exact ⟨0, by simp⟩
/-- The displayed doubled lattice is closed under addition; separately compared. -/
theorem twiceLattice_add (n : ℕ) {a b : Lattice n}
    (ha : ∃ u, a = u + u) (hb : ∃ v, b = v + v) :
    ∃ w, a + b = w + w := by
  rcases ha with ⟨u, rfl⟩
  rcases hb with ⟨v, rfl⟩
  exact ⟨u + v, by abel⟩
/-- The displayed doubled lattice is closed under negation; separately compared. -/
theorem twiceLattice_neg (n : ℕ) {a : Lattice n} (ha : ∃ u, a = u + u) :
    ∃ w, -a = w + w := by
  rcases ha with ⟨u, rfl⟩
  exact ⟨-u, by abel⟩
/-- The actual subgroup 2M of the coordinate lattice. Every proof field is
an explicitly named and separately compared elementary lattice law. -/
def twiceLattice (n : ℕ) : AddSubgroup (Lattice n) where
  carrier := {z | ∃ w, z = w + w}
  zero_mem' := twiceLattice_zero n
  add_mem' := twiceLattice_add n
  neg_mem' := twiceLattice_neg n

/-- The quotient group used in the original prescribed-parity statement. -/
abbrev ParityClass (n : ℕ) := Lattice n ⧸ twiceLattice n

/-- Send a lattice vector to its actual class modulo the doubled lattice. -/
def parityClass (n : ℕ) : Lattice n →+ ParityClass n :=
  QuotientAddGroup.mk' (twiceLattice n)
end PalomarLongEdges.ToricGeometry

namespace PalomarLongEdges
open PalomarLongEdges.ToricGeometry PalomarLongEdges.ToricExchange
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

end PalomarLongEdges
