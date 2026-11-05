module
public import PaperVerification.ToricFaceGeometry
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Int.Basic
@[expose] public section
/-!
# Faithful mathematical targets for the toric paper

The principal claims below are named propositions, not axioms and not claimed proofs.
The polytope, edges, smoothness, lattice lengths, sums, and kernel are all genuine
mathematical objects. No desired conclusion is included in a structure definition.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped Pointwise
open PaperVerification.ToricExchange

abbrev Lattice (n : ℕ) := Fin n → ℤ
abbrev Ambient (n : ℕ) := Fin n → ℝ

/-- The standard inclusion of the full lattice into its real vector space. -/
def embed (n : ℕ) : Lattice n →+ Ambient n where
  toFun z i := z i
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

theorem embed_injective (n : ℕ) : Function.Injective (embed n) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- A vector in an integral basis is primitive: it is not a nonunit integer
multiple of another lattice vector. -/
theorem lattice_basis_vector_primitive {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n)
    (k : ℤ) (z : Lattice n) (h : b i = k • z) : k = 1 ∨ k = -1 := by
  have hc : b.repr (k • z) i = 1 := by
    rw [← h]
    simp
  have hsmul : b.repr (k • z) = k • b.repr z := b.repr.map_smul k z
  rw [hsmul] at hc
  have hk : k * b.repr z i = 1 := by
    simpa only [Finsupp.smul_apply, smul_eq_mul] using hc
  exact Int.eq_one_or_neg_one_of_mul_eq_one hk

/-- The coordinate gcd of a primitive integral basis vector is exactly one. -/
theorem lattice_basis_vector_gcd_one {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    Finset.univ.gcd (fun j : Fin n => (b i j).natAbs) = 1 := by
  classical
  let g : ℕ := Finset.univ.gcd (fun j : Fin n => (b i j).natAbs)
  have hd (j : Fin n) : (g : ℤ) ∣ b i j :=
    Int.natCast_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ j))
  choose z hz using hd
  have hv : b i = (g : ℤ) • z := by funext j; exact hz j
  rcases lattice_basis_vector_primitive b i g z hv with hg | hg
  · exact_mod_cast hg
  · have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
    omega

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

/-- The endpoints of an actual edge are actual vertices of the polytope. -/
theorem edge_endpoints_extreme {v w : Ambient n} (h : P.IsEdge v w) :
    v ∈ P.carrier.extremePoints ℝ ∧ w ∈ P.carrier.extremePoints ℝ :=
  ⟨h.2.extremePoints_subset_extremePoints (left_endpoint_extreme_segment h.1),
    h.2.extremePoints_subset_extremePoints (right_endpoint_extreme_segment h.1)⟩

/-- Every vertex is one of the integral generators, regardless of whether the
original finite generating set contains redundant points. -/
theorem extreme_integral {v : Ambient n} (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ z ∈ P.generators, embed n z = v := by
  obtain ⟨z, hz, he⟩ := extremePoints_convexHull_subset hv
  exact ⟨z, hz, he⟩

/-- The integral-endpoint clause of `EdgesAtLeast` is automatic for a lattice polytope. -/
theorem edge_endpoints_integral {v w : Ambient n} (h : P.IsEdge v w) :
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w := by
  obtain ⟨hv, hw⟩ := P.edge_endpoints_extreme h
  obtain ⟨vZ, _, hvZ⟩ := P.extreme_integral hv
  obtain ⟨wZ, _, hwZ⟩ := P.extreme_integral hw
  exact ⟨vZ, wZ, hvZ, hwZ⟩

/-- Lattice length in standard coordinates, the gcd of the coordinate differences. -/
def latticeLength (v w : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i : Fin n => (w i - v i).natAbs)

/-- The gcd convention for lattice length agrees exactly with positive integer
multiplicity along a primitive basis direction, as used by the smoothness definition. -/
theorem latticeLength_basis_direction (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (k : ℕ) :
    latticeLength v (v + (k : ℤ) • b i) = k := by
  simp only [latticeLength, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_sub_cancel_left, Int.natAbs_mul, Int.natAbs_natCast]
  rw [Finset.gcd_mul_left, lattice_basis_vector_gcd_one]
  simp

/-- Every actual edge has integral endpoints and at least the stated lattice length. -/
def EdgesAtLeast (bound : ℕ) : Prop :=
  ∀ v w : Ambient n, P.IsEdge v w →
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w ∧
      bound ≤ latticeLength vZ wZ

/-- Requiring integral endpoints adds no hypothesis: the edge bound can be
stated equivalently by quantifying only over lattice endpoints. -/
theorem edgesAtLeast_iff (bound : ℕ) :
    P.EdgesAtLeast bound ↔ ∀ v w : Lattice n,
      P.IsEdge (embed n v) (embed n w) → bound ≤ latticeLength v w := by
  constructor
  · intro h v w hvw
    obtain ⟨v', w', hv, hw, hlen⟩ := h (embed n v) (embed n w) hvw
    have hv' := embed_injective n hv
    have hw' := embed_injective n hw
    simpa only [hv', hw'] using hlen
  · intro h v w hvw
    obtain ⟨vZ, wZ, hvZ, hwZ⟩ := P.edge_endpoints_integral hvw
    refine ⟨vZ, wZ, hvZ, hwZ, ?_⟩
    apply h
    simpa only [hvZ, hwZ] using hvw

/-- The coordinate length of a basis-direction edge satisfies precisely the
geometric edge bound. -/
theorem edge_basis_length_bound {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (v : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (k : ℕ)
    (hedge : P.IsEdge (embed n v) (embed n (v + (k : ℤ) • b i))) : bound ≤ k := by
  have h := (P.edgesAtLeast_iff bound).mp hbound v (v + (k : ℤ) • b i) hedge
  simpa only [latticeLength_basis_direction] using h

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

/-- The actual polynomial-kernel quadratic-generation assertion over a coefficient ring. -/
def QuadraticallyGenerated (R : Type*) [CommRing R] : Prop :=
  RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
    polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) R


/-- Every lattice polytope has a finite real affine-inequality presentation,
proved by eliminating its actual convex-combination weights. -/
theorem hasFiniteHalfspaces : HasFiniteHalfspaces P.carrier := by
  classical
  have h := finite_convexHull_hasFiniteHalfspaces (P.generators.image (embed n))
  simpa [carrier, Finset.coe_image] using h

/-- Proposition 2.1, with its literal face hypotheses, on every actual lattice
polytope and in every degree. The ideal equality uses precisely the paper's map. -/
theorem proposition2_1 (R : Type*) [CommRing R]
    (hidp : P.HasIDP) (hparity : FaceParity (embed n) P.carrier)
    (hadjoint : FaceAdjoint (embed n) P.carrier) :
    (∀ s t : Multiset (latticePoints (embed n) P.carrier),
      s.card = t.card → total (latticePoints (embed n) P.carrier) s =
        total (latticePoints (embed n) P.carrier) t →
      Connected (latticePoints (embed n) P.carrier) s t) ∧
      P.QuadraticallyGenerated R := by
  change _ ∧ RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
    polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) R
  change IntegerDecompositionProperty (embed n) P.carrier at hidp
  obtain ⟨ι, hι, H, hP⟩ := P.hasFiniteHalfspaces
  letI := hι
  rw [hP] at hidp hparity hadjoint ⊢
  have hmid := midpointDecomposition_of_convex_idp (embed n) H.region H.convex_region hidp
  have htriple := tripleReduction_of_face_parity_adjoint H (embed n) hparity hadjoint
  exact ⟨all_fibers_connected _ hmid htriple, paper_kernel_eq_quadrics _ R hmid htriple⟩

end LatticePolytope

/-- The exact polytope claim of Theorem 1.1 over an arbitrary field.
This is only a target proposition; no proof is asserted by defining it. -/
def Theorem1_1Statement (R : Type*) [Field R] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : LatticePolytope n,
    P.Smooth → P.EdgesAtLeast n → P.HasIDP ∧ P.QuadraticallyGenerated R

/-- The prescribed-parity geometric claim of Theorem 1.2. Representing a coset by
an arbitrary lattice vector is equivalent to quantifying over `M/2M`.
The correspondence with ample divisors uses the common normal fan dictionary. -/
def Theorem1_2PolytopeStatement : Prop :=
  ∀ n : ℕ, ∀ P Q : LatticePolytope n,
    P.Smooth → Q.Smooth → P.SameNormalFan Q → P.EdgesAtLeast n → Q.EdgesAtLeast n →
    ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
    ∀ parityRepresentative : Lattice n,
      ∃ a b : Lattice n, embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
        a + b = m ∧ SameParity a parityRepresentative

/-- The adjoint-multiplication geometric claim of Theorem 1.3, including both
inclusions in the stated equality of lattice-point sets. -/
def Theorem1_3PolytopeStatement : Prop :=
  ∀ n : ℕ, ∀ P Q : LatticePolytope n,
    P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast (n + 1) → Q.EdgesAtLeast (n + 1) →
    ∀ m : Lattice n,
      embed n m ∈ interior (P.minkowskiSum Q) ↔
      ∃ a b : Lattice n, embed n a ∈ P.carrier ∧ embed n b ∈ interior Q.carrier ∧ a + b = m

end PaperVerification.ToricGeometry
