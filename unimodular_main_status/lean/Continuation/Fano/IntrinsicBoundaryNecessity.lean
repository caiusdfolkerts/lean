module

public import Continuation.Fano.UniformRayNecessity
public import Continuation.Divisor.IntrinsicBoundaryFoundations
public import Continuation.Divisor.BoundaryFiniteness

/-!
# Necessity from the actual boundary of an arbitrary toric variety

The variety in this file is supplied independently. Its boundary vectors
are the orders of its actual rational characters at actual codimension-one
boundary points. No fan presentation or classification is an input.

Properness and smoothness give finiteness of those points. Proper global
characters give zero integral annihilator. The latter, together with the
paper's uniform unimodularity condition, supplies an integral basis and
proves regularity of every ordinary minor. Rational representability needs
only integrality of the vectors.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open scoped BigOperators Matroid

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance boundaryLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- There are finitely many actual codimension-one boundary components.
The argument uses the closed complement of the given nonempty torus open. -/
theorem finite_boundaryPrime : Finite T.BoundaryPrime := by
  classical
  letI : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : Nonempty T.torusOpen := T.torusOpen_dense.nonempty.to_subtype
  let C := {q : {q : X.left // Order.coheight q = 1} //
    (q : X.left) ∉ T.torusOpen}
  letI : Finite C :=
    (Unimodular.IntrinsicBoundary.finite_codimensionOne_outside
      T.torusOpen).to_subtype
  let f : T.BoundaryPrime → C := fun p ↦
    ⟨⟨p.val, p.property.1⟩, p.property.2⟩
  apply Finite.of_injective f
  intro p q hpq
  exact Subtype.ext (congrArg (fun x : C ↦ x.val.val) hpq)

/-- Vanishing of all genuine boundary orders forces the original
integral character exponent to vanish. No positivity is assumed. -/
theorem boundaryValuation_integral_annihilator
    (m : Lattice n)
    (hm : ∀ p : T.BoundaryPrime, ∑ i, T.boundaryValuation p i * m i = 0) :
    m = 0 := by
  apply (T.nonnegative_boundary_orders_iff_zero m).mp
  intro p
  rw [T.characterOrder_eq_integerPairing]
  change 0 ≤ ∑ i, T.boundaryValuation p i * m i
  exact le_of_eq (hm p).symm

/-- The ordinary vector matroid of all actual codimension-one boundary
valuations of the independently given variety. -/
def actualBoundaryMatroid : Matroid T.BoundaryPrime :=
  Unimodular.VectorMatroid.ofFamily (K := ℝ)
    (fun p ↦ Unimodular.embed (T.boundaryValuation p))

/-- Every ordinary minor of the actual boundary matroid is rationally
representable on its entire original ground. -/
theorem rational_of_actualBoundaryMinor {E : Type*}
    (M : Matroid E) [M.Finite] (f : M.E ↪ T.BoundaryPrime)
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m T.actualBoundaryMatroid) :
    Unimodular.RepresentationBridge.RepresentableOnGround ℚ M := by
  letI : Finite T.BoundaryPrime := T.finite_boundaryPrime
  letI : Fintype T.BoundaryPrime := Fintype.ofFinite _
  exact Unimodular.RepresentationBridge.integer_ray_minor_ground_representable
    T.boundaryValuation M f hminor

/-- Uniform unimodularity of the actual boundary valuations implies that
every ordinary minor is regular. The actual variety is arbitrary; no
auxiliary fan, ample divisor or classification theorem occurs here. -/
theorem regular_of_uniform_actualBoundaryMinor {E : Type*}
    (hU : Unimodular.IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      T.boundaryValuation)
    (M : Matroid E) [M.Finite] (f : M.E ↪ T.BoundaryPrime)
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m T.actualBoundaryMatroid) :
    Unimodular.RepresentationBridge.RegularOnGround M := by
  letI : Finite T.BoundaryPrime := T.finite_boundaryPrime
  letI : Fintype T.BoundaryPrime := Fintype.ofFinite _
  exact Unimodular.RepresentationBridge.regular_of_uniform_integer_ray_minor
    T.boundaryValuation hU T.boundaryValuation_integral_annihilator M f hminor

#print axioms finite_boundaryPrime
#print axioms boundaryValuation_integral_annihilator
#print axioms rational_of_actualBoundaryMinor
#print axioms regular_of_uniform_actualBoundaryMinor

end PaperVerification.ToricSchemes.SplitToricEmbedding
