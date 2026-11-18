module

public import Continuation.Runtime.IntrinsicAmpleEmbedding
public import Continuation.Runtime.ProjectiveAmpleCartier

/-!
# The first two clauses of Corollary 6.11 on the original toric scheme

The scheme and its dense equivariant split torus are independently specified.
Actual projectivity supplies an ordinary ample line bundle and hence the
proved reconstruction input. Deep monotonicity then produces integral graphic
coordinates on all original boundary valuations. No fan presentation, ample
divisor, graph presentation or anticanonical comparison is an input.

The ring conclusion quantifies every ordinary invertible sheaf, which includes
the nef sheaves in the paper. The ample conclusion concerns an actual closed
embedding and the original sheaf as its pullback of O(1), with the normal
homogeneous coordinate ring and quadratic geometric vanishing ideal of that
same embedding. These statements do not assert the higher Property N_p clause.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open Unimodular.NefBig Unimodular.GraphicSectionRing Unimodular.ActualVeryAmple
open scoped Classical

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    [X.left.IsProjectiveOver k]
    (T : SplitToricEmbedding k n X)

local instance intrinsicCorollaryLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- Projectivity supplies the auxiliary ample sheaf internally, independently
of every ordinary line bundle later quantified in the conclusion. -/
theorem exists_graphicBoundary_of_projective_deeplyMonotone
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = T.unitBoundaryDivisorPolytope) :
    ∃ H : SimpleGraph (Option (Fin n)),
      Nonempty (T.IntegralGraphicBoundaryPresentation H) := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  exact T.exists_graphicBoundary_of_deeplyMonotone A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA Q hQ hanti

/-- The displayed unit-boundary polytope is attached to the actual intrinsic
anticanonical sheaf. The equality of lattice-character sections is proved,
and the ordinary ample sheaf used for reconstruction is obtained internally. -/
theorem projective_unitBoundary_is_intrinsicAnticanonical :
    ∃ D : CartierData X.left,
      T.HasBoundaryCoefficients D (fun _ => 1) ∧
      Nonempty (D.sheaf ≅ (topDifferentialSheaf k X.left n).dual) ∧
      ∀ m : PaperVerification.ToricGeometry.Lattice n,
        T.intrinsicCharacter m ∈ D.sectionValueRange ⊤ ↔
          embed n m ∈ T.unitBoundaryDivisorPolytope := by
  obtain ⟨A, hA⟩ := exists_isAmpleModule_of_isProjectiveOver (X := X.left) k
  exact T.unitBoundary_is_intrinsicAnticanonical A.obj
    ((isInvertibleModule_iff_standard A.obj).mpr A.property) hA

/-- The actual section-ring clause of Corollary 6.11 on the original scheme.
The graph and the integral coordinates are derived once and work for every
ordinary invertible sheaf, without a Cartier presentation in the hypotheses. -/
theorem corollary_6_11_original_section_rings
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = T.unitBoundaryDivisorPolytope) :
    ∃ H : SimpleGraph (Option (Fin n)),
      ∃ P : T.IntegralGraphicBoundaryPresentation H,
        ∀ L : TauCeti.AlgebraicGeometry.InvertibleSheaf X.left,
          let hL := (isInvertibleModule_iff_standard L.obj).mpr L.property
          let D := invertibleFractionalPresentation L.obj hL
          let C := P.sectionConstraints D
          let e := P.graphicSectionRingEquiv D
          Function.Surjective (P.polynomialMap D) ∧
          (∃ m : MonomialOrder.{0,0} (Point C),
            initialIdeal m (RingHom.ker (P.polynomialMap D).toRingHom) =
              quadraticMonomialIdeal
                (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n) k ∧
            ∀ z ∈ forbiddenExponents
                (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n),
              z.degree = 2 ∧ ∀ i, z i ≤ 1) ∧
          PaperVerification.WeightedBar.HasDiagonalTor
            (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
            (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
            (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) := by
  obtain ⟨H, ⟨P⟩⟩ := T.exists_graphicBoundary_of_projective_deeplyMonotone Q hQ hanti
  refine ⟨H, P, ?_⟩
  intro L
  exact P.theorem_6_10_complete_toric L.obj
    ((isInvertibleModule_iff_standard L.obj).mpr L.property)

/-- The actual ample clause is stated on the same original scheme and for
every ordinary ample invertible sheaf. The ideal is the geometric vanishing
ideal of the displayed morphism, already proved equal to its section kernel. -/
theorem corollary_6_11_original_ample_embeddings
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = T.unitBoundaryDivisorPolytope) :
    ∀ L : TauCeti.AlgebraicGeometry.InvertibleSheaf X.left,
      IsAmpleModule L.obj →
        ∃ E : NormalQuadraticSectionEmbedding k X.left L.obj,
          VeryAmpleOverField k X.left L.obj ∧
          IsDomain (E.geometricCoordinateRing k X.left L.obj) ∧
          IsIntegrallyClosed (E.geometricCoordinateRing k X.left L.obj) ∧
          ∃ S : Set (MvPolynomial E.index k),
            E.geometricCoordinateIdeal k X.left L.obj = Ideal.span S ∧
              ∀ p ∈ S, p.IsHomogeneous 2 := by
  intro L hL
  exact T.corollary_6_11_original_ample_embedding Q hQ hanti L hL

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.projective_unitBoundary_is_intrinsicAnticanonical
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.corollary_6_11_original_section_rings
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.corollary_6_11_original_ample_embeddings

end
