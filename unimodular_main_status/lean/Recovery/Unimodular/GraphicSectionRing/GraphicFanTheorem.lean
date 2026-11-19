module

public import Recovery.Unimodular.GraphicSectionRing.GraphicIncidenceCoordinates
public import Recovery.Unimodular.GraphicSectionRing.GeometricPresentation
public import Recovery.Unimodular.GraphicSectionRing.GeometricAugmentation
public import Recovery.Unimodular.GraphicSectionRing.InvertibleSectionRingTensorProducts

/-!
# Proposition 6.10 for every actual integral graphic fan

The original primitive rays are assumed integrally isomorphic to actual
incidence columns in their literal integer span. The reduction to signed
coordinate differences is proved for arbitrary finite graphs, including
disconnected components and isolated vertices. The input line bundle is an
arbitrary ordinary invertible sheaf on the actual glued smooth complete fan
scheme. Its genuine section ring has a surjective degree-one polynomial
presentation, a squarefree quadratic initial ideal, and diagonal ordinary
augmentation Tor over every ground field. In particular every nef line bundle
satisfies the complete conclusion stated in the paper.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u v
namespace PaperVerification.ToricGeometry.SmoothCompleteFan.IntegralGraphicPresentation

open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing

variable {n : ℕ} {F : SmoothCompleteFan n} {V : Type v} [Fintype V]
  {H : SimpleGraph V} (P : F.IntegralGraphicPresentation H) (k : Type u) [Field k]

/-- Full graphic-fan clause of Proposition 6.10. All graph components, every
ordinary invertible sheaf and every coefficient-field universe are retained.
No coordinate-normalform, nefness, projectivity, full-dimensionality, or
additional section-finiteness premise is imposed. -/
theorem theorem_6_10_graphic_fan (M : (F.fanScheme k).Modules)
    (hM : IsInvertibleModule M) :
    let G := P.graphicCoordinates
    let C := G.constraints
      (F.cartierCoefficients k F.isPure (invertibleFractionalPresentation M hM))
    let e := G.invertibleGraphicSectionRingEquiv k M hM
    Function.Surjective (G.invertiblePolynomialMap k M hM) ∧
    (∃ m : MonomialOrder.{0,0} (Point C),
      initialIdeal m (RingHom.ker (G.invertiblePolynomialMap k M hM).toRingHom) =
        quadraticMonomialIdeal (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n) k ∧
      ∀ z ∈ forbiddenExponents (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n),
        z.degree = 2 ∧ ∀ i, z i ≤ 1) ∧
    PaperVerification.WeightedBar.HasDiagonalTor
      (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
      (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
      (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) :=
  P.graphicCoordinates.theorem_6_10_coordinate_fan k M hM

#print axioms theorem_6_10_graphic_fan

end PaperVerification.ToricGeometry.SmoothCompleteFan.IntegralGraphicPresentation

#check PaperVerification.ToricGeometry.SmoothCompleteFan.IntegralGraphicPresentation.theorem_6_10_graphic_fan
