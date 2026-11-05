module

public import Recovery.Unimodular.GraphicSectionRing.ArbitrarySectionRing
public import Recovery.Unimodular.GraphicSectionRing.Koszul
public import Recovery.Unimodular.FlagKoszul.AlgebraTransport

/-!
# Ordinary derived Tor of genuine geometric section rings

The actual graded Cartier ring, and hence the ring of every ordinary invertible
sheaf, is carried through the proved algebra isomorphism. The augmentation,
basis, multiplication coefficients and bar differential are transported by
that isomorphism; no quotient or associated graded algebra replaces the target.
The internal degree is the original section degree throughout.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.GraphicSectionRing.GeometricKoszul

open Unimodular.FlagKoszul
open PaperVerification.AugmentedAlgebraBasis

variable {n : ℕ} (C : Set (Constraint n)) (k : Type u) [Field k]
  {A : Type u} [Ring A] [Algebra k A] (e : SectionAlgebra C k ≃ₐ[k] A)

/-- The positive indices are only renamed into the coefficient field's universe. -/
abbrev Index := ULift.{u} (Positive (FlagModel.Relation C))

/-- The actual section basis, mapped through an actual algebra equivalence. -/
def basis : Module.Basis (Option (Index C)) k A :=
  BarReindex.basis (Equiv.ulift.symm : Positive (FlagModel.Relation C) ≃ Index C)
    (AlgebraTransport.basis e (FlagModel.basis C k))

def augmentation : A →ₐ[k] k := AlgebraTransport.augmentation e (sectionAugmentation C k)

def degree : Index C → ℕ := positiveDegree (FlagModel.Relation C) ∘ Equiv.ulift

 theorem basis_none : basis C k e none = 1 :=
  BarReindex.unit_transport Equiv.ulift.symm _
    (AlgebraTransport.unit_transport e (FlagModel.basis C k) (FlagModel.basis_none C k))

 theorem augmentation_basis : ∀ i, augmentation C k e (basis C k e (some i)) = 0 :=
  BarReindex.augmentation_transport Equiv.ulift.symm _ _
    (AlgebraTransport.augmentation_transport e (sectionAugmentation C k)
      (FlagModel.basis C k) (FlagModel.augmentation_basis C k))

 theorem product_degree : ∀ i j l,
    productCoefficients (basis C k e) i j l ≠ 0 → degree C l = degree C i + degree C j :=
  BarReindex.productDegree_transport Equiv.ulift.symm _ _
    (AlgebraTransport.productDegree_transport e (FlagModel.basis C k)
      (positiveDegree (FlagModel.Relation C)) (FlagModel.product_degree C k))

/-- Actual ordinary derived augmentation Tor vanishes off the diagonal, in
all homological and internal degrees, for a genuine isomorphic section algebra. -/
theorem hasDiagonalTor [Fintype (Point C)] :
    PaperVerification.WeightedBar.HasDiagonalTor (augmentation C k e) (basis C k e)
      (basis_none C k e) (augmentation_basis C k e) (degree C) (product_degree C k e) :=
  AlgebraTransport.hasDiagonalTor_ulift e (sectionAugmentation C k) (FlagModel.basis C k)
    (FlagModel.basis_none C k) (FlagModel.augmentation_basis C k)
    (positiveDegree (FlagModel.Relation C)) (FlagModel.product_degree C k)
    (positiveDegree_pos (FlagModel.Relation C)) (Koszul.section_reduced_cycle_is_boundary C)

#print axioms hasDiagonalTor

end Unimodular.GraphicSectionRing.GeometricKoszul

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing

variable {n : ℕ} {F : SmoothCompleteFan n} (G : F.GraphicCoordinates)
  (k : Type u) [Field k]

/-- The ordinary derived Tor theorem for every arbitrary actual Cartier
presentation. Finiteness is derived from fan completeness; it is not a premise. -/
theorem arbitraryCartier_hasDiagonalTor (D : CartierData (F.fanScheme k)) :
    let C := G.constraints (F.cartierCoefficients k F.isPure D)
    let e := G.arbitraryGraphicSectionRingEquiv k D
    PaperVerification.WeightedBar.HasDiagonalTor
      (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
      (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
      (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) := by
  letI := G.points_finite (F.cartierCoefficients k F.isPure D)
  letI := Fintype.ofFinite (Point (G.constraints (F.cartierCoefficients k F.isPure D)))
  exact GeometricKoszul.hasDiagonalTor _ k _

/-- The ordinary derived Tor theorem for an arbitrary invertible sheaf on
the actual smooth complete fan scheme, over an arbitrary coefficient field.
This includes every nef line bundle, with no additional positivity assumption. -/
theorem invertible_hasDiagonalTor (M : (F.fanScheme k).Modules)
    (hM : IsInvertibleModule M) :
    let C := G.constraints
      (F.cartierCoefficients k F.isPure (invertibleFractionalPresentation M hM))
    let e := G.invertibleGraphicSectionRingEquiv k M hM
    PaperVerification.WeightedBar.HasDiagonalTor
      (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
      (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
      (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) :=
  G.arbitraryCartier_hasDiagonalTor k (invertibleFractionalPresentation M hM)

#print axioms arbitraryCartier_hasDiagonalTor
#print axioms invertible_hasDiagonalTor

end PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

#check PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.invertible_hasDiagonalTor
