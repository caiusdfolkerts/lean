module

public import Recovery.Unimodular.GraphicSectionRing.GraphicFanCoordinates
public import Recovery.Unimodular.GraphicSectionRing.CartierRingEquivalence

/-!
# Actual section rings for arbitrary Cartier divisors and invertible sheaves

The input is an arbitrary genuine fractional Cartier presentation on the
actual glued fan scheme. Normalization on its dense split torus supplies an
explicit rational unit; equality of fractional sheaves then identifies it
with invariant Cartier data. The resulting graded algebra equivalence is
proved, retaining the original degree and all global-section spaces.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing
open scoped BaseSections

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The actual rational unit used to normalize the original Cartier divisor. -/
def normalizationUnit (D : CartierData (F.fanScheme k)) : (F.fanScheme k).functionFieldˣ :=
  (torusCartierGenerator k n (F.fanScheme k) (F.splitTorusOpenMap k) D)⁻¹

/-- Normalization and the locally constructed fractional cocycle agree exactly. -/
theorem normalizedCartier_localCocycle (D : CartierData (F.fanScheme k)) :
    (F.normalizedCartier k D).localCocycle =
      D.localCocycle.scale (F.normalizationUnit k D) :=
  D.scale_localCocycle (F.normalizationUnit k D)

/-- No invariant presentation is imposed on the input Cartier divisor. -/
theorem normalizedCocycle_equivalent_fan (D : CartierData (F.fanScheme k)) :
    (D.localCocycle.scale (F.normalizationUnit k D)).toCartierData.Equivalent
      (F.fanCartierCocycle k F.isPure (F.cartierCoefficients k F.isPure D)).toCartierData := by
  rw [← F.normalizedCartier_localCocycle k D]
  let E := F.normalizedCartier k D
  exact E.localCocycle.toCartierData.equivalent_trans E _
    (E.equivalent_symm E.localCocycle.toCartierData E.equivalent_localCocycle)
    (F.normalizedCartier_equivalent_fanCartier k F.isPure D)

/-- The entire actual section ring of an arbitrary Cartier divisor is
identified with its invariant presentation, in every nonnegative degree. -/
def arbitraryCartierRingEquiv (D : CartierData (F.fanScheme k)) :
    ActualSections.sectionRing k D.localCocycle ≃ₐ[k]
      ActualSections.sectionRing k
        (F.fanCartierCocycle k F.isPure (F.cartierCoefficients k F.isPure D)) :=
  (ActualSections.scaleEquivalence k D.localCocycle (F.normalizationUnit k D)).trans
    (ActualSections.equivalenceOfEquivalent k _ _
      (F.normalizedCocycle_equivalent_fan k D))

/-- The complete degree formula makes the grading preservation explicit. -/
@[simp] theorem arbitraryCartierRingEquiv_coefficient (D : CartierData (F.fanScheme k))
    (p : ActualSections.sectionRing k D.localCocycle) (d : ℕ) :
    (F.arbitraryCartierRingEquiv k D p).val.coeff d =
      (F.normalizationUnit k D : (F.fanScheme k).functionField) ^ d * p.val.coeff d :=
  ActualSections.scaleEquivalence_coefficient k D.localCocycle (F.normalizationUnit k D) p d

/-- Ordinary tensor powers of the given Cartier sheaf, not powers of a
substitute invariant sheaf, give exactly the homogeneous section spaces. -/
def arbitraryCartierTensorPowerIso (D : CartierData (F.fanScheme k)) (d : ℕ) :
    tensorSheafPower D.sheaf d ≅ (D.localCocycle.pow d).sheaf :=
  D.tensorSheafNsmulIso d

namespace GraphicCoordinates

variable {F} (G : F.GraphicCoordinates)

/-- The actual section ring of every arbitrary Cartier divisor, with no
nefness or full-dimensionality assumptions, is the proved graphic algebra. -/
def arbitraryGraphicSectionRingEquiv (D : CartierData (F.fanScheme k)) :
    SectionAlgebra (G.constraints (F.cartierCoefficients k F.isPure D)) k ≃ₐ[k]
      ActualSections.sectionRing k D.localCocycle :=
  (G.actualSectionRingEquiv k (F.cartierCoefficients k F.isPure D)).trans
    (F.arbitraryCartierRingEquiv k D).symm

end GraphicCoordinates

/-- The section ring is constructed from the actual global sections of the
original ordinary invertible sheaf through its proved fractional presentation. -/
def invertibleSectionRing (M : (F.fanScheme k).Modules) (hM : IsInvertibleModule M) :
    Subalgebra k (AddMonoidAlgebra (F.fanScheme k).functionField ℕ) :=
  ActualSections.sectionRing k (invertibleFractionalPresentation M hM).localCocycle

/-- Every homogeneous piece is the genuine ordinary tensor power of M. -/
def invertibleTensorPowerIso (M : (F.fanScheme k).Modules)
    (hM : IsInvertibleModule M) (d : ℕ) :
    tensorSheafPower M d ≅ ((invertibleFractionalPresentation M hM).localCocycle.pow d).sheaf :=
  (invertibleFractionalPresentation M hM).tensorSheafNsmulIso d

/-- The genuine degree-d global sections inject into the independently
constructed section ring. Together with the finite coefficient expansion,
this realizes the ordinary direct sum of all tensor-power section spaces. -/
def invertibleHomogeneousSection (M : (F.fanScheme k).Modules)
    (hM : IsInvertibleModule M) (d : ℕ) :
    Γ(tensorSheafPower M d, ⊤) →ₗ[k] F.invertibleSectionRing k M hM :=
  (ActualSections.homogeneousSection k
    (invertibleFractionalPresentation M hM).localCocycle d).comp
      (BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM d)).toLinearMap

namespace GraphicCoordinates

variable {F} (G : F.GraphicCoordinates)

/-- This endpoint takes an arbitrary ordinary invertible sheaf on the actual
fan scheme. It does not assume an equivariant or invariant presentation. -/
def invertibleGraphicSectionRingEquiv (M : (F.fanScheme k).Modules)
    (hM : IsInvertibleModule M) :
    SectionAlgebra (G.constraints
      (F.cartierCoefficients k F.isPure (invertibleFractionalPresentation M hM))) k ≃ₐ[k]
      F.invertibleSectionRing k M hM :=
  G.arbitraryGraphicSectionRingEquiv k (invertibleFractionalPresentation M hM)

#print axioms arbitraryGraphicSectionRingEquiv
#print axioms invertibleGraphicSectionRingEquiv

end GraphicCoordinates

#print axioms normalizedCocycle_equivalent_fan
#print axioms arbitraryCartierRingEquiv_coefficient
#print axioms arbitraryCartierTensorPowerIso
#print axioms invertibleTensorPowerIso
#print axioms invertibleHomogeneousSection

end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.invertibleGraphicSectionRingEquiv
