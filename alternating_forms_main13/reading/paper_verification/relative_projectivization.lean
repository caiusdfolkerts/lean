module

public import PaperVerification.ProjectivizationOfModuleSheaf

/-!
# Relative projectivization: the shared scheme construction

This file exposes short names for the recovered complete construction in
`ProjectivizationOfModuleSheaf`. Its scheme is glued from the actual
`Proj (Sym Γ(U,E))` over affine opens. Quasi-coherence proves the required
localization pullbacks; no chart or cohomology assertion is assumed.

The convention is the quotient convention: `Proj (Sym E)` parametrizes
line quotients of `E`. Projective lines in a locally free sheaf `T` use
this construction on `T`'s dual. All subsequent bundle constructions use
this single underlying definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.RelativeProjectivization

open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent]

abbrev chart := ProjectivizationOfModuleSheaf.chart E
abbrev gradedRestriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  ProjectivizationOfModuleSheaf.gradedRestriction E i
abbrev chartMap {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  ProjectivizationOfModuleSheaf.chartMap E i
abbrev chartDiagram := ProjectivizationOfModuleSheaf.diagram E
abbrev gluingData := ProjectivizationOfModuleSheaf.glueData E
abbrev projectivization := ProjectivizationOfModuleSheaf.projectivization E
abbrev toBase := ProjectivizationOfModuleSheaf.projection E
abbrev chartCover := ProjectivizationOfModuleSheaf.openCover E

/-- Restriction to any affine base open is the genuine projective
spectrum of the module of all sections over that open. -/
theorem chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((gluingData E).natTrans.app U) ((chartCover E).f U)
      U.val.ι (toBase E) :=
  ProjectivizationOfModuleSheaf.chart_isPullback E U

end PaperVerification.RelativeProjectivization
