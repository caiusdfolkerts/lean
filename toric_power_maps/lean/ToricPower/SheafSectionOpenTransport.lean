module

public import ToricPower.SheafChartSectionComparison

/-!
# Equality transport of actual open-section comparisons

Changing an open set by a proved equality preserves a natural comparison
of its actual sheaf section groups and the actual restriction maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace ToricPower
universe u
variable {X : Scheme.{u}}

/-- Equality transport of an actual section object. -/
def moduleSectionOpenIso (M : X.Modules) {U W : X.Opens} (equal : U = W) :
    Γ(M, U) ≅ Γ(M, W) :=
  eqToIso (congrArg (fun domain => M.presheaf.obj (op domain)) equal)

/-- A comparison of sections on a proved-equal presentation of an open set. -/
def moduleSectionComparisonTransport {M N : X.Modules} {U W : X.Opens} (equal : U = W)
    (comparison : Γ(M, W) ≅ Γ(N, W)) : Γ(M, U) ≅ Γ(N, U) :=
  moduleSectionOpenIso M equal ≪≫ comparison ≪≫ (moduleSectionOpenIso N equal).symm

/-- Restriction compatibility survives the equality transport. -/
theorem moduleSectionComparisonTransport_restrict {M N : X.Modules}
    {U U' W W' : X.Opens} (equal : U = W) (equal' : U' = W')
    (included : U' ≤ U) (included' : W' ≤ W)
    (large : Γ(M, W) ≅ Γ(N, W)) (small : Γ(M, W') ≅ Γ(N, W'))
    (compatible : large.hom ≫ N.presheaf.map (homOfLE included').op =
      M.presheaf.map (homOfLE included').op ≫ small.hom) :
    (moduleSectionComparisonTransport equal large).hom ≫
      N.presheaf.map (homOfLE included).op =
    M.presheaf.map (homOfLE included).op ≫
      (moduleSectionComparisonTransport equal' small).hom := by
  subst U
  subst U'
  simpa only [moduleSectionComparisonTransport, moduleSectionOpenIso, eqToIso_refl,
    Iso.refl_trans, Iso.refl_symm, Iso.trans_refl] using compatible

end ToricPower
