module

public import ToricPower.CellularClosedSections
public import ToricPower.CellularConstantMap
public import ToricPower.InjectiveResolutionMap
public import ToricPower.ProjectiveSectionsFromResolution

/-! # Actual canonical sections of a closed constant coefficient diagram -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)

def closedConstantDiagram : B ⥤ ModuleCat.{u} k :=
  closedFaceExtension k P downward (constantDiagram k {b : B // P b})

def constantToClosed : constantDiagram k B ⟶ closedConstantDiagram k P downward :=
  (closedFaceUnit k P downward).app (constantDiagram k B)

def closedScalarMap : ModuleCat.of k k ⟶
    (constantSections k B).obj (closedConstantDiagram k P downward) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton k
    (constantDiagram k B ⟶ closedConstantDiagram k P downward)
    (constantToClosed k P downward))

theorem closedScalarMap_sectionComparison :
    closedScalarMap k P downward ≫
      (closedFaceSectionNatIso k P downward).hom.app (constantDiagram k {b : B // P b}) =
      constantScalarMap k {b : B // P b} := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change closedFaceSectionEquiv k P downward (constantDiagram k {b : B // P b})
    (a • constantToClosed k P downward) = a • 𝟙 _
  rw [map_smul]
  congr 1

variable [HasDerivedCategory (B ⥤ ModuleCat.{u} k)]

theorem closedProjectiveSectionMap_quasiIso_of_resolution
    (Q : ProjectiveResolution (constantDiagram k B))
    (J : InjectiveResolution (constantDiagram k {b : B // P b}))
    [QuasiIso (mappedSingleAugmentation (constantSections k {b : B // P b})
      (constantScalarMap k {b : B // P b}) J.ι)] :
    QuasiIso (scalarProjectiveSectionMap k Q (closedScalarMap k P downward)) := by
  haveI := mappedInjectiveSection_quasiIso (closedFaceExtensionFunctor k P downward) J
    (constantSections k B) (constantSections k {b : B // P b})
    (closedFaceSectionNatIso k P downward) (closedScalarMap k P downward)
    (constantScalarMap k {b : B // P b}) (closedScalarMap_sectionComparison k P downward)
  exact scalarProjectiveSectionMap_quasiIso_of_resolution k Q (closedScalarMap k P downward)
    (mappedInjectiveResolution (closedFaceExtensionFunctor k P downward) J)

end ToricPower.Cellular

end
