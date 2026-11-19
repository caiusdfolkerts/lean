module

public import ToricPower.ToricCartierSectionsLinear
public import ToricPower.CechToricCover

/-! # Actual Cartier sections as a natural diagram of all characters

The coordinate isomorphism is natural for every cone face, before any
Čech or cohomology construction. All coefficients have their actual
base-field scalar action.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric

namespace ToricPower

universe v w

variable {N : Type} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {B : Type w} [Preorder B] (charts : B ⥤ fan.cones)

def toricChartSectionOpens : B ⥤ fan.algebraicRealization.Opens where
  obj b := (fan.affineToricChartι (charts.obj b)).opensRange
  map f := homOfLE (toricCechChartOpen_mono fan (charts.map f).le)

def toricCartierWeightDiagram (b : fan.Ray → ℤ) : Bᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj c := ModuleCat.of ℂ (ToricChartDivisorWeight fan b (charts.obj c.unop) →₀ ℂ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℂ ℂ
    (toricDivisorWeightFaceMap fan b (charts.map f.unop).le))
  map_id c := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro m r
    change Finsupp.mapDomain (toricDivisorWeightFaceMap fan b (charts.map (𝟙 c.unop)).le)
      (Finsupp.single m r) = Finsupp.single m r
    rw [Finsupp.mapDomain_single]
    congr 1
  map_comp {c d e} f g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro m r
    change Finsupp.mapDomain (toricDivisorWeightFaceMap fan b (charts.map (f ≫ g).unop).le)
        (Finsupp.single m r) =
      Finsupp.mapDomain (toricDivisorWeightFaceMap fan b (charts.map g.unop).le)
        (Finsupp.mapDomain (toricDivisorWeightFaceMap fan b (charts.map f.unop).le)
          (Finsupp.single m r))
    simp only [Finsupp.mapDomain_single]
    congr 1

variable [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)

local instance cartierSectionDiagramIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

def toricCartierSectionDiagram (b : fan.Ray → ℤ) : Bᵒᵖ ⥤ ModuleCat.{0} ℂ :=
  (toricChartSectionOpens fan charts).op ⋙
    (FiniteCover.schemeBasePresheaf ℂ fan.algebraicRealization).obj
      (invariantCartierDivisor fan nonempty regular b).sheaf

def toricCartierSectionDiagramIso (b : fan.Ray → ℤ) :
    toricCartierWeightDiagram fan charts b ≅
      toricCartierSectionDiagram fan charts regular b :=
  NatIso.ofComponents (fun c =>
    (toricDivisorSectionCoefficientsLinearEquiv fan nonempty regular b
      (charts.obj c.unop)).toModuleIso)
    (by
      intro c d f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      change toricDivisorSectionCoefficientsEquiv fan nonempty regular b (charts.obj d.unop)
        (Finsupp.mapDomain (toricDivisorWeightFaceMap fan b (charts.map f.unop).le) p) =
        (invariantCartierDivisor fan nonempty regular b).sheaf.presheaf.map
          (homOfLE (toricCechChartOpen_mono fan (charts.map f.unop).le)).op
          (toricDivisorSectionCoefficientsEquiv fan nonempty regular b (charts.obj c.unop) p)
      exact (toricDivisorSectionCoefficientsEquiv_restrict fan nonempty regular b
        (charts.map f.unop).le p).symm)

end ToricPower

end
