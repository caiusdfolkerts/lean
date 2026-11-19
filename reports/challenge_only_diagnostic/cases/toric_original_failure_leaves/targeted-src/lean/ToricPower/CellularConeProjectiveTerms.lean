module

public import ToricPower.CellularConeResolution

/-! # Every term of the actual finite cone resolution is projective -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open scoped ZeroObject

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

private theorem mappingCone_projectiveTerm
    {D : Type*} [Category* D] [Abelian D]
    {K L : CochainComplex D ℤ} (f : K ⟶ L) (q : ℤ)
    [Projective (K.X (q+1))] [Projective (L.X q)] :
    Projective ((mappingCone f).X q) :=
  Projective.of_iso (homotopyCofiber.XIsoBiprod f q (q+1) rfl).symm inferInstance

/-- The finite cone construction retains genuinely projective terms in
every integer degree, even for an unbounded input complex. -/
theorem finiteConeResolution_term_projective (m : ℕ)
    (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) (q : ℤ) :
    Projective (((finiteConeResolution k m).functor.obj K).X q) := by
  induction m generalizing K q with
  | zero =>
    change Projective ((0 : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ).X q)
    exact ((HomologicalComplex.eval _ (.up ℤ) q).map_isZero (isZero_zero _)).projective
  | succ m ih =>
    let α := (complexResolutionArrow k (finiteConeResolution k m)).app K
    letI : Projective
        (((diagramSyzygyComplexFunctor k ⋙ (finiteConeResolution k m).functor).obj K).X
          (q+1)) := ih _ _
    letI : Projective (((diagramCoverComplexFunctor k).obj K).X q) :=
      diagramVectorCoverObj_projective k (K.X q)
    change Projective ((mappingCone α).X q)
    exact mappingCone_projectiveTerm α q

end ToricPower.Cellular

end
