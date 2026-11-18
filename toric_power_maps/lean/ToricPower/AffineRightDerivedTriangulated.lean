module

public import ToricPower.AffineRightDerivedResolved

/-!
# Exactness of the unbounded affine right-derived functor

Every derived arrow can be represented in the homotopy category. Apply
the actual finite affine coresolution to a representative chain map.
Its endpoints and mapping cone are in the homotopy right orthogonal,
so the genuine derived comparison is invertible on the entire triangle.
Transport of this distinguished triangle proves triangulated exactness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Functor CategoryTheory.Pretriangulated CochainComplex TopologicalSpace

namespace ToricPower

universe u v w z

section ArrowComparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- The canonical comparison between the two actual derived
localizations on a chain map, expressed as an isomorphism of arrows. -/
def quotientDerivedArrowIso {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    Arrow.mk (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f)) ≅
      Arrow.mk (DerivedCategory.Q.map f) :=
  Arrow.isoMk ((DerivedCategory.quotientCompQhIso A).app K)
    ((DerivedCategory.quotientCompQhIso A).app L)
    ((DerivedCategory.quotientCompQhIso A).hom.naturality f).symm

end ArrowComparison

local instance affineTriangulatedDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (l : List I) (hl : ∀ i, i ∈ l) (hV : IsOpenCover V)

include hl hV

/-- The actual coaugmentation identifies every original derived arrow
with its resolved arrow. -/
def affineResolvedArrowIso {K L : CochainComplex (QCoh X) ℤ} (f : K ⟶ L) :
    Arrow.mk (DerivedCategory.Q.map f) ≅
      Arrow.mk (DerivedCategory.Q.map ((affineConeCoresolution V l).map f)) := by
  letI := affineConeCoaugmentation_quasiIso V l hl hV K
  letI := affineConeCoaugmentation_quasiIso V l hl hV L
  refine Arrow.isoMk
    (asIso (DerivedCategory.Q.map ((affineConeCoaugmentation V l).app K)))
    (asIso (DerivedCategory.Q.map ((affineConeCoaugmentation V l).app L))) ?_
  change DerivedCategory.Q.map ((affineConeCoaugmentation V l).app K) ≫
      DerivedCategory.Q.map ((affineConeCoresolution V l).map f) =
    DerivedCategory.Q.map f ≫ DerivedCategory.Q.map ((affineConeCoaugmentation V l).app L)
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg DerivedCategory.Q.map ((affineConeCoaugmentation V l).naturality f).symm

variable {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]

/-- The canonical shift comparison of the actual unbounded right
derived functor, derived from its proved universal property. -/
def affineRightDerivedCommShift : (affineConeDerivedStage V H l).CommShift ℤ := by
  letI := affineConeDerivedStage_isRightDerivedFunctor V H l hl hV
  exact homotopyRightDerivedCommShift H (affineConeDerivedStage V H l)
    (affineRightDerivedUnit V H l)

/-- The finite affine right-derived functor carries every distinguished
triangle of unbounded quasicoherent complexes to a distinguished triangle. -/
theorem affineRightDerived_isTriangulated :
    letI := affineRightDerivedCommShift V l hl hV H
    (affineConeDerivedStage V H l).IsTriangulated := by
  let R := affineConeDerivedStage V H l
  let β := affineRightDerivedUnit V H l
  let α := homotopyRightDerivedComparison H R β
  letI := affineConeDerivedStage_isRightDerivedFunctor V H l hl hV
  letI := affineRightDerivedCommShift V l hl hV H
  letI : NatTrans.CommShift α ℤ := homotopyRightDerivedComparison_commShift H R β
  apply R.isTriangulated_of_leftExtension α
  intro K L f
  let a := (DerivedCategory.Qh (C := QCoh X)).mapArrow.objPreimage (Arrow.mk f)
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  let g : a.left.as ⟶ a.right.as := Q.preimage a.hom
  let rg := (affineConeCoresolution V l).map g
  let T := mappingCone.triangleh rg
  have hT : T ∈ distTriang (HomotopyCategory (QCoh X) (.up ℤ)) :=
    HomotopyCategory.mappingCone_triangleh_distinguished rg
  have h₁ := affineConeCoresolution_rightOrthogonal V l a.left.as
  have h₂ := affineConeCoresolution_rightOrthogonal V l a.right.as
  have h₃ := (affineCoverContractible V).rightOrthogonal.ext_of_isTriangulatedClosed₃
    T hT h₁ h₂
  refine ⟨T, hT,
    affineHomotopyRightDerivedComparison_isIso V l hl H T.obj₁ h₁,
    affineHomotopyRightDerivedComparison_isIso V l hl H T.obj₂ h₂,
    affineHomotopyRightDerivedComparison_isIso V l hl H T.obj₃ h₃, ⟨?_⟩⟩
  have e : Arrow.mk (DerivedCategory.Qh.map (Q.map g)) ≅ Arrow.mk f := by
    let e' := (DerivedCategory.Qh (C := QCoh X)).mapArrow.objObjPreimageIso (Arrow.mk f)
    change Arrow.mk (DerivedCategory.Qh.map a.hom) ≅ Arrow.mk f at e'
    simpa only [g, Functor.map_preimage] using e'
  exact quotientDerivedArrowIso rg ≪≫
    (affineResolvedArrowIso V l hl hV g).symm ≪≫
    (quotientDerivedArrowIso g).symm ≪≫ e

end ToricPower

end
