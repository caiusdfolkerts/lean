module

public import ToricPower.AffineConeDerivedStage
public import ToricPower.ComplexAdjunction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# The affine coresolution as a homotopy localization

Let `P` consist of complexes contractible on every chosen affine open.
Every affine-open direct image is right orthogonal to `P`, by the actual
restriction adjunction on complexes. The finite cone-composition triangle
then puts each coresolution in this right orthogonal.

Once the iterated fiber is known to lie in `P`, the coaugmentation is a
`P`-equivalence. Its universal mapping property into the right orthogonal
shows that the two iterated coaugmentations are chain homotopic. This is
the coherence required by the absolute right-derived universal property.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Pretriangulated CochainComplex
open scoped ZeroObject

namespace ToricPower

universe u v w z

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]

/-- Actual contractibility on each chosen open, in the homotopy category. -/
def affineCoverContractible :
    ObjectProperty (HomotopyCategory (QCoh X) (.up ℤ)) := fun K =>
  ∀ i, IsZero (((quasicoherentRestriction (V i).ι).mapHomotopyCategory (.up ℤ)).obj K)

instance : (affineCoverContractible V).IsClosedUnderIsomorphisms where
  of_iso e h i :=
    (((quasicoherentRestriction (V i).ι).mapHomotopyCategory (.up ℤ)).mapIso e).isZero_iff.mp
      (h i)

instance : (affineCoverContractible V).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK i =>
    ((((quasicoherentRestriction (V i).ι).mapHomotopyCategory (.up ℤ)).commShiftIso n).app K).isZero_iff.mpr
      ((CategoryTheory.shiftFunctor _ n).map_isZero (hK i))⟩

instance : (affineCoverContractible V).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun i =>
    ((quasicoherentRestriction (V i).ι).mapHomotopyCategory (.up ℤ)).map_isZero
      (isZero_zero _)⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ i =>
    Triangle.isZero₂_of_isZero₁₃ _
      (((quasicoherentRestriction (V i).ι).mapHomotopyCategory (.up ℤ)).map_distinguished T hT)
      (h₁ i) (h₃ i))

/-- An affine-open direct image is right orthogonal to complexes
contractible on that open. This is the ordinary complex adjunction. -/
theorem affinePushComplex_rightOrthogonal (i : I)
    (K : CochainComplex (QCoh (V i).toScheme) ℤ) :
    (affineCoverContractible V).rightOrthogonal
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj K)) := by
  intro Z f hZ
  let L := quasicoherentRestriction (V i).ι
  let R := quasicoherentAffinePushforward (V i).ι
  let LC := L.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  let QU := HomotopyCategory.quotient (QCoh (V i).toScheme) (.up ℤ)
  let adj := complexAdjunction (quasicoherentOpenAdjunction (V i).ι) (.up ℤ)
  have hL : IsZero (QU.obj (LC.obj Z.as)) :=
    ((L.mapHomotopyCategoryFactors (.up ℤ)).app Z.as).isZero_iff.mp (hZ i)
  have hR : IsZero (Q.obj (RC.obj (LC.obj Z.as))) :=
    ((R.mapHomotopyCategoryFactors (.up ℤ)).app (LC.obj Z.as)).isZero_iff.mp
      ((R.mapHomotopyCategory (.up ℤ)).map_isZero hL)
  obtain ⟨g, rfl⟩ := Q.map_surjective f
  let g' := (adj.homEquiv Z.as K).symm g
  have hg : adj.unit.app Z.as ≫ RC.map g' = g := by
    exact (adj.homEquiv_unit Z.as K g').symm.trans
      ((adj.homEquiv Z.as K).apply_symm_apply g)
  rw [← hg, Q.map_comp, hR.eq_of_src (Q.map (RC.map g')) 0, comp_zero]

/-- Every finite coresolution stage lies in the same right orthogonal.
The proof retains the genuine cone-composition filtration. -/
theorem affineConeCoresolution_rightOrthogonal (l : List I)
    (K : CochainComplex (QCoh X) ℤ) :
    (affineCoverContractible V).rightOrthogonal
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        ((affineConeCoresolution V l).obj K)) := by
  let P := affineCoverContractible V
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  induction l with
  | nil =>
      exact P.rightOrthogonal.prop_of_isZero
        ((HomotopyCategory.isZero_quotient_obj_iff _).mpr
          ⟨mappingCone.homotopyToZeroOfId K⟩)
  | cons i l ih =>
      let S := openFiberStage V l
      let τ := (openLocalizationComplexUnit (V i).ι).app (S.1.obj K)
      let p := mappingCocone.fst τ
      let g := S.2.app K
      have hfirst : P.rightOrthogonal (Q.obj (mappingCone p)) := by
        let e := HomotopyCategory.isoOfHomotopyEquiv
          (ComplexCone.fiberProjectionConeHomotopyEquiv τ)
        apply (P.rightOrthogonal.prop_iff_of_iso e).mpr
        exact affinePushComplex_rightOrthogonal V i
          (((quasicoherentRestriction (V i).ι).mapHomologicalComplex (.up ℤ)).obj (S.1.obj K))
      exact P.rightOrthogonal.ext_of_isTriangulatedClosed₂
        (mappingConeCompTriangleh p g)
        (HomotopyCategory.mappingConeCompTriangleh_distinguished p g) hfirst ih

variable (l : List I)
  (hT : ∀ K : CochainComplex (QCoh X) ℤ,
    affineCoverContractible V
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj ((openFiberStage V l).1.obj K)))

include hT

/-- The actual coaugmentation is a local-homotopy equivalence. The
hypothesis is discharged by support removal for a finite affine cover. -/
theorem affineConeCoaugmentation_mem_trW (K : CochainComplex (QCoh X) ℤ) :
    (affineCoverContractible V).trW
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).map
        ((affineConeCoaugmentation V l).app K)) := by
  let P := affineCoverContractible V
  let π := (openFiberStage V l).2.app K
  exact ObjectProperty.trW.mk P
    (rot_of_distTriang (mappingCone.triangleh π)
      (HomotopyCategory.mappingCone_triangleh_distinguished π))
    (P.le_shift (1 : ℤ) _ (hT K))

/-- The two genuine iterated coaugmentations are homotopic. -/
def affineConeCoaugmentation_homotopy (K : CochainComplex (QCoh X) ℤ) :
    Homotopy
      ((affineConeCoresolution V l).map ((affineConeCoaugmentation V l).app K))
      ((affineConeCoaugmentation V l).app ((affineConeCoresolution V l).obj K)) := by
  let R := affineConeCoresolution V l
  let η := affineConeCoaugmentation V l
  let P := affineCoverContractible V
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  have hr : P.rightOrthogonal (Q.obj (R.obj (R.obj K))) :=
    affineConeCoresolution_rightOrthogonal V l (R.obj K)
  have hl : P.trW.isLocal (Q.obj (R.obj (R.obj K))) := by
    rwa [P.isLocal_trW]
  apply HomotopyCategory.homotopyOfEq
  apply (hl (Q.map (η.app K)) (affineConeCoaugmentation_mem_trW V l hT K)).injective
  simp only [← Q.map_comp]
  exact congrArg Q.map (η.naturality (η.app K)).symm

/-- Every additive functor identifies the two iterated coaugmentations
in its target derived category. -/
theorem affineConeCoaugmentation_coherence
    {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
    (H : QCoh X ⥤ D) [H.Additive] (K : CochainComplex (QCoh X) ℤ) :
    DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map
      ((affineConeCoresolution V l).map ((affineConeCoaugmentation V l).app K))) =
    DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map
      ((affineConeCoaugmentation V l).app ((affineConeCoresolution V l).obj K))) :=
  DerivedCategory.Q_map_eq_of_homotopy D
    (H.mapHomotopy (affineConeCoaugmentation_homotopy V l hT K))

end ToricPower

end
