module

public import ToricPower.QuasicoherentOpenAdjunction
public import ToricPower.SheafModuleHomGluing

/-!
# Open covers detect zero objects and derived isomorphisms

This file proves local detection for the actual unbounded derived category
of quasicoherent sheaves. Restriction is exact, so its homology is the
restriction of actual homology sheaves. Ordinary sheaf separatedness on
the given cover then detects their vanishing.

No boundedness, finite-dimensionality, or derived descent equivalence is
assumed. These results are the local checking step for a concrete Čech
coaugmentation or a diagonal reconstruction map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Pretriangulated TopologicalSpace
open scoped ZeroObject

namespace ToricPower

universe u v

variable {X : Scheme.{u}} {I : Type v} (U : I → X.Opens) (hU : IsOpenCover U)

include hU

/-- A module sheaf is zero if all its actual restrictions to a cover
are zero. The proof uses equality of the identity and zero morphisms. -/
theorem moduleSheaf_isZero_of_openCover (M : X.Modules)
    (hM : ∀ i, IsZero (M.restrict (U i).ι)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero _).2
  apply SheafModuleGluing.hom_ext_of_cover U hU
  intro i
  have hz : IsZero (M.over (U i)) := by
    apply IsZero.of_full_of_faithful_of_isZero (Scheme.Modules.overEquiv (U i)).functor
    exact ((Scheme.Modules.overFunctorEquiv (U i)).app M).isZero_iff.mpr (hM i)
  change 𝟙 (M.over (U i)) = 0
  exact (IsZero.iff_id_eq_zero _).1 hz

local instance openCoverQuasicoherentDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh Y) := HasDerivedCategory.standard _

/-- Actual open restrictions detect zero objects of the full unbounded
quasicoherent derived category. -/
theorem quasicoherentDerived_isZero_of_openCover (E : DerivedQCoh X)
    (hE : ∀ i, IsZero
      ((quasicoherentRestriction (U i).ι).mapDerivedCategory.obj E)) : IsZero E := by
  let K : CochainComplex (QCoh X) ℤ := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hH (n : ℤ) : IsZero (K.homology n) := by
    apply IsZero.of_full_of_faithful_of_isZero (quasicoherentInclusion X)
    apply moduleSheaf_isZero_of_openCover U hU
    intro i
    let F := quasicoherentRestriction (U i).ι
    let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
    have hQ : IsZero (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
      (F.mapDerivedCategory.mapIso e).isZero_iff.mpr (hE i)
    have hFK : IsZero (DerivedCategory.Q.obj FK) :=
      (F.mapDerivedCategoryFactors.app K).isZero_iff.mp hQ
    have hh : IsZero (FK.homology n) :=
      ((DerivedCategory.homologyFunctorFactors (QCoh (U i).toScheme) n).app FK).isZero_iff.mp
        ((DerivedCategory.homologyFunctor (QCoh (U i).toScheme) n).map_isZero hFK)
    have hFh : IsZero (F.obj (K.homology n)) :=
      ((K.sc n).mapHomologyIso F).isZero_iff.mp hh
    exact (quasicoherentInclusion (U i).toScheme).map_isZero hFh
  let z : K ⟶ (0 : CochainComplex (QCoh X) ℤ) := 0
  have hz : QuasiIso z := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hH n).isIso
      ((HomologicalComplex.homologyFunctor (QCoh X) (.up ℤ) n).map_isZero (isZero_zero _)) _
  letI := hz
  have hK : IsZero (DerivedCategory.Q.obj K) :=
    (asIso (DerivedCategory.Q.map z)).isZero_iff.mpr
      (DerivedCategory.Q.map_isZero (isZero_zero _))
  exact e.isZero_iff.mp hK

/-- A morphism of arbitrary quasicoherent derived objects is an
isomorphism once its actual open restrictions are isomorphisms. -/
theorem quasicoherentDerived_isIso_of_openCover
    {E F : DerivedQCoh X} (f : E ⟶ F)
    (hf : ∀ i, IsIso
      ((quasicoherentRestriction (U i).ι).mapDerivedCategory.map f)) : IsIso f := by
  obtain ⟨K, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hK : IsZero K := by
    apply quasicoherentDerived_isZero_of_openCover U hU
    intro i
    let G := (quasicoherentRestriction (U i).ι).mapDerivedCategory
    exact Triangle.isZero₃_of_isIso₁ (G.mapTriangle.obj T)
      (G.map_distinguished T hT) (hf i)
  exact (Triangle.isZero₃_iff_isIso₁ T hT).mp hK

end ToricPower

end
