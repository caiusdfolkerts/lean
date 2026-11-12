module

public import ToricPower.SheafFramePullbackNaturality

/-!
# Comparisons of locally framed sheaves

The isomorphism obtained by comparing two frames is compatible with
restriction whenever the two frames are. The proof is categorical
cancellation, with the common structure-sheaf normalization retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower
universe u

/-- A common normalization cancels in the comparison of two frames. -/
theorem frameComparison_map {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U M N : C} {U' M' N' : D}
    (unit : U' ≅ F.obj U) (first : U ≅ M) (second : U ≅ N)
    (first' : U' ≅ M') (second' : U' ≅ N')
    (source : F.obj M ≅ M') (target : F.obj N ≅ N')
    (sourceFrame : unit ≪≫ F.mapIso first ≪≫ source = first')
    (targetFrame : unit ≪≫ F.mapIso second ≪≫ target = second') :
    source.symm ≪≫ F.mapIso (first.symm ≪≫ second) ≪≫ target =
      first'.symm ≪≫ second' := by
  rw [← sourceFrame, ← targetFrame]
  simp only [CategoryTheory.Functor.mapIso_trans, CategoryTheory.Functor.mapIso_symm,
    Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.refl_trans]

/-- The comparison of two ordinary restricted frames respects the
actual chart-refinement isomorphisms. -/
theorem frameComparison_restrict {A B : Scheme.{u}} (c : B ⟶ A)
    [IsOpenImmersion c] {M N : A.Modules} {M' N' : B.Modules}
    (first : 𝟙_ A.Modules ≅ M) (second : 𝟙_ A.Modules ≅ N)
    (first' : 𝟙_ B.Modules ≅ M') (second' : 𝟙_ B.Modules ≅ N')
    (source : M.restrict c ≅ M') (target : N.restrict c ≅ N')
    (sourceFrame : restrictModuleFrame c first ≪≫ source = first')
    (targetFrame : restrictModuleFrame c second ≪≫ target = second') :
    source.symm ≪≫ (restrictFunctor c).mapIso (first.symm ≪≫ second) ≪≫ target =
      first'.symm ≪≫ second' :=
  frameComparison_map (restrictFunctor c) (restrictUnitIso c).symm
    first second first' second' source target sourceFrame targetFrame

end ToricPower
