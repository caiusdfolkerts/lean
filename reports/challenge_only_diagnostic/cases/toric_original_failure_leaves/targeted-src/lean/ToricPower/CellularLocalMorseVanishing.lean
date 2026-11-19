module

public import ToricPower.CellularLocalMorse
public import ToricPower.ProjectiveSectionSingleComparison

/-! # Vanishing of the actual local Morse complex

These implications refer to the particular restriction comparison and
its signed mapping fiber. In the boundary case both the central stalk
and the full derived section complex vanish.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex

namespace ToricPower

theorem acyclic_of_derivedComplex_isZero
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : CochainComplex A ℤ) (zero : IsZero (DerivedCategory.Q.obj K)) : K.Acyclic := by
  intro q
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((DerivedCategory.homologyFunctorFactors A q).app K).isZero_iff.mp
    ((DerivedCategory.homologyFunctor A q).map_isZero zero)

namespace Cellular

universe u
variable (k : Type u) [Field k]
  {C H : Type u} [Category.{u} C] [Category.{u} H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} k) :=
  HasDerivedCategory.standard _

theorem localMorse_acyclic_of_comparison_quasiIso
    (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [QuasiIso ((localSectionComparison k j c arrows).app K)] :
    ((localMorseComplexFunctor k j c arrows).obj K).Acyclic := by
  let φ := (localSectionComparison k j c arrows).app K
  letI : QuasiIso φ := inferInstanceAs
    (QuasiIso ((localSectionComparison k j c arrows).app K))
  apply acyclic_of_derivedComplex_isZero
  exact Triangle.isZero₁_of_isIso₂
    (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ))
    (DerivedCategory.mappingCocone_triangle_distinguished φ)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map φ)))

theorem localMorse_acyclic_of_stalk_and_sections
    (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    (stalk : ((((evaluation C (ModuleCat.{u} k)).obj c).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (sections : ((localSectionComplexFunctor k j).obj K).Acyclic) :
    ((localMorseComplexFunctor k j c arrows).obj K).Acyclic := by
  haveI : QuasiIso ((localSectionComparison k j c arrows).app K) := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (stalk q).isZero_homology.isIso (sections q).isZero_homology _
  exact localMorse_acyclic_of_comparison_quasiIso k j c arrows K

/-- The canonical single-object transport retains the actual restricted
diagram, so a zero stalk and zero projective sections imply Morse vanishing. -/
theorem localMorse_single_acyclic_of_stalk_and_restrictedSections
    (F : C ⥤ ModuleCat.{u} k) (stalk : IsZero (F.obj c))
    (sections : ((projectiveCoefficientComplexFunctor k (𝟭 (H ⥤ ModuleCat.{u} k))
      (localSectionResolution k (H := H))).obj
        ((singleFunctor (H ⥤ ModuleCat.{u} k) 0).obj (j ⋙ F))).Acyclic) :
    ((localMorseComplexFunctor k j c arrows).obj
      ((singleFunctor (C ⥤ ModuleCat.{u} k) 0).obj F)).Acyclic := by
  apply localMorse_acyclic_of_stalk_and_sections k j c arrows
  · apply HomologicalComplex.acyclic_of_isZero
    exact ((HomologicalComplex.singleMapHomologicalComplex
      ((evaluation C (ModuleCat.{u} k)).obj c) (.up ℤ) 0).app F).isZero_iff.mpr
        ((singleFunctor (ModuleCat.{u} k) 0).map_isZero stalk)
  · exact projectiveCoefficientSingle_acyclic k (localDiagramRestriction k j)
      (localSectionResolution k (H := H)) F sections

/-- Literal zero coefficients throughout the face region imply vanishing
without any geometric assumption on that region. -/
theorem localMorse_single_acyclic_of_coefficients
    (F : C ⥤ ModuleCat.{u} k) (stalk : IsZero (F.obj c))
    (vanishes : ∀ h : H, IsZero (F.obj (j.obj h))) :
    ((localMorseComplexFunctor k j c arrows).obj
      ((singleFunctor (C ⥤ ModuleCat.{u} k) 0).obj F)).Acyclic := by
  apply localMorse_acyclic_of_stalk_and_sections k j c arrows
  · apply HomologicalComplex.acyclic_of_isZero
    exact ((HomologicalComplex.singleMapHomologicalComplex
      ((evaluation C (ModuleCat.{u} k)).obj c) (.up ℤ) 0).app F).isZero_iff.mpr
        ((singleFunctor (ModuleCat.{u} k) 0).map_isZero stalk)
  · apply localSectionComplex_acyclic_of_coefficients k j
    intro h
    apply HomologicalComplex.acyclic_of_isZero
    exact ((HomologicalComplex.singleMapHomologicalComplex
      ((evaluation C (ModuleCat.{u} k)).obj (j.obj h)) (.up ℤ) 0).app F).isZero_iff.mpr
        ((singleFunctor (ModuleCat.{u} k) 0).map_isZero (vanishes h))

end Cellular

end ToricPower

end
