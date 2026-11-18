module

public import ToricPower.CellularLocalMorseVanishing
public import ToricPower.ProjectiveSectionSingleNaturality
public import ToricPower.CellularConstantSections
public import ToricPower.CellularConstantMap

/-! # The canonical local Morse map on constant coefficients

The particular restriction map is transported to the canonical scalar
augmentation. A coefficient comparison which is an isomorphism at the
central cell and throughout the cut region preserves its vanishing.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower

section Single
variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]
  (S : A ⥤ D) [S.Additive] {M N : A} (f : M ⟶ N) [IsIso (S.map f)]

theorem mapSingle_isIso_of_image_isIso :
    IsIso ((S.mapHomologicalComplex (.up ℤ)).map ((singleFunctor A 0).map f)) := by
  let e := HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0
  rw [← isIso_comp_right_iff _ (e.hom.app N)]
  have natural := e.hom.naturality f
  change (S.mapHomologicalComplex (.up ℤ)).map ((singleFunctor A 0).map f) ≫
      e.hom.app N = e.hom.app M ≫ (singleFunctor D 0).map (S.map f) at natural
  rw [natural]
  infer_instance
end Single

namespace Cellular

variable (k : Type) [Field k]
  {C H : Type} [Category C] [Category H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)

theorem localSectionComparison_single_quasiIso_of_scalar
    (F : C ⥤ ModuleCat k)
    [QuasiIso (scalarProjectiveSectionMap k
      (localSectionResolution k (H := H))
      ((initialCoefficientSectionNatTrans k j c arrows).app F))] :
    QuasiIso ((localSectionComparison k j c arrows).app
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj F)) := by
  have comparison := projectiveSingleSection_comparison k
    (localSectionResolution k (H := H)) (localDiagramRestriction k j) F
    ((evaluation C (ModuleCat k)).obj c)
    (initialCoefficientSectionNatTrans k j c arrows)
  haveI : QuasiIso (((localSectionComparison k j c arrows).app
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj F)) ≫
      (projectiveCoefficientSingleIso k (localDiagramRestriction k j)
        (localSectionResolution k (H := H)) F).hom) := by
    change QuasiIso ((NatTrans.mapHomologicalComplex
      (initialCoefficientSectionNatTrans k j c arrows) (.up ℤ)).app
        ((singleFunctor (C ⥤ ModuleCat k) 0).obj F) ≫
      (projectiveCoefficientComplexUnit k (localDiagramRestriction k j)
        (localSectionResolution k (H := H))).app
        ((singleFunctor (C ⥤ ModuleCat k) 0).obj F) ≫
      (projectiveCoefficientSingleIso k (localDiagramRestriction k j)
        (localSectionResolution k (H := H)) F).hom)
    rw [comparison]
    infer_instance
  exact quasiIso_of_comp_right _
    (projectiveCoefficientSingleIso k (localDiagramRestriction k j)
      (localSectionResolution k (H := H)) F).hom

/-- All actual face maps in a constant diagram give its scalar identity
section; this is equality of the particular natural transformations. -/
theorem initialCoefficientSection_constant :
    (initialCoefficientSectionNatTrans k j c arrows).app (constantDiagram k C) =
      constantScalarMap k H := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change k at a
  apply NatTrans.ext
  funext h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change k at r
  change r * a = a * r
  exact mul_comm r a

/-- Actual isomorphisms on the central coefficient and the entire cut
diagram transfer the particular section comparison, including its map. -/
theorem localSectionComparison_single_quasiIso_of_map
    {F G : C ⥤ ModuleCat k} (f : F ⟶ G)
    [IsIso (f.app c)] [IsIso ((localDiagramRestriction k j).map f)]
    [QuasiIso ((localSectionComparison k j c arrows).app
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj G))] :
    QuasiIso ((localSectionComparison k j c arrows).app
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj F)) := by
  let z := (singleFunctor (C ⥤ ModuleCat k) 0).map f
  have : IsIso (((evaluation C (ModuleCat k)).obj c).map f) :=
    inferInstanceAs (IsIso (f.app c))
  haveI : IsIso ((((evaluation C (ModuleCat k)).obj c).mapHomologicalComplex (.up ℤ)).map z) :=
    mapSingle_isIso_of_image_isIso ((evaluation C (ModuleCat k)).obj c) f
  haveI : IsIso (((localDiagramRestriction k j).mapHomologicalComplex (.up ℤ)).map z) :=
    mapSingle_isIso_of_image_isIso (localDiagramRestriction k j) f
  haveI : IsIso ((localSectionComplexFunctor k j).map z) :=
    inferInstanceAs (IsIso ((linearHomComplexFunctor k
      (projectiveCochain (localSectionResolution k (H := H)))).map
        (((localDiagramRestriction k j).mapHomologicalComplex (.up ℤ)).map z)))
  haveI : QuasiIso ((localSectionComparison k j c arrows).app _ ≫
      (localSectionComplexFunctor k j).map z) := by
    rw [← (localSectionComparison k j c arrows).naturality z]
    infer_instance
  exact quasiIso_of_comp_right _ ((localSectionComplexFunctor k j).map z)

end Cellular

namespace FiniteCech

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B] [Finite B]
  (P : B → Prop) (upward : Monotone P)
  {C : Type} [Category C] (j : {b : B // P b} ⥤ C) (c : C)
  (arrows : (Functor.const {b : B // P b}).obj c ⟶ j)
  [ContractibleSpace (BondalThomsen.ConvexNerveReducedCochainAcyclicity.incidenceRealization
    (fun b c : B => b ≤ c) P)]

include upward in
/-- Contractibility makes the literal local restriction map on constant
coefficients a quasi-isomorphism. -/
theorem constant_localSectionComparison_single_quasiIso :
    QuasiIso ((Cellular.localSectionComparison k j c arrows).app
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj (Cellular.constantDiagram k C))) := by
  haveI : QuasiIso (scalarProjectiveSectionMap k
      (Cellular.localSectionResolution k (H := {b : B // P b}))
      ((Cellular.initialCoefficientSectionNatTrans k j c arrows).app
        (Cellular.constantDiagram k C))) := by
    rw [Cellular.initialCoefficientSection_constant]
    exact constantProjectiveSectionMap_quasiIso k P upward
      (Cellular.localSectionResolution k (H := {b : B // P b}))
  exact Cellular.localSectionComparison_single_quasiIso_of_scalar k j c arrows _

end FiniteCech

end ToricPower

end
