module

public import ToricPower.CellularCechNerve
public import ToricPower.CechConstantAugmentation
public import ToricPower.MappedSingleAugmentation

/-! # The canonical constant section augmentation and its actual nerve coordinates -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.FiniteCech

universe u
variable (k : Type u) [Field k] {B : Type u} [SemilatticeInf B]
  (P : B → Prop) (upward : Monotone P)

def retainedScalarSections : ModuleCat.of k k ⟶
    (retainedSections k P).obj (constantFieldDiagram k P) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton k
    (constantFieldDiagram k P ⟶ constantFieldDiagram k P) (𝟙 _))

theorem retainedScalarSections_map_app {F : {b : B // P b} ⥤ ModuleCat.{u} k}
    (f : constantFieldDiagram k P ⟶ F) (a r : k) (b : {b : B // P b}) :
    (((retainedSections k P).map f) (retainedScalarSections k P a)).app b r =
      f.app b (a*r) := rfl

theorem constantCotupleAugmentation_value (b : {b : B // P b}) (a : k)
    (t : UpperTuple b.val 0) :
    cotupleDualFunctional k P 0 b
      (((constantCotupleInjectiveResolution k P upward).ι.f 0).app b a)
        (ModuleCat.freeMk t) = a := by
  change (ModuleCat.freeDesc (M := ModuleCat.of k k)
    (↾fun _ : PUnit.{u+1} => a))
      ((ModuleCat.free k).map (↾fun _ : UpperTuple b.val 0 => PUnit.unit)
        (ModuleCat.freeMk t)) = a
  rw [ModuleCat.free_map_apply,ModuleCat.freeDesc_apply]
  rfl

def cotupleSectionAugmentation :
    (CochainComplex.single₀ (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶
      cotupleSectionComplex k P :=
  mappedSingleAugmentation (retainedSections k P) (retainedScalarSections k P)
    (constantCotupleInjectiveResolution k P upward).ι

theorem cotupleSectionAugmentation_zero :
    (cotupleSectionAugmentation k P upward).f 0 =
      retainedScalarSections k P ≫
        (retainedSections k P).map ((constantCotupleInjectiveResolution k P upward).ι.f 0) :=
  mappedSingleAugmentation_zero _ _ _

theorem cotupleSectionAugmentation_coordinates (a : k) (t : RetainedTuple P 0) :
    cotupleGlobalEvaluation k P upward 0
      ((cotupleSectionAugmentation k P upward).f 0 a) t = a := by
  rw [cotupleSectionAugmentation_zero,cotupleGlobalEvaluation_apply,ModuleCat.comp_apply]
  let f : constantFieldDiagram k P ⟶
      (retainedDiagramDual k P).obj (op (tupleModule k (B := B) 0)) :=
    (constantCotupleInjectiveResolution k P upward).ι.f 0
  have value := retainedScalarSections_map_app k P f a (1 : k) (retainedTupleCell P t)
  have compared := congrArg (fun x => cotupleDualFunctional k P 0
    (retainedTupleCell P t) x (ModuleCat.freeMk (tupleAtMeet t.val))) value
  rw [mul_one] at compared
  exact compared.trans (constantCotupleAugmentation_value k P upward _ a _)

end ToricPower.FiniteCech

namespace ToricPower.FiniteCech

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B]
  (P : B → Prop) (upward : Monotone P)

def cotupleSectionAugmentationAdd :
    (CochainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of k) ⟶
      ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (cotupleSectionComplex k P) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (forget₂ (ModuleCat k) AddCommGrpCat) (.up ℕ) 0).inv.app (ModuleCat.of k k) ≫
      ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (cotupleSectionAugmentation k P upward)

theorem cotupleSectionAugmentationAdd_zero :
    (cotupleSectionAugmentationAdd k P upward).f 0 =
      (forget₂ (ModuleCat k) AddCommGrpCat).map
        ((cotupleSectionAugmentation k P upward).f 0) :=
  mappedSingleAugmentation_core_zero _ _

theorem cotupleSectionNerveAugmentation :
    cotupleSectionAugmentationAdd k P upward ≫
      (cotupleSectionNerveIso k P upward).hom =
        negativeConstantChainMap k (fun b c : B => b ≤ c) P := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,cotupleSectionAugmentationAdd_zero,
    cotupleSectionNerveIso_hom_f]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  funext t
  rw [negativeConstantChainMap_zero]
  change cotupleGlobalEvaluation k P upward 0
    ((cotupleSectionAugmentation k P upward).f 0 a)
      ((retainedTupleNegativeEquiv P upward 0).symm t) = a
  exact cotupleSectionAugmentation_coordinates k P upward a _

variable [Finite B]
  [ContractibleSpace (BondalThomsen.ConvexNerveReducedCochainAcyclicity.incidenceRealization
    (fun b c : B => b ≤ c) P)]

theorem cotupleSectionAugmentation_quasiIso :
    QuasiIso (cotupleSectionAugmentation k P upward) := by
  haveI : QuasiIso (cotupleSectionAugmentationAdd k P upward ≫
      (cotupleSectionNerveIso k P upward).hom) := by
    rw [cotupleSectionNerveAugmentation]
    exact negativeConstantChainMap_quasiIso k _ _
  haveI : QuasiIso (cotupleSectionAugmentationAdd k P upward) :=
    quasiIso_of_comp_right _ (cotupleSectionNerveIso k P upward).hom
  haveI : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
      (forget₂ (ModuleCat k) AddCommGrpCat) (.up ℕ) 0).inv.app (ModuleCat.of k k) ≫
      ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (cotupleSectionAugmentation k P upward)) :=
    inferInstanceAs (QuasiIso (cotupleSectionAugmentationAdd k P upward))
  haveI : QuasiIso (((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex
      (.up ℕ)).map (cotupleSectionAugmentation k P upward)) :=
    quasiIso_of_comp_left
      ((HomologicalComplex.singleMapHomologicalComplex
        (forget₂ (ModuleCat k) AddCommGrpCat) (.up ℕ) 0).inv.app (ModuleCat.of k k)) _
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (cotupleSectionAugmentation k P upward) (forget₂ (ModuleCat k) AddCommGrpCat)).mp inferInstance

end ToricPower.FiniteCech

end
