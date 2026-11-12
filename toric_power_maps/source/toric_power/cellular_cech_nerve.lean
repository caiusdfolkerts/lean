module

public import ToricPower.CellularCechSections
public import ToricPower.DualAlternatingComplex
public import ToricPower.CechNegativeRelative

/-!
# Derived local-section terms and the actual retained-intersection nerve

The full global-section complex of the constructed injective resolution
is identified with the ordered nerve cochains. This is a chain-level
comparison, preserving every tuple and every alternating differential.
The scalar-linear comparison is established before forgetting scalars.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower.FiniteCech

universe u
variable (k : Type u) [Field k] {B : Type u} [SemilatticeInf B]
  (P : B → Prop) (upward : Monotone P)

/-- The actual ordinary section functor of the retained face diagram. -/
abbrev retainedSections : ({b : B // P b} ⥤ ModuleCat.{u} k) ⥤ ModuleCat.{u} k :=
  (linearCoyoneda k ({b : B // P b} ⥤ ModuleCat.{u} k)).obj
    (op (constantFieldDiagram k P))

/-- The genuine scalar-linear global-section complex of the full
injective tuple resolution. -/
def cotupleSectionComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  ((retainedSections k P).mapHomologicalComplex (.up ℕ)).obj (cotupleComplex k P)

def retainedTupleComplex : CochainComplex (ModuleCat.{u} k) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (retainedTupleCosimplicial k P upward)

/-- The whole tuple cochain complex is computed by the actual
injective resolution, with its scalar action and all maps. -/
def cotupleSectionComplexIso : cotupleSectionComplex k P ≅ retainedTupleComplex k P upward :=
  dualAlternatingComparisonIso (retainedDiagramDual k P) (tupleAugmented k).left
    (retainedSections k P) (retainedTupleCosimplicial k P upward)
    (cotupleGlobalCosimplicialIso k P upward)

theorem cotupleSectionComplexIso_hom_f (q : ℕ) :
    (cotupleSectionComplexIso k P upward).hom.f q =
      (cotupleGlobalEvaluation k P upward q).toModuleIso.hom :=
  dualAlternatingComparisonIso_hom_f _ _ _ _ _ q

end ToricPower.FiniteCech

namespace ToricPower.FiniteCech

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B]
  (P : B → Prop) (upward : Monotone P)

/-- A tuple meets the retained region exactly when its actual
intersection does; no approximate center test is used. -/
def retainedTupleNegativeEquiv (n : ℕ) :
    RetainedTuple P n ≃ NegativeSupportRelative.forbiddenTuple
      (fun b c : B => b ≤ c) P n where
  toFun t := ⟨t.val,tupleMeet t.val,t.property,tupleMeet_le t.val⟩
  invFun t := ⟨t.val,by
    obtain ⟨b,retained,contains⟩ := t.property
    exact upward ((le_tupleMeet_iff t.val b).mpr contains) retained⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal tuple-coordinate reindexing as an additive equivalence. -/
def retainedTupleNegativeCoefficients (n : ℕ) :
    (RetainedTuple P n → k) ≃+
      (NegativeSupportRelative.forbiddenTuple (fun b c : B => b ≤ c) P n → k) where
  toFun values t := values ((retainedTupleNegativeEquiv P upward n).symm t)
  invFun values t := values (retainedTupleNegativeEquiv P upward n t)
  left_inv values := by funext t; rfl
  right_inv values := by funext t; rfl
  map_add' := by intros; rfl

/-- Forgetting scalars leaves exactly the usual full nerve cochains. -/
def retainedTupleNegativeCosimplicialIso :
    retainedTupleCosimplicial k P upward ⋙ forget₂ (ModuleCat k) AddCommGrpCat ≅
      NegativeSupportRelative.negativeCosimplicial k (fun b c : B => b ≤ c) P :=
  NatIso.ofComponents (fun simplex =>
    (retainedTupleNegativeCoefficients k P upward simplex.len).toAddCommGrpIso)
    (by
      intro source target selection
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro values
      funext t
      rfl)

/-- The complete global-section complex is the literal ordered nerve
cochain complex, rather than only a cohomology-dimension match. -/
def cotupleSectionNerveIso :
    ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (cotupleSectionComplex k P) ≅
      NegativeSupportRelative.negativeComplex k (fun b c : B => b ≤ c) P :=
  ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).mapIso
      (cotupleSectionComplexIso k P upward) ≪≫
    (additiveAlternatingCofaceIso (forget₂ (ModuleCat k) AddCommGrpCat)
      (retainedTupleCosimplicial k P upward)).symm ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (retainedTupleNegativeCosimplicialIso k P upward)

theorem cotupleSectionNerveIso_hom_f (q : ℕ) :
    (cotupleSectionNerveIso k P upward).hom.f q =
      (forget₂ (ModuleCat k) AddCommGrpCat).map
        (cotupleGlobalEvaluation k P upward q).toModuleIso.hom ≫
      (retainedTupleNegativeCoefficients k P upward q).toAddCommGrpIso.hom := by
  simp only [cotupleSectionNerveIso,Iso.trans_hom,HomologicalComplex.comp_f,
    Functor.mapIso_hom,Functor.mapHomologicalComplex_map_f,
    cotupleSectionComplexIso_hom_f]
  change _ ≫ (𝟙 _ ≫ _) = _
  rw [Category.id_comp]
  rfl

end ToricPower.FiniteCech

end
