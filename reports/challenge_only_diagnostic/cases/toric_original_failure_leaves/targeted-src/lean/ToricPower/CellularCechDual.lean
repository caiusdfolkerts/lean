module

public import ToricPower.CellularCechInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The full injective Čech resolution of a constant face diagram

The resolution is the exact scalar dual of the actual ordered tuple
chain complex, restricted to an upward-closed region. Its terms are
identified with the literal coinduced tuple modules. Thus both the
quasi-isomorphism and injectivity are proved for the complete complex,
with its actual augmentation and all degrees retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u

/-- Duality commutes with a complex concentrated in degree zero. -/
def dualSingleZeroIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (Z : C) :
    (F.mapHomologicalComplex (.up ℕ)).obj ((ChainComplex.single₀ C).obj Z).op ≅
      (CochainComplex.single₀ D).obj (F.obj (op Z)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => by
      cases q with
      | zero => exact Iso.refl _
      | succ q => exact IsZero.iso (F.map_isZero (isZero_zero C).op) (isZero_zero D))
    (by
      intro i j _
      simp only [Functor.mapHomologicalComplex_obj_d,HomologicalComplex.op_d,
        HomologicalComplex.single_obj_d,op_zero,Functor.map_zero,zero_comp,comp_zero])

end ToricPower.Cellular

namespace ToricPower.FiniteCech

universe u
variable (k : Type u) [Field k] {B : Type u} [SemilatticeInf B] (P : B → Prop)

/-- The actual retained face inclusion. -/
def retainedRegionInclusion : {b : B // P b} ⥤ B where
  obj b := b.val
  map f := homOfLE f.le

/-- Restriction to the actual retained region. -/
def retainedDiagramRestriction :
    (B ⥤ ModuleCat.{u} k) ⥤ {b : B // P b} ⥤ ModuleCat.{u} k :=
  (Functor.whiskeringLeft _ _ _).obj (retainedRegionInclusion P)

instance retainedDiagramRestriction_additive : (retainedDiagramRestriction k P).Additive := by
  unfold retainedDiagramRestriction
  infer_instance

instance retainedDiagramRestriction_limits : PreservesFiniteLimits (retainedDiagramRestriction k P) := by
  unfold retainedDiagramRestriction
  infer_instance

instance retainedDiagramRestriction_colimits : PreservesFiniteColimits (retainedDiagramRestriction k P) := by
  unfold retainedDiagramRestriction
  infer_instance

/-- The actual dual-and-restrict functor. -/
def retainedDiagramDual : (Bᵒᵖ ⥤ ModuleCat.{u} k)ᵒᵖ ⥤ {b : B // P b} ⥤ ModuleCat.{u} k :=
  Cellular.diagramScalarDual k B ⋙ retainedDiagramRestriction k P

instance retainedDiagramDual_additive : (retainedDiagramDual k P).Additive := by
  unfold retainedDiagramDual
  infer_instance

instance retainedDiagramDual_homology : (retainedDiagramDual k P).PreservesHomology := by
  unfold retainedDiagramDual
  infer_instance

/-- A scalar functional on a free module is literally its function
of values on the original basis generators. -/
def freeDualFunctionEquiv (T : Type u) :
    ((ModuleCat.free k).obj T ⟶ ModuleCat.of k k) ≃ₗ[k] (T → k) where
  toFun φ := fun t => φ (ModuleCat.freeMk t)
  invFun values := ModuleCat.freeDesc (↾values)
  left_inv φ := by
    apply ModuleCat.free_hom_ext
    intro t
    exact ModuleCat.freeDesc_apply _ _
  right_inv values := by
    funext t
    exact ModuleCat.freeDesc_apply _ _
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The dual tuple term is isomorphic to the genuine coinduced
function diagram, compatibly with every face map. -/
def cotupleDualIso (n : ℕ) :
    (retainedDiagramDual k P).obj (op (tupleModule k (B := B) n)) ≅ cotupleModule k P n :=
  NatIso.ofComponents (fun b => (freeDualFunctionEquiv k (UpperTuple b.val n)).toModuleIso)
    (by
      intro b c f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change ((ModuleCat.free k).obj (UpperTuple b.val n) ⟶ ModuleCat.of k k) at φ
      funext t
      change φ ((tupleModule k n).map (homOfLE f.le : b.val ⟶ c.val).op
        (ModuleCat.freeMk t)) =
        φ (ModuleCat.freeMk (upperTupleRestrict (homOfLE f.le : b.val ⟶ c.val).op t))
      rw [tupleModule_map_freeMk])

/-- The complete actual cochain complex of coinduced tuple modules. -/
def cotupleComplex : CochainComplex ({b : B // P b} ⥤ ModuleCat.{u} k) ℕ :=
  ((retainedDiagramDual k P).mapHomologicalComplex _).obj (tupleComplex k (B := B)).op

theorem cotupleComplex_injective (upward : Monotone P) (n : ℕ) :
    Injective ((cotupleComplex k P).X n) :=
  Injective.of_iso (cotupleDualIso k P n).symm (cotupleModule_injective k P upward n)

/-- The augmented coefficient is the exact dual of the constant free
rank-one presheaf, before identifying it with the coefficient field. -/
def cotupleConstantDiagram : {b : B // P b} ⥤ ModuleCat.{u} k :=
  (retainedDiagramDual k P).obj (op (tupleAugmented k (B := B)).right)

/-- The genuine augmentation inherited from the checked anchor
contraction of the original ordered tuple resolution. -/
def cotupleAugmentation :
    (CochainComplex.single₀ ({b : B // P b} ⥤ ModuleCat.{u} k)).obj
      (cotupleConstantDiagram k P) ⟶ cotupleComplex k P :=
  (Cellular.dualSingleZeroIso (retainedDiagramDual k P) (tupleAugmented k).right).inv ≫
    ((retainedDiagramDual k P).mapHomologicalComplex _).map
      ((HomologicalComplex.opFunctor _ _).map (tupleAugmentation k (B := B)).op)

instance cotupleAugmentation_quasiIso : QuasiIso (cotupleAugmentation k P) := by
  unfold cotupleAugmentation
  infer_instance

/-- The literal full tuple complex is an injective resolution; no
unproved acyclicity or chosen dimension truncation is used. -/
def cotupleInjectiveResolution (upward : Monotone P) :
    InjectiveResolution (cotupleConstantDiagram k P) where
  cocomplex := cotupleComplex k P
  injective := cotupleComplex_injective k P upward
  ι := cotupleAugmentation k P

/-- The augmented diagram is exactly the constant coefficient field. -/
def cotupleConstantIso : cotupleConstantDiagram k P ≅
    (Functor.const {b : B // P b}).obj (ModuleCat.of k k) :=
  NatIso.ofComponents
    (fun _ => ((freeDualFunctionEquiv k PUnit.{u+1}).trans
      (LinearEquiv.funUnique PUnit.{u+1} k k)).toModuleIso)
    (by
      intro b c f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change ((ModuleCat.free k).obj PUnit.{u+1} ⟶ ModuleCat.of k k) at φ
      change φ ((ModuleCat.free k).map (𝟙 PUnit.{u+1}) (ModuleCat.freeMk PUnit.unit)) =
        φ (ModuleCat.freeMk PUnit.unit)
      rw [ModuleCat.free_map_apply])

/-- An injective resolution of the actual constant rank-one diagram. -/
def constantCotupleInjectiveResolution (upward : Monotone P) :
    InjectiveResolution ((Functor.const {b : B // P b}).obj (ModuleCat.of k k)) where
  cocomplex := cotupleComplex k P
  injective := cotupleComplex_injective k P upward
  ι := (CochainComplex.single₀ _).map (cotupleConstantIso k P).inv ≫ cotupleAugmentation k P

end ToricPower.FiniteCech

end
