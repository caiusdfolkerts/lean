module

public import ToricPower.LinearDualHomology
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.Functor

/-!
# Exact scalar duality of actual cellular diagrams

Scalar duality reverses every actual incidence. It is exact for vector
spaces of arbitrary dimension, and therefore preserves the complete
homology of diagram complexes. No finite-dimensional double-dual
identification is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] (C : Type u) [Category.{u} C]

/-- Literal scalar duality reverses the original face diagram. -/
def diagramScalarDual : (Cᵒᵖ ⥤ ModuleCat.{u} k)ᵒᵖ ⥤ C ⥤ ModuleCat.{u} k :=
  (Functor.leftOpRightOpEquiv (C := C) (D := ModuleCat.{u} k)).functor ⋙
    (Functor.whiskeringRight C (ModuleCat.{u} k)ᵒᵖ (ModuleCat.{u} k)).obj (scalarDual k)

instance diagramScalarDual_additive : (diagramScalarDual k C).Additive where
  map_add {F G} f g := by
    apply NatTrans.ext
    funext c
    exact (scalarDual k).map_add (f := (f.unop.app (op c)).op) (g := (g.unop.app (op c)).op)

instance diagramScalarDual_limits : PreservesFiniteLimits (diagramScalarDual k C) := by
  letI : PreservesFiniteLimits (scalarDual k) :=
    (scalarDual k).preservesFiniteLimits_of_preservesHomology
  apply preservesFiniteLimits_of_evaluation
  intro c
  letI : PreservesFiniteLimits ((evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (op c)).op :=
    preservesFiniteLimits_op _
  change PreservesFiniteLimits
    (((evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (op c)).op ⋙ scalarDual k)
  infer_instance

instance diagramScalarDual_colimits : PreservesFiniteColimits (diagramScalarDual k C) := by
  letI : PreservesFiniteColimits (scalarDual k) :=
    (scalarDual k).preservesFiniteColimits_of_preservesHomology
  apply preservesFiniteColimits_of_evaluation
  intro c
  letI : PreservesFiniteColimits ((evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (op c)).op :=
    preservesFiniteColimits_op _
  change PreservesFiniteColimits
    (((evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (op c)).op ⋙ scalarDual k)
  infer_instance

instance diagramScalarDual_homology : (diagramScalarDual k C).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The full dual cochain complex, including every original differential. -/
def diagramScalarDualComplex (K : ChainComplex (Cᵒᵖ ⥤ ModuleCat.{u} k) ℕ) :
    CochainComplex (C ⥤ ModuleCat.{u} k) ℕ :=
  ((diagramScalarDual k C).mapHomologicalComplex _).obj K.op

/-- The contravariant chain map induced by an actual diagram chain map. -/
def diagramScalarDualMap {K L : ChainComplex (Cᵒᵖ ⥤ ModuleCat.{u} k) ℕ} (f : K ⟶ L) :
    diagramScalarDualComplex k C L ⟶ diagramScalarDualComplex k C K :=
  ((diagramScalarDual k C).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map f.op)

instance diagramScalarDualMap_quasiIso
    {K L : ChainComplex (Cᵒᵖ ⥤ ModuleCat.{u} k) ℕ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (diagramScalarDualMap k C f) := by
  unfold diagramScalarDualMap
  infer_instance

end ToricPower.Cellular

end
