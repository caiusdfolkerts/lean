module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import all Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Group.Subgroup.Ker
import all Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Subobject.Basic
import all Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
import all Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Limits.Final
import all Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import all Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.RingTheory.PicardGroup
import all Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Finiteness.Descent
import all Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.LinearAlgebra.Dual.BaseChange
import all Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Descent
import all Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import all Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.HomCongr
import all Mathlib.CategoryTheory.HomCongr
public import Mathlib.Topology.Sheaves.Forget
import all Mathlib.Topology.Sheaves.Forget
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import all Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.CommAlgCat.Basic
import all Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import all Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme -/

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

noncomputable section

/-!
# Scheme-theoretic kernels for PoincareBundle

The kernel is the fiber product over the identity section. Its universal
property identifies its points over every test object with the group
kernel, so infinitesimal points are retained.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- Postcomposition with a group-object morphism on all test objects. -/
def pointsMap (T : C) : (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := MonObj.one_comp f
  map_mul' x y := MonObj.mul_comp x y f

/-- The scheme-theoretic kernel object, defined as a fiber product. -/
abbrev kernelObject : C := pullback f η[B]

/-- The kernel inclusion. -/
def kernelInclusion : kernelObject f ⟶ A := pullback.fst f η[B]

instance : Mono (kernelInclusion f) := by
  have : Mono η[B] := ⟨fun _ _ _ => Subsingleton.elim _ _⟩
  constructor
  intro T x y h
  apply pullback.hom_ext
  · exact h
  · exact Subsingleton.elim _ _

/-- Its test-object points are exactly the kernel of postcomposition. -/
def kernelPointsEquiv (T : C) :
    (T ⟶ kernelObject f) ≃ (pointsMap f T).ker where
  toFun x := ⟨x ≫ kernelInclusion f, by
    change (x ≫ kernelInclusion f) ≫ f = 1
    rw [Category.assoc, kernelInclusion, pullback.condition]
    rw [← Category.assoc]
    change (x ≫ pullback.snd f η[B]) ≫ η[B] = toUnit T ≫ η[B]
    rw [Subsingleton.elim (x ≫ pullback.snd f η[B]) (toUnit T)]⟩
  invFun x := pullback.lift x.1 (toUnit T) x.2
  left_inv x := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · apply Subsingleton.elim
  right_inv x := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

/-- Kernel points form a presheaf of groups. -/
def kernelPointFunctor : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (pointsMap f T.unop).ker
  map {T U} a := GrpCat.ofHom {
    toFun x := ⟨a.unop ≫ x.1, by
      change (a.unop ≫ x.1) ≫ f = 1
      rw [Category.assoc, show x.1 ≫ f = 1 from x.2, MonObj.comp_one]⟩
    map_one' := by
      apply Subtype.ext
      exact MonObj.comp_one a.unop
    map_mul' x y := by
      apply Subtype.ext
      exact MonObj.comp_mul a.unop x.1 y.1 }
  map_id T := by
    ext x
    exact Category.id_comp x.1
  map_comp a b := by
    ext x
    exact Category.assoc b.unop a.unop x.1

/-- The fiber product represents the full group-valued kernel presheaf. -/
def kernelRepresentableBy :
    (kernelPointFunctor f ⋙ forget GrpCat).RepresentableBy (kernelObject f) where
  homEquiv := kernelPointsEquiv f _
  homEquiv_comp a x := by
    apply Subtype.ext
    exact Category.assoc a x (kernelInclusion f)

/-- The group structure on the scheme-theoretic kernel is constructed
from its represented group-valued functor. -/
@[instance_reducible]
def kernelGroup : GrpObj (kernelObject f) :=
  GrpObj.ofRepresentableBy _ (kernelPointFunctor f) (kernelRepresentableBy f)

attribute [local instance] kernelGroup

/-- The represented point identification respects the group operations. -/
def kernelPointsMulEquiv (T : C) :
    (T ⟶ kernelObject f) ≃* (pointsMap f T).ker :=
  ((yonedaGrpObjIsoOfRepresentableBy _ (kernelPointFunctor f)
    (kernelRepresentableBy f)).app (op T)).groupIsoToMulEquiv

/-- Inclusion of the kernel as a natural transformation of group presheaves. -/
def kernelPointInclusion : kernelPointFunctor f ⟶ yonedaGrpObj A where
  app T := GrpCat.ofHom (pointsMap f T.unop).ker.subtype
  naturality _ _ a := by
    ext x
    rfl

/-- The kernel inclusion constructed as a morphism of group objects. -/
def kernelInclusionAsGroup : Grp.mk (kernelObject f) ⟶ Grp.mk A :=
  yonedaGrpFullyFaithful.preimage
    ((yonedaGrpObjIsoOfRepresentableBy _ (kernelPointFunctor f)
      (kernelRepresentableBy f)).hom ≫ kernelPointInclusion f)

theorem kernelInclusionAsGroup_hom : (kernelInclusionAsGroup f).hom.hom = kernelInclusion f := by
  change (𝟙 (kernelObject f)) ≫ kernelInclusion f = kernelInclusion f
  exact Category.id_comp _

instance kernelInclusion_isMonHom : IsMonHom (kernelInclusion f) := by
  rw [← kernelInclusionAsGroup_hom f]
  infer_instance

/-- Kernels of morphisms between commutative group objects are commutative. -/
theorem kernelGroup_commutative [BraidedCategory C] [IsCommMonObj A] : IsCommMonObj (kernelObject f) := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (kernelPointsMulEquiv f T).injective
  rw [map_mul, map_mul, mul_comm]

/-- The defining kernel inclusion is annihilated by the original map. -/
theorem kernelInclusion_comp : kernelInclusion f ≫ f = 1 := by
  have h := (kernelPointsEquiv f (kernelObject f) (𝟙 _)).property
  change ((𝟙 (kernelObject f)) ≫ kernelInclusion f) ≫ f = 1 at h
  simpa only [Category.id_comp] using h

/-- A scheme-theoretic kernel as an actual subobject of its source. -/
def kernelSubobject : Subobject A := Subobject.mk (kernelInclusion f)

variable {D : C} [GrpObj D] (g : A ⟶ D) [IsMonHom g]

/-- Containment of kernels can be checked on all test objects. -/
theorem kernelSubobject_le_iff : kernelSubobject f ≤ kernelSubobject g ↔
    ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1 := by
  constructor
  · intro h T x hx
    let i := Subobject.ofMkLEMk (kernelInclusion f) (kernelInclusion g) h
    let y := (kernelPointsEquiv f T).symm ⟨x, hx⟩
    have hy : y ≫ kernelInclusion f = x := pullback.lift_fst _ _ _
    rw [← hy, ← Subobject.ofMkLEMk_comp h, Category.assoc, Category.assoc,
      kernelInclusion_comp g, MonObj.comp_one, MonObj.comp_one]
  · intro h
    let i := (kernelPointsEquiv g (kernelObject f)).symm
      ⟨kernelInclusion f, h _ _ (kernelInclusion_comp f)⟩
    exact Subobject.mk_le_mk_of_comm i (pullback.lift_fst _ _ _)

end

variable {S : Scheme.{u}} {A B : Over S} [GrpObj B] (f : A ⟶ B)

/-- The kernel square remains a pullback after forgetting to schemes. -/
theorem kernel_isPullback :
    IsPullback (kernelInclusion f).left (pullback.snd f η[B]).left f.left η[B].left :=
  (Over.forget S).map_isPullback (IsPullback.of_hasPullback f η[B])

/-- The structural map of the kernel is the second fiber-product projection. -/
theorem kernel_hom_eq_snd : (kernelObject f).hom = (pullback.snd f η[B]).left := by
  simpa using (Over.w (pullback.snd f η[B])).symm

/-- The scheme-theoretic kernel of a finite homomorphism is finite over the base. -/
theorem kernel_isFinite [IsFinite f.left] : IsFinite (kernelObject f).hom := by
  rw [kernel_hom_eq_snd f]
  exact MorphismProperty.of_isPullback (P := @IsFinite) (kernel_isPullback f) inferInstance

/-- The scheme-theoretic kernel of a flat homomorphism is flat over the base. -/
theorem kernel_flat [Flat f.left] : Flat (kernelObject f).hom := by
  rw [kernel_hom_eq_snd f]
  exact MorphismProperty.of_isPullback (P := @Flat) (kernel_isPullback f) inferInstance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair -/

/-! # Pair -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

noncomputable section

/-!
# The kernel-pair torsor isomorphism for PoincareBundle

Two points of a group-scheme quotient have the same image exactly when
their difference lies in its scheme-theoretic kernel. This is an actual
isomorphism between the corresponding fiber product and the product
with the kernel, including for nonreduced kernels.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The kernel element measuring the difference between two points in one fiber. -/
def difference : pullback f f ⟶ Scheme.kernelObject f :=
  (Scheme.kernelPointsEquiv f (pullback f f)).symm
    ⟨(pullback.fst f f)⁻¹ * pullback.snd f f, by
      change ((pullback.fst f f)⁻¹ * pullback.snd f f) ≫ f = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel]⟩

/-- The difference map has its expected inclusion in the original group. -/
theorem difference_comp_inclusion :
    difference f ≫ Scheme.kernelInclusion f =
      (pullback.fst f f)⁻¹ * pullback.snd f f :=
  pullback.lift_fst _ _ _

/-- A point and a kernel element give two points of the same fiber. -/
def kernelPairHom : A ⊗ Scheme.kernelObject f ⟶ pullback f f :=
  pullback.lift (fst _ _) ((fst _ _) * (snd _ _ ≫ Scheme.kernelInclusion f)) (by
    rw [MonObj.mul_comp, Category.assoc, Scheme.kernelInclusion_comp,
      MonObj.comp_one, mul_one])

@[simp]
theorem kernelPairHom_fst : kernelPairHom f ≫ pullback.fst f f = fst _ _ :=
  pullback.lift_fst _ _ _

@[simp]
theorem kernelPairHom_snd : kernelPairHom f ≫ pullback.snd f f =
    (fst _ _) * (snd _ _ ≫ Scheme.kernelInclusion f) :=
  pullback.lift_snd _ _ _

/-- Recover the first point and their difference. -/
def kernelPairInv : pullback f f ⟶ A ⊗ Scheme.kernelObject f :=
  lift (pullback.fst f f) (difference f)

@[simp]
theorem kernelPairInv_fst : kernelPairInv f ≫ fst _ _ = pullback.fst f f :=
  lift_fst _ _

@[simp]
theorem kernelPairInv_snd : kernelPairInv f ≫ snd _ _ = difference f :=
  lift_snd _ _

/-- The fiber relation is canonically the action relation of the full kernel scheme. -/
def kernelPairIso : A ⊗ Scheme.kernelObject f ≅ pullback f f where
  hom := kernelPairHom f
  inv := kernelPairInv f
  hom_inv_id := by
    apply hom_ext
    · simp only [Category.assoc, kernelPairInv_fst, kernelPairHom_fst, Category.id_comp]
    · apply (cancel_mono (Scheme.kernelInclusion f)).mp
      simp only [Category.assoc, kernelPairInv_snd, difference_comp_inclusion,
        MonObj.comp_mul, GrpObj.comp_inv, kernelPairHom_fst, kernelPairHom_snd,
        Category.id_comp, inv_mul_cancel_left]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, kernelPairHom_fst, kernelPairInv_fst, Category.id_comp]
    · rw [Category.assoc, kernelPairHom_snd, MonObj.comp_mul,
        kernelPairInv_fst, ← Category.assoc, kernelPairInv_snd,
        difference_comp_inclusion, Category.id_comp, mul_inv_cancel_left]

attribute [local instance] Scheme.kernelGroup

/-- The kernel-valued difference of any two equal-image test points. -/
def pointDifference {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    T ⟶ Scheme.kernelObject f :=
  pullback.lift x y h ≫ difference f

@[simp]
theorem pointDifference_comp_inclusion {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    pointDifference f x y h ≫ Scheme.kernelInclusion f = x⁻¹ * y := by
  rw [pointDifference, Category.assoc, difference_comp_inclusion,
    MonObj.comp_mul, GrpObj.comp_inv, pullback.lift_fst, pullback.lift_snd]

/-- The difference cocycle is the group law on the scheme-theoretic kernel. -/
theorem pointDifference_cocycle {T : C} (x y z : T ⟶ A)
    (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    pointDifference f x z (hxy.trans hyz) =
      pointDifference f x y hxy * pointDifference f y z hyz := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [MonObj.mul_comp, pointDifference_comp_inclusion,
    pointDifference_comp_inclusion, pointDifference_comp_inclusion]
  simp only [mul_assoc, mul_inv_cancel_left]

@[simp]
theorem pointDifference_self {T : C} (x : T ⟶ A) :
    pointDifference f x x rfl = 1 := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [pointDifference_comp_inclusion, MonObj.one_comp, inv_mul_cancel]

/-- Reversing a fiber relation inverts the corresponding kernel element. -/
theorem pointDifference_reverse {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    pointDifference f y x h.symm = (pointDifference f x y h)⁻¹ := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [GrpObj.inv_comp, pointDifference_comp_inclusion, pointDifference_comp_inclusion,
    mul_inv_rev, inv_inv]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization -/

/-! # Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization

noncomputable section

/-!
# Kernel-equivariant transport gives ordinary descent data

The construction uses points over every test object and the represented
scheme-theoretic kernel. In particular, it retains nonreduced kernels.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

attribute [local instance] Scheme.kernelGroup

/-- The kernel-valued difference carries the first point to the second. -/
theorem difference_translates {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    x * (Pair.pointDifference f x y h ≫ Scheme.kernelInclusion f) = y := by
  rw [Pair.pointDifference_comp_inclusion, mul_inv_cancel_left]

/-- The full kernel-valued difference commutes with change of test object. -/
theorem difference_naturality {T T' : C} (g : T' ⟶ T) (x y : T ⟶ A)
    (h : x ≫ f = y ≫ f) (x' y' : T' ⟶ A) (h' : x' ≫ f = y' ≫ f)
    (hx : g ≫ x = x') (hy : g ≫ y = y') :
    g ≫ Pair.pointDifference f x y h = Pair.pointDifference f x' y' h' := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [Category.assoc, Pair.pointDifference_comp_inclusion, MonObj.comp_mul,
    GrpObj.comp_inv, hx, hy, Pair.pointDifference_comp_inclusion]

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  (L : F.obj (.mk (op A)))

/-- The object pulled back to an arbitrary test point of the group object. -/
abbrev pointObject {T : C} (x : T ⟶ A) : F.obj (.mk (op T)) :=
  (F.map x.op.toLoc).toFunctor.obj L

/-- A kernel action on the pulled-back object, natural on all test objects.
The identities are the ordinary unit, action-composition, and base-change laws. -/
structure KernelLinearization where
  transport ⦃T : C⦄ (x y : T ⟶ A) (k : T ⟶ Scheme.kernelObject f)
    (_hk : x * (k ≫ Scheme.kernelInclusion f) = y) : pointObject F L x ⟶ pointObject F L y
  unit_compat ⦃T : C⦄ (x : T ⟶ A)
    (hx : x * ((1 : T ⟶ Scheme.kernelObject f) ≫ Scheme.kernelInclusion f) = x) :
    transport x x 1 hx = 𝟙 _
  mul_compat ⦃T : C⦄ (x y z : T ⟶ A) (k l m : T ⟶ Scheme.kernelObject f)
    (hx : x * (k ≫ Scheme.kernelInclusion f) = y)
    (hy : y * (l ≫ Scheme.kernelInclusion f) = z)
    (hz : x * (m ≫ Scheme.kernelInclusion f) = z) (hm : k * l = m) :
    transport x y k hx ≫ transport y z l hy = transport x z m hz
  pullback_compat ⦃T T' : C⦄ (g : T' ⟶ T)
    (x y : T ⟶ A) (k : T ⟶ Scheme.kernelObject f) (hk : x * (k ≫ Scheme.kernelInclusion f) = y)
    (x' y' : T' ⟶ A) (k' : T' ⟶ Scheme.kernelObject f)
    (hk' : x' * (k' ≫ Scheme.kernelInclusion f) = y')
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hkk : g ≫ k = k') :
    pullHom (transport x y k hk) g x' y' hx hy = transport x' y' k' hk'

/-- Equivariant transport along the actual kernel produces ordinary Čech descent data. -/
def KernelLinearization.toDescentData (D : KernelLinearization f F L) :
    F.DescentData (fun (_ : PUnit.{1}) => f) where
  obj _ := L
  hom T q _i₁ _i₂ x y hx hy :=
    D.transport x y (Pair.pointDifference f x y (hx.trans hy.symm))
      (difference_translates f x y (hx.trans hy.symm))
  pullHom_hom T' T g q q' hq _i₁ _i₂ x y hx hy x' y' hxx hyy := by
    apply D.pullback_compat
    exact difference_naturality f g x y _ x' y' _ hxx hyy
  hom_self T q _i x hx := by
    change D.transport x x (Pair.pointDifference f x x (hx.trans hx.symm)) _ = 𝟙 _
    simpa only [Pair.pointDifference_self] using
      D.unit_compat x (by rw [MonObj.one_comp, mul_one])
  hom_comp T q _i₁ _i₂ _i₃ x y z hx hy hz := by
    apply D.mul_compat
    exact (Pair.pointDifference_cocycle f x y z (hx.trans hy.symm) (hy.trans hz.symm)).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps -/

/-! # Action Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps

noncomputable section

/-!
# The actual kernel action and its unit and composition maps
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

attribute [local instance] Scheme.kernelGroup

/-- The source of a kernel-action arrow. -/
abbrev source : A ⊗ Scheme.kernelObject f ⟶ A := fst _ _

/-- Translation by the full scheme-theoretic kernel. -/
def action : A ⊗ Scheme.kernelObject f ⟶ A :=
  source f * (snd _ _ ≫ Scheme.kernelInclusion f)

omit [IsMonHom f] in
theorem action_pair {T : C} (x : T ⟶ A) (k : T ⟶ Scheme.kernelObject f) :
    lift x k ≫ action f = x * (k ≫ Scheme.kernelInclusion f) := by
  simp only [action, MonObj.comp_mul, source, lift_fst, lift_snd_assoc]

/-- The identity-action section. -/
def unitSection : A ⟶ A ⊗ Scheme.kernelObject f := lift (𝟙 A) 1

theorem unitSection_source : unitSection f ≫ source f = 𝟙 A := lift_fst _ _

theorem unitSection_action : unitSection f ≫ action f = 𝟙 A := by
  rw [unitSection, action_pair, MonObj.one_comp, mul_one]

/-- The first arrow in a composable pair of kernel actions. -/
abbrev firstStep : (A ⊗ Scheme.kernelObject f) ⊗ Scheme.kernelObject f ⟶ A ⊗ Scheme.kernelObject f := fst _ _

/-- The second arrow starts at the endpoint of the first action. -/
def secondStep : (A ⊗ Scheme.kernelObject f) ⊗ Scheme.kernelObject f ⟶ A ⊗ Scheme.kernelObject f :=
  lift (firstStep f ≫ action f) (snd _ _)

/-- The composite action multiplies the two kernel elements. -/
def productStep : (A ⊗ Scheme.kernelObject f) ⊗ Scheme.kernelObject f ⟶ A ⊗ Scheme.kernelObject f :=
  lift (firstStep f ≫ source f) ((firstStep f ≫ snd _ _) * snd _ _)

abbrev tripleSource := firstStep f ≫ source f
abbrev tripleMiddle := firstStep f ≫ action f
abbrev tripleTarget := secondStep f ≫ action f

omit [IsMonHom f] in
theorem secondStep_source : secondStep f ≫ source f = tripleMiddle f := lift_fst _ _

theorem productStep_source : productStep f ≫ source f = tripleSource f := lift_fst _ _

/-- The endpoint of a composite kernel action is the endpoint after the two actions. -/
theorem productStep_action : productStep f ≫ action f = tripleTarget f := by
  change productStep f ≫ action f = secondStep f ≫ action f
  rw [productStep, action_pair, MonObj.mul_comp, secondStep, action_pair]
  rw [action, MonObj.comp_mul, ← Category.assoc, mul_assoc]

omit [GrpObj A] [IsMonHom f] in
/-- Pairing a point and a kernel element commutes with every change of test object. -/
theorem pair_naturality {T T' : C} (g : T' ⟶ T) (x : T ⟶ A) (k : T ⟶ Scheme.kernelObject f) :
    g ≫ lift x k = lift (g ≫ x) (g ≫ k) := by
  apply hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd]

theorem unitSection_point {T : C} (x : T ⟶ A) :
    x ≫ unitSection f = lift x (1 : T ⟶ Scheme.kernelObject f) := by
  rw [unitSection, pair_naturality, Category.comp_id, MonObj.comp_one]

omit [GrpObj A] [IsMonHom f] in
theorem triple_firstStep {T : C} (x : T ⟶ A) (k l : T ⟶ Scheme.kernelObject f) :
    lift (lift x k) l ≫ firstStep f = lift x k := lift_fst _ _

omit [IsMonHom f] in
theorem triple_secondStep {T : C} (x : T ⟶ A) (k l : T ⟶ Scheme.kernelObject f) :
    lift (lift x k) l ≫ secondStep f = lift (x * (k ≫ Scheme.kernelInclusion f)) l := by
  rw [secondStep, pair_naturality, ← Category.assoc, triple_firstStep, action_pair, lift_snd]

theorem triple_productStep {T : C} (x : T ⟶ A) (k l : T ⟶ Scheme.kernelObject f) :
    lift (lift x k) l ≫ productStep f = lift x (k * l) := by
  rw [productStep, pair_naturality, ← Category.assoc, triple_firstStep, source, lift_fst,
    MonObj.comp_mul, ← Category.assoc, triple_firstStep, lift_snd, lift_snd]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom -/

/-! # Pull Hom -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

noncomputable section

/-!
# Elementary compatibility of pullback morphisms for PoincareBundle equivariant descent
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {A B D T T' : C} {L : F.obj (.mk (op A))} {M : F.obj (.mk (op B))}
  {N : F.obj (.mk (op D))}
  {x : T ⟶ A} {y : T ⟶ B} {z : T ⟶ D}

/-- Equal base morphisms give the same pullback morphism, independently of compatibility proofs. -/
theorem pullHom_congr
    (φ : (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (g g' : T' ⟶ T) (h : g = g') (x' : T' ⟶ A) (y' : T' ⟶ B)
    (hx : g ≫ x = x') (hy : g ≫ y = y')
    (hx' : g' ≫ x = x') (hy' : g' ≫ y = y') :
    pullHom φ g x' y' hx hy = pullHom φ g' x' y' hx' hy' := by
  subst g'
  rfl

/-- Pullback preserves composition when all target maps are specified. -/
theorem pullHom_comp
    (φ : (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (ψ : (F.map y.op.toLoc).toFunctor.obj M ⟶ (F.map z.op.toLoc).toFunctor.obj N)
    (g : T' ⟶ T) (x' : T' ⟶ A) (y' : T' ⟶ B) (z' : T' ⟶ D)
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z') :
    pullHom (φ ≫ ψ) g x' z' hx hz =
      pullHom φ g x' y' hx hy ≫ pullHom ψ g y' z' hy hz := by
  let ex := (Cat.Hom.toNatIso
    (F.mapComp' x.op.toLoc g.op.toLoc x'.op.toLoc (by aesop))).app L
  let ey := (Cat.Hom.toNatIso
    (F.mapComp' y.op.toLoc g.op.toLoc y'.op.toLoc (by aesop))).app M
  let ez := (Cat.Hom.toNatIso
    (F.mapComp' z.op.toLoc g.op.toLoc z'.op.toLoc (by aesop))).app N
  let G := (F.map g.op.toLoc).toFunctor
  change ex.hom ≫ G.map (φ ≫ ψ) ≫ ez.inv =
    (ex.hom ≫ G.map φ ≫ ey.inv) ≫ (ey.hom ≫ G.map ψ ≫ ez.inv)
  rw [G.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Pullback of an identity morphism is an identity morphism. -/
theorem pullHom_identity (g : T' ⟶ T) (x' : T' ⟶ A) (hx : g ≫ x = x') :
    pullHom (𝟙 ((F.map x.op.toLoc).toFunctor.obj L)) g x' x' hx hx = 𝟙 _ := by
  let ex := (Cat.Hom.toNatIso
    (F.mapComp' x.op.toLoc g.op.toLoc x'.op.toLoc (by aesop))).app L
  let G := (F.map g.op.toLoc).toFunctor
  change ex.hom ≫ G.map (𝟙 _) ≫ ex.inv = 𝟙 _
  erw [G.map_id, Category.id_comp, ex.hom_inv_id]

/-- Replacing the common base map by an equal map does not change a descent morphism. -/
theorem descentHom_base_congr {X Y : C} (f : X ⟶ Y)
    (D : F.DescentData (fun (_ : PUnit.{1}) => f))
    (q q' : T ⟶ Y) (hq : q = q') (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hx' : x ≫ f = q') (hy' : y ≫ f = q') :
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      D.hom q' (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx' hy' := by
  subst q'
  rfl

/-- Gluing isomorphisms compose even when each pair is presented with its own base map. -/
theorem descentIso_comp {X Y : C} (f : X ⟶ Y)
    (D : F.DescentData (fun (_ : PUnit.{1}) => f)) (x y z : T ⟶ X)
    (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    (D.iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y rfl hxy.symm).hom ≫
        (D.iso (y ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) y z rfl hyz.symm).hom =
      (D.iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x z rfl (hxy.trans hyz).symm).hom := by
  have hb := descentHom_base_congr f D (y ≫ f) (x ≫ f) hxy.symm y z
    rfl hyz.symm hxy.symm (hxy.trans hyz).symm
  exact (congrArg (fun m => D.hom (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      x y rfl hxy.symm ≫ m) hb).trans
    (D.hom_comp (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit)
      x y z rfl hxy.symm (hxy.trans hyz).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization -/

/-! # Global Kernel Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization

noncomputable section

/-!
# Transport from a global kernel-action linearization
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op A)))

attribute [local instance] Kernel.Scheme.kernelGroup

/-- An isomorphism over the actual kernel-action scheme, with the unit and action cocycle. -/
structure ActionLinearization where
  actionIso : (F.map (Kernel.ActionMaps.source f).op.toLoc).toFunctor.obj L ≅
    (F.map (Kernel.ActionMaps.action f).op.toLoc).toFunctor.obj L
  unit : pullHom actionIso.hom (Kernel.ActionMaps.unitSection f) (𝟙 A) (𝟙 A)
    (Kernel.ActionMaps.unitSection_source f) (Kernel.ActionMaps.unitSection_action f) = 𝟙 _
  cocycle :
    pullHom actionIso.hom (Kernel.ActionMaps.firstStep f) (Kernel.ActionMaps.tripleSource f) (Kernel.ActionMaps.tripleMiddle f) rfl rfl ≫
      pullHom actionIso.hom (Kernel.ActionMaps.secondStep f) (Kernel.ActionMaps.tripleMiddle f) (Kernel.ActionMaps.tripleTarget f)
        (Kernel.ActionMaps.secondStep_source f) rfl =
    pullHom actionIso.hom (Kernel.ActionMaps.productStep f) (Kernel.ActionMaps.tripleSource f) (Kernel.ActionMaps.tripleTarget f)
      (Kernel.ActionMaps.productStep_source f) (Kernel.ActionMaps.productStep_action f)

variable (D : ActionLinearization f F L)

/-- Restrict the global action isomorphism to a test point and its kernel translate. -/
def transport {T : C} (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hk : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) : Kernel.Linearization.pointObject F L x ⟶ Kernel.Linearization.pointObject F L y :=
  pullHom D.actionIso.hom (lift x k) x y (lift_fst _ _) ((Kernel.ActionMaps.action_pair f x k).trans hk)

/-- The global unit diagram implies identity transport over every test object. -/
theorem transport_unit {T : C} (x : T ⟶ A)
    (hx : x * ((1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f) = x) :
    GlobalKernelLinearization.transport f F L D x x 1 hx = 𝟙 _ := by
  have h0 : pullHom (pullHom D.actionIso.hom (Kernel.ActionMaps.unitSection f) (𝟙 A) (𝟙 A)
      (Kernel.ActionMaps.unitSection_source f) (Kernel.ActionMaps.unitSection_action f)) x x x
      (Category.comp_id x) (Category.comp_id x) = 𝟙 _ := by
    rw [D.unit]
    exact PullHom.pullHom_identity x x (Category.comp_id x)
  have h1 := pullHom_pullHom D.actionIso.hom (Kernel.ActionMaps.unitSection f) (𝟙 A) (𝟙 A) x x x
    (Kernel.ActionMaps.unitSection_source f) (Kernel.ActionMaps.unitSection_action f) (Category.comp_id x) (Category.comp_id x)
  have h2 := PullHom.pullHom_congr D.actionIso.hom (lift x (1 : T ⟶ Kernel.Scheme.kernelObject f))
    (x ≫ Kernel.ActionMaps.unitSection f) (Kernel.ActionMaps.unitSection_point f x).symm x x (lift_fst _ _)
    ((Kernel.ActionMaps.action_pair f x 1).trans hx)
    (by rw [Category.assoc, Kernel.ActionMaps.unitSection_source, Category.comp_id])
    (by rw [Category.assoc, Kernel.ActionMaps.unitSection_action, Category.comp_id])
  exact h2.trans (h1.symm.trans h0)

/-- Base-change compatibility of the test-object transport follows from pullback functoriality. -/
theorem transport_pullback {T T' : C} (g : T' ⟶ T)
    (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f) (hk : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y)
    (x' y' : T' ⟶ A) (k' : T' ⟶ Kernel.Scheme.kernelObject f)
    (hk' : x' * (k' ≫ Kernel.Scheme.kernelInclusion f) = y')
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hkk : g ≫ k = k') :
    pullHom (GlobalKernelLinearization.transport f F L D x y k hk) g x' y' hx hy =
      GlobalKernelLinearization.transport f F L D x' y' k' hk' := by
  have h1 := pullHom_pullHom D.actionIso.hom (lift x k) x y g x' y'
    (lift_fst _ _) ((Kernel.ActionMaps.action_pair f x k).trans hk) hx hy
  have hp : g ≫ lift x k = lift x' k' := by rw [Kernel.ActionMaps.pair_naturality, hx, hkk]
  have h2 := PullHom.pullHom_congr D.actionIso.hom (g ≫ lift x k) (lift x' k') hp x' y'
    (by rw [Category.assoc, Kernel.ActionMaps.source, lift_fst, hx])
    (by rw [Category.assoc, Kernel.ActionMaps.action_pair, hk, hy])
    (lift_fst _ _) ((Kernel.ActionMaps.action_pair f x' k').trans hk')
  exact h1.trans h2

/-- The global action cocycle gives composition of transport over every test object. -/
theorem transport_mul {T : C} (x y z : T ⟶ A) (k l m : T ⟶ Kernel.Scheme.kernelObject f)
    (hx : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) (hy : y * (l ≫ Kernel.Scheme.kernelInclusion f) = z)
    (hz : x * (m ≫ Kernel.Scheme.kernelInclusion f) = z) (hm : k * l = m) :
    GlobalKernelLinearization.transport f F L D x y k hx ≫ GlobalKernelLinearization.transport f F L D y z l hy =
      GlobalKernelLinearization.transport f F L D x z m hz := by
  let t : T ⟶ (A ⊗ Kernel.Scheme.kernelObject f) ⊗ Kernel.Scheme.kernelObject f := lift (lift x k) l
  have ha : t ≫ Kernel.ActionMaps.firstStep f = lift x k := Kernel.ActionMaps.triple_firstStep f x k l
  have hb : t ≫ Kernel.ActionMaps.secondStep f = lift y l :=
    (Kernel.ActionMaps.triple_secondStep f x k l).trans (congrArg (fun a => lift a l) hx)
  have hc : t ≫ Kernel.ActionMaps.productStep f = lift x m :=
    (Kernel.ActionMaps.triple_productStep f x k l).trans (congrArg (lift x) hm)
  have hs : t ≫ Kernel.ActionMaps.tripleSource f = x :=
    (Category.assoc t (Kernel.ActionMaps.firstStep f) (Kernel.ActionMaps.source f)).symm.trans
      ((congrArg (fun a => a ≫ Kernel.ActionMaps.source f) ha).trans (lift_fst x k))
  have hmid : t ≫ Kernel.ActionMaps.tripleMiddle f = y :=
    (Category.assoc t (Kernel.ActionMaps.firstStep f) (Kernel.ActionMaps.action f)).symm.trans
      ((congrArg (fun a => a ≫ Kernel.ActionMaps.action f) ha).trans ((Kernel.ActionMaps.action_pair f x k).trans hx))
  have ht : t ≫ Kernel.ActionMaps.tripleTarget f = z :=
    (Category.assoc t (Kernel.ActionMaps.secondStep f) (Kernel.ActionMaps.action f)).symm.trans
      ((congrArg (fun a => a ≫ Kernel.ActionMaps.action f) hb).trans ((Kernel.ActionMaps.action_pair f y l).trans hy))
  have H := congrArg (fun φ : Kernel.Linearization.pointObject F L (Kernel.ActionMaps.tripleSource f) ⟶
      Kernel.Linearization.pointObject F L (Kernel.ActionMaps.tripleTarget f) => pullHom φ t x z hs ht) D.cocycle
  rw [PullHom.pullHom_comp _ _ t x y z hs hmid ht] at H
  simpa only [GlobalKernelLinearization.transport, pullHom_pullHom, ha, hb, hc] using H

/-- A global linearization on the actual kernel-action scheme induces natural equivariant transport. -/
def toKernelLinearization : Kernel.Linearization.KernelLinearization f F L where
  transport := fun {_T} x y k hk => GlobalKernelLinearization.transport f F L D x y k hk
  unit_compat := fun {_T} x hx => transport_unit f F L D x hx
  mul_compat := fun {_T} x y z k l m hx hy hz hm => transport_mul f F L D x y z k l m hx hy hz hm
  pullback_compat := fun {_T _T'} g x y k hk x' y' k' hk' hx hy hkk =>
    transport_pullback f F L D g x y k hk x' y' k' hk' hx hy hkk

/-- The global kernel-action isomorphism produces ordinary descent data for the quotient map. -/
def toDescentData : F.DescentData (fun (_ : PUnit.{1}) => f) :=
  (toKernelLinearization f F L D).toDescentData

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles -/

/-! # Bundles -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

noncomputable section

/-!
# Line bundles for the PoincareBundle polarization descent construction

Line bundles here are actual sheaves of modules, locally isomorphic to
the structure sheaf. Pullback and its action on isomorphism classes are
constructed from the existing sheaf-of-modules pullback functor.
No descent, ampleness, or representability assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

/-- The structure sheaf, considered as a module over itself. -/
def unitLine (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Inverse image of open sets preserves the whole space, hence is final. -/
theorem opensMap_final {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final := by
  let F := TopologicalSpace.Opens.map f.base
  have : PreservesLimit (Functor.empty.{0} Y.Opens) F :=
    preservesTerminal_of_iso F
      (F.mapIso (terminalIsTerminal.uniqueUpToIso isTerminalTop) ≪≫
        eqToIso (show F.obj (⊤ : Y.Opens) = (⊤ : X.Opens) from by ext; simp [F]) ≪≫
        isTerminalTop.uniqueUpToIso terminalIsTerminal)
  infer_instance

/-- Pullback preserves the trivial line bundle. -/
def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (unitLine Y) ≅ unitLine X := by
  have : (SheafOfModules.pushforward
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have := opensMap_final f
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  let e : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf :=
    asIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- A line bundle is locally free of rank one, expressed by local
isomorphisms with the structure sheaf on Zariski open neighborhoods. -/
def IsLine {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ unitLine U)

theorem isLine_unit (X : Scheme.{u}) : IsLine (unitLine X) := by
  intro x
  exact ⟨⊤, trivial, ⟨pullbackUnitIso (⊤ : X.Opens).ι⟩⟩

theorem IsLine.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : IsLine M) (e : M ≅ N) : IsLine N := by
  intro x
  obtain ⟨U, hx, ⟨hU⟩⟩ := hM x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ hU⟩⟩

/-- Local trivializations of a line bundle pull back along any morphism
of schemes, including inseparable morphisms. -/
theorem IsLine.pullback {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : IsLine M) (f : X ⟶ Y) : IsLine ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨eU⟩⟩ := hM (f x)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso eU ≪≫
    pullbackUnitIso (f ∣_ U)

/-- A genuine algebraic line bundle with its local-freeness property. -/
structure LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  isLine : IsLine sheaf

namespace LineBundle

def trivial (X : Scheme.{u}) : LineBundle X := ⟨unitLine X, isLine_unit X⟩

def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) : LineBundle X :=
  ⟨(Scheme.Modules.pullback f).obj L.sheaf, L.isLine.pullback f⟩

/-- Isomorphism of the actual module sheaves, independent of choices
of local trivialization. -/
def isoSetoid (X : Scheme.{u}) : Setoid (LineBundle X) where
  r L M := Nonempty (L.sheaf ≅ M.sheaf)
  iseqv := ⟨fun L => ⟨Iso.refl L.sheaf⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨d⟩ => ⟨e ≪≫ d⟩⟩

end LineBundle

/-- Isomorphism classes of algebraic line bundles. The tensor product
group structure is not built into this definition. -/
def LineBundleClass (X : Scheme.{u}) := Quotient (LineBundle.isoSetoid X)

namespace LineBundleClass

def mk {X : Scheme.{u}} (L : LineBundle X) : LineBundleClass X := Quotient.mk _ L

def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : LineBundleClass Y → LineBundleClass X :=
  Quotient.map (LineBundle.pullback f) (fun _ _ ⟨e⟩ =>
    ⟨(Scheme.Modules.pullback f).mapIso e⟩)

@[simp]
theorem pullback_mk {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    LineBundleClass.pullback f (LineBundleClass.mk L) = LineBundleClass.mk (L.pullback f) := rfl

@[simp]
theorem pullback_id {X : Scheme.{u}} (L : LineBundleClass X) :
    LineBundleClass.pullback (𝟙 X) L = L := by
  induction L using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      exact ⟨(Scheme.Modules.pullbackId X).app L.sheaf⟩

theorem pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : LineBundleClass Z) : LineBundleClass.pullback (f ≫ g) L = LineBundleClass.pullback f (LineBundleClass.pullback g L) := by
  induction L using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      exact ⟨((Scheme.Modules.pullbackComp f g).app L.sheaf).symm⟩

end LineBundleClass

/-- The presheaf of isomorphism classes of algebraic line bundles.
Relative Picard functors additionally quotient by bundles from the base
and sheafify; neither operation is silently assumed here. -/
def lineBundleClassFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := LineBundleClass X.unop
  map f := ↾(LineBundleClass.pullback f.unop)
  map_id X := by ext L; exact LineBundleClass.pullback_id L
  map_comp f g := by ext L; exact LineBundleClass.pullback_comp g.unop f.unop L

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization -/

/-! # Kernel Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

noncomputable section

/-!
# Geometric line-bundle descent data from an actual kernel linearization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The actual module-sheaf pullback pseudofunctor on schemes. -/
def modulePullbacks : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

/-- Module sheaves on schemes over a fixed base, with their actual pullback functors. -/
def overModulePullbacks (S : Scheme.{u}) :
    Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat :=
  (Over.forget S).op.toPseudofunctor.comp modulePullbacks

theorem overModulePullbacks_map {S : Scheme.{u}} {T A : Over S} (x : T ⟶ A) :
    ((overModulePullbacks S).map x.op.toLoc).toFunctor = Scheme.Modules.pullback x.left := rfl

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)

/-- A line-bundle isomorphism on the actual kernel-action scheme with its unit and cocycle. -/
abbrev LineLinearization :=
  GlobalKernelLinearization.ActionLinearization f (overModulePullbacks S) L.sheaf

/-- The ordinary geometric descent datum constructed from the line-bundle linearization. -/
def lineDescentData (D : LineLinearization f L) :
    (overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f) :=
  GlobalKernelLinearization.toDescentData f (overModulePullbacks S) L.sheaf D

/-- The object on the cover is the given geometric line bundle. -/
theorem lineDescentData_obj (D : LineLinearization f L) :
    (lineDescentData f L D).obj PUnit.unit = L.sheaf := rfl

/-- Every equal-image pair of test schemes receives the actual geometric gluing isomorphism. -/
def lineGluingIso (D : LineLinearization f L) {T : Over S} (x y : T ⟶ A)
    (h : x ≫ f = y ≫ f) :
    (Scheme.Modules.pullback x.left).obj L.sheaf ≅ (Scheme.Modules.pullback y.left).obj L.sheaf :=
  (lineDescentData f L D).iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y rfl h.symm

/-- The geometric gluing maps satisfy the Čech composition law over a common base map. -/
theorem lineDescentData_comp (D : LineLinearization f L) {T : Over S}
    (q : T ⟶ B) (x y z : T ⟶ A)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    (lineDescentData f L D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (lineDescentData f L D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) y z hy hz =
      (lineDescentData f L D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x z hx hz :=
  (lineDescentData f L D).hom_comp q
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit) x y z hx hy hz

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent -/

/-! # Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent

noncomputable section

/-!
# Faithfully flat descent of invertible modules for PoincareBundle

The contraction map M* tensor M → R detects invertibility. For a finitely
presented module, flat base change commutes with its dual, so faithful
flatness detects invertibility of the contraction map. This is the
affine algebra needed for descent of algebraic line bundles.
-/

open TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Flat base change commutes with the dual of a finitely presented module. -/
def dualBaseChangeEquiv [Module.Flat R S] [Module.FinitePresentation R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (Module.FinitePresentation.isBaseChange_map R M R S).equiv ≪≫ₗ
    (AlgebraTensorModule.rid R S S).congrRight

@[simp]
theorem dualBaseChangeEquiv_tmul [Module.Flat R S] [Module.FinitePresentation R M]
    (s t : S) (φ : Module.Dual R M) (m : M) :
    dualBaseChangeEquiv R S M (s ⊗ₜ[R] φ) (t ⊗ₜ[R] m) =
      s * t * algebraMap R S (φ m) := by
  simp [dualBaseChangeEquiv, LinearEquiv.congrRight, LinearEquiv.arrowCongr,
    IsBaseChange.equiv_tmul, Algebra.smul_def, mul_assoc, mul_comm]

/-- Over the cover, the original contraction becomes the invertible
module's evaluation isomorphism after the canonical tensor identifications. -/
def evaluationAfterBaseChangeEquiv
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] :
    S ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[S] S :=
  AlgebraTensorModule.distribBaseChange R S (Module.Dual R M) M ≪≫ₗ
    TensorProduct.congr (dualBaseChangeEquiv R S M) (LinearEquiv.refl S (S ⊗[R] M)) ≪≫ₗ
    Module.Invertible.linearEquiv S (S ⊗[R] M)

@[simp]
theorem evaluationAfterBaseChangeEquiv_tmul
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)]
    (s : S) (φ : Module.Dual R M) (m : M) :
    evaluationAfterBaseChangeEquiv R S M (s ⊗ₜ[R] (φ ⊗ₜ[R] m)) =
      s * algebraMap R S (φ m) := by
  simp [evaluationAfterBaseChangeEquiv, Module.Invertible.linearEquiv]

/-- The base-changed contraction is the evaluation equivalence. -/
theorem evaluationAfterBaseChange_eq
    [Module.Flat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] :
    (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S S (contractLeft R M) =
        (evaluationAfterBaseChangeEquiv R S M).toLinearMap := by
  ext φ m
  simp [Algebra.smul_def]

/-- Invertibility of finitely presented modules descends along faithfully
flat ring maps. This asserts invertibility of the actual evaluation map. -/
theorem invertible_of_faithfullyFlat_baseChange
    [Module.FaithfullyFlat R S] [Module.FinitePresentation R M]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  constructor
  let c : (Module.Dual R M ⊗[R] M) →ₗ[R] R := {
    toFun := contractLeft R M
    map_add' := (contractLeft R M).map_add
    map_smul' := (contractLeft R M).map_smul
  }
  change Function.Bijective c
  have hreflect := @Module.FaithfullyFlat.lTensor_bijective_iff_bijective
    R S inferInstance inferInstance inferInstance
    (Module.Dual R M ⊗[R] M) R inferInstance inferInstance inferInstance inferInstance
    c inferInstance
  apply hreflect.mp
  have heq := evaluationAfterBaseChange_eq R S M
  have heval := (evaluationAfterBaseChangeEquiv R S M).bijective
  let F := AlgebraTensorModule.lTensor S S (contractLeft R M)
  let e := AlgebraTensorModule.rid R S S
  have hcomp (x : S ⊗[R] (Module.Dual R M ⊗[R] M)) :
      e (F x) = evaluationAfterBaseChangeEquiv R S M x :=
    LinearMap.congr_fun heq x
  change Function.Bijective F
  constructor
  · intro x y hxy
    apply heval.1
    rw [← hcomp x, ← hcomp y]
    exact congrArg e hxy
  · intro y
    obtain ⟨x, hx⟩ := heval.2 (e y)
    refine ⟨x, e.injective ?_⟩
    rw [hcomp x]
    exact hx

/-- On noetherian affine schemes, no finite-presentation hypothesis on
the descended module is needed: it follows by faithful flat descent of
finite generation. -/
theorem invertible_of_faithfullyFlat_baseChange_noetherian
    [IsNoetherianRing R] [Module.FaithfullyFlat R S]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  have : Module.Finite R M :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact invertible_of_faithfullyFlat_baseChange R S M

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent -/

/-! # Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent

noncomputable section

/-!
# Effective affine module descent for PoincareBundle

A descent datum is a coalgebra for the standard extension/restriction
of scalars comonad. Its counit and coassociativity fields are the descent
compatibility equations, not an assertion that a descended module exists.
The descended module is constructed using the proved faithfully flat
comonadicity theorem.
-/

open _root_.CategoryTheory _root_.ModuleCat
open TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- An S-module with the standard affine descent coaction. -/
abbrev ModuleDatum (f : R →+* S) :=
  (extendRestrictScalarsAdj f).toComonad.Coalgebra

/-- Faithfully flat module descent is an equivalence of categories. -/
def descentEquivalence (f : R →+* S) (hf : f.FaithfullyFlat) :
    ModuleCat.{u} R ≌ ModuleDatum f := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact (Comonad.comparison (extendRestrictScalarsAdj f)).asEquivalence

/-- The R-module obtained by effective descent of the supplied coaction. -/
def descendedModule (f : R →+* S) (hf : f.FaithfullyFlat) (D : ModuleDatum f) :
    ModuleCat.{u} R :=
  (descentEquivalence f hf).inverse.obj D

/-- The descent coaction, not only the underlying S-module, is recovered. -/
def descentDataIso (f : R →+* S) (hf : f.FaithfullyFlat) (D : ModuleDatum f) :
    (Comonad.comparison (extendRestrictScalarsAdj f)).obj (descendedModule f hf D) ≅ D :=
  (descentEquivalence f hf).counitIso.app D

/-- Base change of the constructed R-module recovers the original S-module. -/
def baseChangeIso (f : R →+* S) (hf : f.FaithfullyFlat) (D : ModuleDatum f) :
    (extendScalars f).obj (descendedModule f hf D) ≅ D.A :=
  (extendRestrictScalarsAdj f).toComonad.forget.mapIso (descentDataIso f hf D)

/-- Uniqueness of the descended module up to an isomorphism, with the
descent datum retained in the hypothesis. -/
theorem descendedModule_unique (f : R →+* S) (hf : f.FaithfullyFlat)
    (D : ModuleDatum f) (M : ModuleCat.{u} R)
    (e : (Comonad.comparison (extendRestrictScalarsAdj f)).obj M ≅ D) :
    Nonempty (M ≅ descendedModule f hf D) := by
  have : (Comonad.comparison (extendRestrictScalarsAdj f)).IsEquivalence :=
    (comonadicExtendScalars hf).eqv
  exact ⟨(Comonad.comparison (extendRestrictScalarsAdj f)).preimageIso
    (e ≪≫ (descentDataIso f hf D).symm)⟩

/-- Effective descent of a line module over a noetherian affine base:
the module constructed from the coaction is itself invertible. -/
theorem descendedModule_invertible
    [IsNoetherianRing R] (f : R →+* S) (hf : f.FaithfullyFlat)
    (D : ModuleDatum f) [Module.Invertible S D.A] :
    Module.Invertible R (descendedModule f hf D) := by
  let : Algebra R S := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  have : Module.Invertible S (S ⊗[R] (descendedModule f hf D)) :=
    Module.Invertible.congr (baseChangeIso f hf D).symm.toLinearEquiv
  exact LineDescent.invertible_of_faithfullyFlat_baseChange_noetherian
    R S (descendedModule f hf D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback -/

/-! # Tilde Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback

noncomputable section

/-!
# Affine pullback of module sheaves for PoincareBundle

The sheaf associated to extension of scalars is identified with the
geometric pullback of the associated sheaf. The construction compares
their adjunctions; it does not assume preservation of line bundles or
effectiveness of descent.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R S : CommRingCat.{u}}

/-- Taking sections over the whole spectrum for a sheaf of R-modules. -/
def sectionsFunctor (R : CommRingCat.{u}) :
    TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)

/-- Pushforward along an affine morphism commutes with global sections,
with the corresponding restriction of scalars. -/
def pushforwardSectionsIso (f : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars f.hom := by
  let e := pushforwardCompModulesSpecToSheafIso f
  let Γ := sectionsFunctor R
  refine NatIso.ofComponents (fun N => Γ.mapIso (e.app N)) ?_
  intro M N g
  exact congrArg (fun h => Γ.map h) (e.hom.naturality g)

/-- The tilde functor commutes with arbitrary affine base change. -/
def tildePullbackIso (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (pushforwardSectionsIso f).symm)

/-- A module trivialization after localization gives an actual line-bundle
trivialization on the associated principal open subscheme. -/
def basicOpenTrivialization (M : ModuleCat.{u} R) (r : R)
    (eLocal : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) :
    (Scheme.Modules.pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj
      (tilde M) ≅ Line.Bundles.unitLine
        (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)) := by
  let A := CommRingCat.of (Localization.Away r)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let i := basicOpenIsoSpecAway r
  let eModule : (ModuleCat.extendScalars f.hom).obj M ≅ ModuleCat.of A A := by
    have halg : f.hom.toAlgebra = inferInstanceAs (Algebra R (Localization.Away r)) := by
      exact toAlgebra_algebraMap
    have hloc : letI := f.hom.toAlgebra
        IsLocalization (.powers r) (Localization.Away r) := by
      rw [halg]
      infer_instance
    have htower : @IsScalarTower R (Localization.Away r) (LocalizedModule.Away r M)
        f.hom.toAlgebra.toSMul inferInstance inferInstance := by
      rw [halg]
      infer_instance
    letI : Algebra R (Localization.Away r) := f.hom.toAlgebra
    haveI : IsLocalization (.powers r) (Localization.Away r) := hloc
    haveI := htower
    exact ((IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) M)).equiv ≪≫ₗ eLocal).toModuleIso
  exact (Scheme.Modules.pullbackCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app
      (tilde M) ≪≫
    ((Scheme.Modules.pullbackComp i.hom (Spec.map f)).app (tilde M)).symm ≪≫
    (Scheme.Modules.pullback i.hom).mapIso ((tildePullbackIso f).app M) ≪≫
    (Scheme.Modules.pullback i.hom).mapIso
      ((tilde.functor A).mapIso eModule ≪≫ tildeSelf) ≪≫
    Line.Bundles.pullbackUnitIso i.hom

/-- Invertible modules give genuine algebraic line bundles on their spectra. -/
theorem isLine_tilde_of_invertible (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Line.Bundles.IsLine (tilde M) := by
  classical
  intro x
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R M
  let p : PrimeSpectrum R := x
  have hex : ∃ r ∈ s, r ∉ p.asIdeal := by
    by_contra! h
    have hle : Ideal.span (s : Set R) ≤ p.asIdeal := Ideal.span_le.mpr h
    rw [hs] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨r, hr, hxr⟩ := hex
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree r hr
  obtain ⟨eLocal⟩ := (Module.Invertible.free_iff_linearEquiv
    (R := Localization.Away r) (M := LocalizedModule.Away r M)).mp inferInstance
  exact ⟨PrimeSpectrum.basicOpen r, hxr, ⟨basicOpenTrivialization M r eLocal⟩⟩

/-- The line bundle associated to an invertible module. -/
def lineBundleOfInvertible (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Line.Bundles.LineBundle (Spec R) :=
  ⟨tilde M, isLine_tilde_of_invertible M⟩

/-- The algebraic line bundle obtained from affine line-module descent data. -/
def descendedLineBundle [IsNoetherianRing R] (f : R ⟶ S)
    (hf : f.hom.FaithfullyFlat) (D : Affine.Descent.ModuleDatum f.hom)
    [Module.Invertible S D.A] : Line.Bundles.LineBundle (Spec R) := by
  have := Affine.Descent.descendedModule_invertible f.hom hf D
  exact lineBundleOfInvertible (Affine.Descent.descendedModule f.hom hf D)

/-- Geometric pullback of the descended line bundle recovers the sheaf
associated with the line module on the cover. -/
def descendedLineBundlePullbackIso [IsNoetherianRing R] (f : R ⟶ S)
    (hf : f.hom.FaithfullyFlat) (D : Affine.Descent.ModuleDatum f.hom)
    [Module.Invertible S D.A] :
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLineBundle f hf D).sheaf ≅
      tilde D.A :=
  (tildePullbackIso f).app (Affine.Descent.descendedModule f.hom hf D) ≪≫
    (tilde.functor S).mapIso (Affine.Descent.baseChangeIso f.hom hf D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections -/

/-! # Pushforward Sections -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections

noncomputable section

/-!
# Global-section formulas for the actual affine direct-image comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R S : CommRingCat.{u}}

/-- The affine direct-image comparison retains the underlying global section. -/
theorem pushforwardSectionsIso_hom_apply (f : R ⟶ S) (M : (Spec S).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj M) :
    (TildePullback.pushforwardSectionsIso f).hom.app M
        (show (moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward (Spec.map f)).obj M) from m) =
      (show (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := S)).obj M) from m) := by
  rfl

/-- The inverse direct-image comparison likewise retains the underlying global section. -/
theorem pushforwardSectionsIso_inv_apply (f : R ⟶ S) (M : (Spec S).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj M) :
    (TildePullback.pushforwardSectionsIso f).inv.app M
        (show (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := S)).obj M) from m) =
      (show (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map f)).obj M) from m) := by
  rfl

variable {T : CommRingCat.{u}}

/-- Compare sections after two direct images, using the two affine comparison maps in succession. -/
def iteratedSectionsIso (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
        moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
      (TildePullback.pushforwardSectionsIso f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (TildePullback.pushforwardSectionsIso g)
      (ModuleCat.restrictScalars f.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T))
      (ModuleCat.restrictScalarsComp f.hom g.hom).symm

/-- Compare the same sections using the geometric composite morphism and one affine comparison. -/
def compositeSectionsIso (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
        moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars (f ≫ g).hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
        Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm)
      (moduleSpecΓFunctor (R := R)) ≪≫
    TildePullback.pushforwardSectionsIso (f ≫ g)

/-- The iterated comparison retains the actual global section. -/
theorem iteratedSectionsIso_hom_apply (f : R ⟶ S) (g : S ⟶ T) (M : (Spec T).Modules)
    (m : (moduleSpecΓFunctor (R := T)).obj M) :
    (iteratedSectionsIso f g).hom.app M
        (show ((Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
          moduleSpecΓFunctor (R := R)).obj M) from m) =
      (show (ModuleCat.restrictScalars (f ≫ g).hom).obj
        ((moduleSpecΓFunctor (R := T)).obj M) from m) := rfl

/-- The composite comparison retains the same actual global section. -/
theorem compositeSectionsIso_hom_apply (f : R ⟶ S) (g : S ⟶ T) (M : (Spec T).Modules)
    (m : (moduleSpecΓFunctor (R := T)).obj M) :
    (compositeSectionsIso f g).hom.app M
        (show ((Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
          moduleSpecΓFunctor (R := R)).obj M) from m) =
      (show (ModuleCat.restrictScalars (f ≫ g).hom).obj
        ((moduleSpecΓFunctor (R := T)).obj M) from m) := by
  change M.presheaf.map (𝟙 (op ⊤)) m = m
  rw [M.presheaf.map_id]
  rfl

/-- The affine direct-image/global-sections isomorphism is compatible with composition. -/
theorem sectionsIso_composition (f : R ⟶ S) (g : S ⟶ T) :
    compositeSectionsIso f g = iteratedSectionsIso f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (compositeSectionsIso_hom_apply f g M m).trans (iteratedSectionsIso_hom_apply f g M m).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate -/

/-! # Tilde Mate -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

noncomputable section

/-!
# The affine tilde/pullback comparison is the canonical adjunction mate
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Uniqueness of a left adjoint after changing its right adjoint is exactly the mates isomorphism. -/
theorem leftAdjointUniq_ofNatIsoRight {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : R₂ ≅ R₁) :
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e) = (conjugateIsoEquiv adj₂ adj₁).symm e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adj₁.homEquiv X (L₂.obj X)).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (adj₂.ofNatIsoRight e).unit.app X =
    adj₁.unit.app X ≫ R₁.map (((conjugateEquiv adj₂ adj₁).symm e.hom).app X)
  exact unit_conjugateEquiv_symm adj₂ adj₁ e.hom X

variable {R S : CommRingCat.{u}}

/-- The geometric affine pullback comparison has the canonical mate normalization. -/
theorem tildePullbackIso_eq_mate (f : R ⟶ S) :
    TildePullback.tildePullbackIso f =
      (conjugateIsoEquiv
        ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
        ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))).symm
        (TildePullback.pushforwardSectionsIso f).symm :=
  leftAdjointUniq_ofNatIsoRight _ _ _

/-- Equivalently, its inverse is the canonical left-adjoint composition isomorphism. -/
theorem tildePullbackIso_symm_eq_compIso (f : R ⟶ S) :
    (TildePullback.tildePullbackIso f).symm =
      Adjunction.leftAdjointCompIso (ModuleCat.extendRestrictScalarsAdj f.hom)
        (tilde.adjunction (R := S))
        ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
        (TildePullback.pushforwardSectionsIso f).symm := by
  rw [tildePullbackIso_eq_mate]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition -/

/-! # Tilde Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition

noncomputable section

/-!
# Composition compatibility of the canonical affine tilde comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

variable {R S T : CommRingCat.{u}}

/-- Composition of restriction of scalars after global sections. -/
def restrictionCompositionIso (f : R ⟶ S) (g : S ⟶ T) :
    (moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars g.hom) ⋙
        ModuleCat.restrictScalars f.hom ≅
      moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T))
      (ModuleCat.restrictScalarsComp f.hom g.hom).symm

/-- The right-adjoint comparison diagram commutes. -/
theorem right_composition (f : R ⟶ S) (g : S ⟶ T) :
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
        (TildePullback.pushforwardSectionsIso f).symm ≪≫ Affine.PushforwardSections.compositeSectionsIso f g =
      (Functor.associator (Scheme.Modules.pushforward (Spec.map g))
        (moduleSpecΓFunctor (R := S)) (ModuleCat.restrictScalars f.hom)).symm ≪≫
        Functor.isoWhiskerRight (TildePullback.pushforwardSectionsIso g) (ModuleCat.restrictScalars f.hom) ≪≫
          restrictionCompositionIso f g := by
  rw [Affine.PushforwardSections.sectionsIso_composition]
  apply Iso.ext
  simp only [Affine.PushforwardSections.iteratedSectionsIso, restrictionCompositionIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.id_comp]

/-- The canonical comparison from two scalar extensions followed by tilde to their composite. -/
def extensionThenTildeIso (f : R ⟶ S) (g : S ⟶ T) :
    ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom ⋙ tilde.functor T ≅
      ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor T :=
  Adjunction.leftAdjointCompIso (ModuleCat.extendRestrictScalarsAdj f.hom)
    ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (restrictionCompositionIso f g)

/-- The canonical comparison from two geometric pullbacks to the composite scalar extension. -/
def iteratedPullbackToModuleIso (f : R ⟶ S) (g : S ⟶ T) :
    (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f)) ⋙
        Scheme.Modules.pullback (Spec.map g) ≅
      ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor T :=
  Adjunction.leftAdjointCompIso
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (Affine.PushforwardSections.compositeSectionsIso f g)

/-- The canonical mates give a coherent comparison along the two affine pullbacks. -/
theorem tilde_composition (f : R ⟶ S) (g : S ⟶ T) :
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (TildePullback.tildePullbackIso g) ≪≫
        extensionThenTildeIso f g =
      (Functor.associator (ModuleCat.extendScalars f.hom) (tilde.functor S)
        (Scheme.Modules.pullback (Spec.map g))).symm ≪≫
        Functor.isoWhiskerRight (TildePullback.tildePullbackIso f).symm (Scheme.Modules.pullback (Spec.map g)) ≪≫
          iteratedPullbackToModuleIso f g := by
  have hg : TildePullback.tildePullbackIso g = Adjunction.leftAdjointCompIso (tilde.adjunction (R := S))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
      ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
      (TildePullback.pushforwardSectionsIso g) := by
    rw [TildeMate.tildePullbackIso_eq_mate]
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (ModuleCat.extendRestrictScalarsAdj f.hom)
    (tilde.adjunction (R := S)) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
    ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (TildePullback.pushforwardSectionsIso f).symm (TildePullback.pushforwardSectionsIso g)
    (restrictionCompositionIso f g) (Affine.PushforwardSections.compositeSectionsIso f g) (right_composition f g)
  rw [← hg, ← TildeMate.tildePullbackIso_symm_eq_compIso] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition -/

/-! # Adjoint Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition

noncomputable section

/-!
# Pasting canonical comparisons of left adjoints
-/

open _root_.CategoryTheory

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Appending an adjunction to a canonical composition comparison gives the whiskered comparison. -/
theorem postcompose
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₀₂ : A ⥤ C} {R₂₀ : C ⥤ A} {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₀₂ ⊣ R₂₀) (d : L₂₃ ⊣ R₃₂)
    (e : R₂₁ ⋙ R₁₀ ≅ R₂₀) :
    Adjunction.leftAdjointCompIso a (b.comp d) (c.comp d)
        (Functor.associator R₃₂ R₂₁ R₁₀ ≪≫ Functor.isoWhiskerLeft R₃₂ e) =
      (Functor.associator L₀₁ L₁₂ L₂₃).symm ≪≫
        Functor.isoWhiskerRight (Adjunction.leftAdjointCompIso a b c e) L₂₃ := by
  apply Iso.ext_inv
  apply (conjugateEquiv (a.comp (b.comp d)) (c.comp d)).injective
  change _ = conjugateEquiv (a.comp (b.comp d)) (c.comp d)
    (Functor.whiskerRight (Adjunction.leftAdjointCompIso a b c e).inv L₂₃ ≫
      (Functor.associator L₀₁ L₁₂ L₂₃).hom)
  rw [← conjugateEquiv_comp _ ((a.comp b).comp d), conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rfl

/-- The inverse associator has the inverse right-adjoint associator as its mate. -/
theorem associator_inv
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator L₀₁ L₁₂ L₂₃).inv = (Functor.associator R₃₂ R₂₁ R₁₀).inv := by
  have h : conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)
      (Functor.associator L₀₁ L₁₂ L₂₃) = Functor.associator R₃₂ R₂₁ R₁₀ :=
    Iso.ext (conjugateEquiv_associator_hom a b c)
  exact congrArg Iso.inv h

/-- Pasting two right-adjoint comparisons gives the corresponding composite of left comparisons. -/
theorem paste
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} {L₁₃ : B ⥤ D} {R₃₁ : D ⥤ B}
    {L₀₃ : A ⥤ D} {R₃₀ : D ⥤ A}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₂₃ ⊣ R₃₂)
    (d : L₁₃ ⊣ R₃₁) (v : L₀₃ ⊣ R₃₀)
    (e : R₃₂ ⋙ R₂₁ ≅ R₃₁) (k : R₃₁ ⋙ R₁₀ ≅ R₃₀) :
    Adjunction.leftAdjointCompIso (a.comp b) c v
        ((Functor.associator R₃₂ R₂₁ R₁₀).symm ≪≫
          Functor.isoWhiskerRight e R₁₀ ≪≫ k) =
      Functor.associator L₀₁ L₁₂ L₂₃ ≪≫
        Functor.isoWhiskerLeft L₀₁ (Adjunction.leftAdjointCompIso b c d e) ≪≫
          Adjunction.leftAdjointCompIso a d v k := by
  apply Iso.ext_inv
  apply (conjugateEquiv ((a.comp b).comp c) v).injective
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ (a.comp d),
    ← conjugateEquiv_comp _ (a.comp (b.comp c)), associator_inv,
    conjugateEquiv_whiskerLeft]
  simp only [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition -/

/-! # Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

noncomputable section

/-!
# Standard maps in the affine pullback composition comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

/-- Equality transport for geometric pullbacks has the corresponding direct-image mate. -/
theorem pullbackCongr_mate {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g) (Scheme.Modules.pullbackCongr h).inv =
        (Scheme.Modules.pushforwardCongr h).hom := by
  subst g
  change conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) (𝟙 _) = _
  rw [conjugateEquiv_id]
  ext M U x
  simp

variable {R S T : CommRingCat.{u}}

/-- The canonical scalar-extension comparison is the usual scalar-extension composition map. -/
theorem extensionThenTildeIso_standard (f : R ⟶ S) (g : S ⟶ T) :
    TildeComposition.extensionThenTildeIso f g =
      (Functor.associator (ModuleCat.extendScalars f.hom)
        (ModuleCat.extendScalars g.hom) (tilde.functor T)).symm ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f.hom g.hom).symm
          (tilde.functor T) := by
  exact AdjointComposition.postcompose
    (ModuleCat.extendRestrictScalarsAdj f.hom) (ModuleCat.extendRestrictScalarsAdj g.hom)
    (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom) (tilde.adjunction (R := T))
    (ModuleCat.restrictScalarsComp f.hom g.hom).symm

/-- Geometric pullback composition, including the contravariant composition equation for Spec. -/
def geometricCompositionIso (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      Scheme.Modules.pullback (Spec.map (f ≫ g)) :=
  Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
    Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm

/-- This geometric map is the canonical mate of direct-image composition. -/
theorem geometricCompositionIso_mate (f : R ⟶ S) (g : S ⟶ T) :
    Adjunction.leftAdjointCompIso
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
        Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm) =
      geometricCompositionIso f g := by
  apply Iso.ext_inv
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))).injective
  change _ = conjugateEquiv _ _
    ((Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).inv ≫
      (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv)
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map g ≫ Spec.map f)), Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    pullbackCongr_mate, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rfl

/-- The iterated geometric comparison uses the standard pullback composition and tilde map. -/
theorem iteratedPullbackToModuleIso_standard (f : R ⟶ S) (g : S ⟶ T) :
    TildeComposition.iteratedPullbackToModuleIso f g =
      Functor.associator (tilde.functor R) (Scheme.Modules.pullback (Spec.map f))
        (Scheme.Modules.pullback (Spec.map g)) ≪≫
        Functor.isoWhiskerLeft (tilde.functor R) (geometricCompositionIso f g) ≪≫
          TildePullback.tildePullbackIso (f ≫ g) := by
  have h := AdjointComposition.paste (tilde.adjunction (R := R))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
      Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm)
    (TildePullback.pushforwardSectionsIso (f ≫ g))
  rw [geometricCompositionIso_mate] at h
  have ht : Adjunction.leftAdjointCompIso (tilde.adjunction (R := R))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
      ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
      (TildePullback.pushforwardSectionsIso (f ≫ g)) = TildePullback.tildePullbackIso (f ≫ g) := by
    rw [TildeMate.tildePullbackIso_eq_mate]
    rfl
  rw [ht] at h
  exact h

/-- The affine comparison carries the standard scalar-extension composition to geometric pullback
composition, on each actual module. -/
theorem tilde_composition_app (f : R ⟶ S) (g : S ⟶ T) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map g)).map ((TildePullback.tildePullbackIso f).hom.app M) ≫
        (TildePullback.tildePullbackIso g).hom.app ((ModuleCat.extendScalars f.hom).obj M) ≫
          (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) =
      (geometricCompositionIso f g).hom.app ((tilde.functor R).obj M) ≫
        (TildePullback.tildePullbackIso (f ≫ g)).hom.app M := by
  have h := TildeComposition.tilde_composition f g
  rw [extensionThenTildeIso_standard, iteratedPullbackToModuleIso_standard] at h
  have hm := congrArg (fun e => e.hom.app M) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp] at hm
  rw [hm, ← Category.assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app,
    (Scheme.Modules.pullback (Spec.map g)).map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom -/

/-! # Pull Hom -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom

noncomputable section

/-!
# Native geometric formulas for pullback of descent morphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open Pseudofunctor.LocallyDiscreteOpToCat

/-- Pulling a descent morphism uses the standard sheaf pullback composition isomorphisms. -/
theorem pullHom_eq {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := KernelLinearization.modulePullbacks) a g gf₁ gf₂ h₁ h₂ =
      (Scheme.Modules.pullbackComp g f₁ ≪≫ Scheme.Modules.pullbackCongr h₁).inv.app L₁ ≫
        (Scheme.Modules.pullback g).map a ≫
          (Scheme.Modules.pullbackComp g f₂ ≪≫ Scheme.Modules.pullbackCongr h₂).hom.app L₂ := by
  subst gf₁
  subst gf₂
  simp only [pullHom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.trans_refl]
  rfl

/-- The geometric pullback formula, kept as a named proposition for stable specialization. -/
def HasPullHomFormula {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) : Prop :=
  pullHom (F := KernelLinearization.modulePullbacks) a g gf₁ gf₂ h₁ h₂ =
    (Scheme.Modules.pullbackComp g f₁ ≪≫ Scheme.Modules.pullbackCongr h₁).inv.app L₁ ≫
      (Scheme.Modules.pullback g).map a ≫
        (Scheme.Modules.pullbackComp g f₂ ≪≫ Scheme.Modules.pullbackCongr h₂).hom.app L₂

/-- The standard formula holds for all geometric descent morphisms. -/
theorem hasPullHomFormula {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    HasPullHomFormula a g gf₁ gf₂ h₁ h₂ := pullHom_eq a g gf₁ gf₂ h₁ h₂

/-- The native descent pullback has the standard formula for the affine coordinate maps. -/
theorem affine_hasPullHomFormula {R S T : CommRingCat.{u}} {L : (Spec R).Modules}
    (f g : R ⟶ S) (k : S ⟶ T)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    HasPullHomFormula a (Spec.map k) (Spec.map (f ≫ k)) (Spec.map (g ≫ k))
      (Spec.map_comp f k).symm (Spec.map_comp g k).symm :=
  hasPullHomFormula (X₁ := Spec R) (X₂ := Spec R) (Y := Spec S) (Y' := Spec T)
    (L₁ := L) (L₂ := L) (f₁ := Spec.map f) (f₂ := Spec.map g)
    a (Spec.map k) (Spec.map (f ≫ k)) (Spec.map (g ≫ k))
    (Spec.map_comp f k).symm (Spec.map_comp g k).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations -/

/-! # Descent Equations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

noncomputable section

/-!
# Ordinary scheme descent data satisfy native geometric pullback equations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom

/-- Pullback of a geometric gluing morphism, using actual scheme pullback composition maps. -/
def nativePullback {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (Scheme.Modules.pullback gf₁).obj L₁ ⟶ (Scheme.Modules.pullback gf₂).obj L₂ :=
  (Scheme.Modules.pullbackComp g f₁ ≪≫ Scheme.Modules.pullbackCongr h₁).inv.app L₁ ≫
    (Scheme.Modules.pullback g).map a ≫
      (Scheme.Modules.pullbackComp g f₂ ≪≫ Scheme.Modules.pullbackCongr h₂).hom.app L₂

variable {ι : Type v} {B : Scheme.{u}} {A : ι → Scheme.{u}} {f : ∀ i, A i ⟶ B}
  (D : KernelLinearization.modulePullbacks.DescentData f)

/-- The ordinary descent data give exactly the native sheaf pullback equation. -/
theorem hom_pullback {Y Y' : Scheme.{u}} (p : Y' ⟶ Y) (q : Y ⟶ B) (q' : Y' ⟶ B)
    (hq : p ≫ q = q') {i j : ι} (x : Y ⟶ A i) (y : Y ⟶ A j)
    (hx : x ≫ f i = q) (hy : y ≫ f j = q)
    (x' : Y' ⟶ A i) (y' : Y' ⟶ A j) (hpx : p ≫ x = x') (hpy : p ≫ y = y') :
    nativePullback (D.hom q x y hx hy) p x' y' hpx hpy =
      D.hom q' x' y' (by rw [← hpx, Category.assoc, hx, hq])
        (by rw [← hpy, Category.assoc, hy, hq]) := by
  unfold nativePullback
  exact (PullHom.pullHom_eq (L₁ := D.obj i) (L₂ := D.obj j)
    (D.hom q x y hx hy) p x' y' hpx hpy).symm.trans
    (D.pullHom_hom p q q' hq x y hx hy x' y' hpx hpy)

/-- Equal choices of the composite coordinate maps induce the usual endpoint transports. -/
theorem nativePullback_congr {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) {gf₁ gf₁' : Y' ⟶ X₁} {gf₂ gf₂' : Y' ⟶ X₂}
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (e₁ : gf₁ = gf₁') (e₂ : gf₂ = gf₂') :
    nativePullback a g gf₁' gf₂' (h₁.trans e₁) (h₂.trans e₂) =
      eqToHom (congrArg (fun r => (Scheme.Modules.pullback r).obj L₁) e₁.symm) ≫
        nativePullback a g gf₁ gf₂ h₁ h₂ ≫
          eqToHom (congrArg (fun r => (Scheme.Modules.pullback r).obj L₂) e₂) := by
  subst gf₁'
  subst gf₂'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition -/

/-! # Pullback Fiber Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

noncomputable section

/-!
# Composition comparisons for fibers of a pulled-back object commute with native geometric pullback
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {E Z : C} (p : E ⟶ Z) (L : F.obj (.mk (op Z)))

/-- The actual composition isomorphism identifies a fiber of the pulled-back object with its original fiber. -/
def fiberIso {T : C} (x : T ⟶ E) :
    (F.map x.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) ≅
      (F.map (x ≫ p).op.toLoc).toFunctor.obj L :=
  (Cat.Hom.toNatIso (F.mapComp' p.op.toLoc x.op.toLoc (x ≫ p).op.toLoc rfl)).symm.app L

/-- The same actual composition comparison with an explicitly specified composite point. -/
def fiberIsoTo {T : C} (k : T ⟶ E) (x : T ⟶ Z) (hk : k ≫ p = x) :
    (F.map k.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) ≅
      (F.map x.op.toLoc).toFunctor.obj L :=
  (Cat.Hom.toNatIso (F.mapComp' p.op.toLoc k.op.toLoc x.op.toLoc (by rw [← hk]; rfl))).symm.app L

/-- Native pullback preserves composition comparisons with specified endpoint equalities. -/
theorem fiberIsoTo_hom_pullback {T T' : C} (g : T' ⟶ T) (k : T ⟶ E) (x : T ⟶ Z)
    (hk : k ≫ p = x) (k' : T' ⟶ E) (x' : T' ⟶ Z) (hk' : k' ≫ p = x')
    (hgk : g ≫ k = k') (hgx : g ≫ x = x') :
    pullHom (fiberIsoTo F p L k x hk).hom g k' x' hgk hgx = (fiberIsoTo F p L k' x' hk').hom := by
  unfold pullHom fiberIsoTo
  have h := F.mapComp'₀₁₃_inv_app p.op.toLoc k.op.toLoc g.op.toLoc
    x.op.toLoc k'.op.toLoc x'.op.toLoc (by rw [← hk]; rfl)
    (by rw [← hgk]; rfl) (by rw [← hk']; rfl) L
  exact h.symm

/-- Pseudofunctor associativity gives native pullback of the actual fiber comparison. -/
theorem fiberIso_hom_pullback {T T' : C} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (hxp : g ≫ (x ≫ p) = x' ≫ p) :
    pullHom (fiberIso F p L x).hom g x' (x' ≫ p) hx hxp = (fiberIso F p L x').hom := by
  unfold pullHom fiberIso
  have h := F.mapComp'₀₁₃_inv_app p.op.toLoc x.op.toLoc g.op.toLoc
    (x ≫ p).op.toLoc x'.op.toLoc (x' ≫ p).op.toLoc rfl
    (by rw [← hx]; rfl) rfl L
  exact h.symm

/-- Native pullback carries an actual fiber isomorphism to an actual fiber isomorphism. -/
def pullIso {A B T T' : C} {M : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    {x : T ⟶ A} {y : T ⟶ B}
    (e : (F.map x.op.toLoc).toFunctor.obj M ≅ (F.map y.op.toLoc).toFunctor.obj N)
    (g : T' ⟶ T) (x' : T' ⟶ A) (y' : T' ⟶ B) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    (F.map x'.op.toLoc).toFunctor.obj M ≅ (F.map y'.op.toLoc).toFunctor.obj N where
  hom := pullHom e.hom g x' y' hx hy
  inv := pullHom e.inv g y' x' hy hx
  hom_inv_id := by
    rw [← PullHom.pullHom_comp e.hom e.inv g x' y' x' hx hy hx, e.hom_inv_id]
    exact PullHom.pullHom_identity g x' hx
  inv_hom_id := by
    rw [← PullHom.pullHom_comp e.inv e.hom g y' x' y' hy hx hy, e.inv_hom_id]
    exact PullHom.pullHom_identity g y' hy

/-- The whole fiber comparison isomorphism is preserved by change of test object. -/
theorem fiberIso_pullback {T T' : C} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (hxp : g ≫ (x ≫ p) = x' ≫ p) :
    pullIso F (fiberIso F p L x) g x' (x' ≫ p) hx hxp = fiberIso F p L x' := by
  apply Iso.ext
  exact fiberIso_hom_pullback F p L g x x' hx hxp

/-- Native pullback also preserves the inverse fiber comparison. -/
theorem fiberIso_inv_pullback {T T' : C} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (hxp : g ≫ (x ≫ p) = x' ≫ p) :
    pullHom (fiberIso F p L x).inv g (x' ≫ p) x' hxp hx = (fiberIso F p L x').inv :=
  congrArg Iso.inv (fiberIso_pullback F p L g x x' hx hxp)

/-- Transport a morphism of original fibers to the actual fibers of the pulled-back object. -/
def transport {T : C} (x y : T ⟶ E)
    (a : (F.map (x ≫ p).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ p).op.toLoc).toFunctor.obj L) :
    (F.map x.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) ⟶
      (F.map y.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) :=
  (fiberIso F p L x).hom ≫ a ≫ (fiberIso F p L y).inv

/-- Pulling back a transported fiber operation agrees with transporting its genuine native pullback. -/
theorem transport_pullback {T T' : C} (g : T' ⟶ T) (x y : T ⟶ E)
    (a : (F.map (x ≫ p).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ p).op.toLoc).toFunctor.obj L)
    (x' y' : T' ⟶ E) (hx : g ≫ x = x') (hy : g ≫ y = y')
    (hxp : g ≫ (x ≫ p) = x' ≫ p) (hyp : g ≫ (y ≫ p) = y' ≫ p) :
    pullHom (transport F p L x y a) g x' y' hx hy =
      transport F p L x' y' (pullHom a g (x' ≫ p) (y' ≫ p) hxp hyp) := by
  unfold transport
  rw [PullHom.pullHom_comp _ _ g x' (x' ≫ p) y' hx hxp hy,
    PullHom.pullHom_comp _ _ g (x' ≫ p) (y' ≫ p) y' hxp hyp hy,
    fiberIso_hom_pullback, fiberIso_inv_pullback]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles -/

/-! # Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

noncomputable section

/-!
Line bundles over arbitrary schemes and their contravariant functor of
isomorphism classes. These are actual sheaves of modules locally isomorphic
to the structure sheaf, not abstract polarization parameters.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The structure sheaf considered as a sheaf of modules over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Pullback preserves the structure module. -/
def structureModulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
  have : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
  have : ((Functor.fromPUnit.{0} (⊤ : Y.Opens)) ⋙
      TopologicalSpace.Opens.map f.base).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso (fun _ => Iso.refl _))
  have : (TopologicalSpace.Opens.map f.base).Final :=
    Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) _
  have := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :
    (SheafOfModules.pullback f.toRingCatSheafHom).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

/-- An algebraic line bundle over an arbitrary scheme. -/
structure LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  locallyTrivial : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj sheaf ≅ structureModule U.toScheme)

namespace LineBundle

variable {X Y Z : Scheme.{u}}

/-- The trivial line bundle. -/
def trivial (X : Scheme.{u}) : LineBundle X where
  sheaf := structureModule X
  locallyTrivial x := ⟨⊤, by trivial, ⟨structureModulePullbackIso _⟩⟩

/-- Base change of a line bundle, with local triviality proved by pulling
back its frames to the preimages of the trivializing opens. -/
def pullback (f : X ⟶ Y) (L : LineBundle Y) : LineBundle X where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial (f x)
    refine ⟨f ⁻¹ᵁ U, hx, ⟨?_⟩⟩
    exact (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app L.sheaf ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
      structureModulePullbackIso (f ∣_ U)

/-- Isomorphism of line bundles is isomorphism of their module sheaves. -/
def isoSetoid (X : Scheme.{u}) : Setoid (LineBundle X) where
  r L M := Nonempty (L.sheaf ≅ M.sheaf)
  iseqv := {
    refl L := ⟨Iso.refl L.sheaf⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩ }

/-- Isomorphism classes of actual algebraic line bundles. -/
def IsoClass (X : Scheme.{u}) := Quotient (isoSetoid X)

/-- The isomorphism class of a line bundle. -/
def classOf (L : LineBundle X) : IsoClass X := Quotient.mk _ L

/-- The class of the structure sheaf. -/
def trivialClass (X : Scheme.{u}) : IsoClass X := Quotient.mk _ (LineBundle.trivial X)

/-- Pullback on isomorphism classes does not depend on the representative. -/
def pullbackClass (f : X ⟶ Y) : IsoClass Y → IsoClass X :=
  Quotient.map (LineBundle.pullback f) (fun _ _ ⟨e⟩ =>
    ⟨(Scheme.Modules.pullback f).mapIso e⟩)

@[simp]
theorem pullbackClass_trivial (f : X ⟶ Y) :
    pullbackClass f (trivialClass Y) = trivialClass X := by
  apply Quotient.sound
  exact ⟨structureModulePullbackIso f⟩

@[simp]
theorem pullbackClass_id (q : IsoClass X) : pullbackClass (𝟙 X) q = q := by
  refine Quotient.inductionOn q (fun L => ?_)
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackId X).app L.sheaf⟩

theorem pullbackClass_comp (f : X ⟶ Y) (g : Y ⟶ Z) (q : IsoClass Z) :
    pullbackClass (f ≫ g) q = pullbackClass f (pullbackClass g q) := by
  refine Quotient.inductionOn q (fun L => ?_)
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackComp f g).symm.app L.sheaf⟩

/-- Pullback along an isomorphism gives an equivalence on line-bundle classes. -/
def pullbackIso (e : X ≅ Y) : IsoClass Y ≃ IsoClass X where
  toFun := pullbackClass e.hom
  invFun := pullbackClass e.inv
  left_inv q := (pullbackClass_comp e.inv e.hom q).symm.trans
    ((congrArg (fun f : Y ⟶ Y => pullbackClass f q) e.inv_hom_id).trans
      (pullbackClass_id q))
  right_inv q := (pullbackClass_comp e.hom e.inv q).symm.trans
    ((congrArg (fun f : X ⟶ X => pullbackClass f q) e.hom_inv_id).trans
      (pullbackClass_id q))

end LineBundle

/-- The contravariant functor of isomorphism classes of line bundles. -/
def lineBundleClassFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := LineBundle.IsoClass X.unop
  map f := TypeCat.ofHom (LineBundle.pullbackClass f.unop)
  map_id X := by
    ext q
    exact LineBundle.pullbackClass_id q
  map_comp f g := by
    ext q
    exact LineBundle.pullbackClass_comp g.unop f.unop q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality -/

/-! # Square Map Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality

noncomputable section

/-! Equality of module maps after pullback transports across a commutative square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X X' Y Y' : Scheme.{u}}

def modulePullbackSquareIso (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback b :=
  Scheme.Modules.pullbackComp g a ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp b f).symm

theorem pullbackSquare_map_eq (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) {M N : X.Modules} (φ ψ : M ⟶ N)
    (hφ : (Scheme.Modules.pullback f).map φ = (Scheme.Modules.pullback f).map ψ) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback a).map φ) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback a).map ψ) := by
  let e := modulePullbackSquareIso a b f g h
  apply (cancel_mono (e.hom.app N)).mp
  exact (e.hom.naturality φ).trans
    ((congrArg (fun k => e.hom.app M ≫ (Scheme.Modules.pullback b).map k) hφ).trans
      (e.hom.naturality ψ).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps -/

/-! # Square Module Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps

noncomputable section

/-! Restrict a map upstairs to a commutative square, retaining the canonical
comparison between the two iterated pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X X' Y Y' : Scheme.{u}}

def pullbackSquareModuleMap (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj N) :=
  (SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M ≫ (Scheme.Modules.pullback b).map φ ≫
    (SquareMapEquality.modulePullbackSquareIso a b f g h).inv.app N

theorem pullbackSquareModuleMap_of_pullback (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : g ≫ a = b ≫ f) {M N : X.Modules} (φ : M ⟶ N) :
    pullbackSquareModuleMap a b f g h ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback a).map φ) := by
  let e := SquareMapEquality.modulePullbackSquareIso a b f g h
  exact (congrArg (fun k => k ≫ e.inv.app N) (e.hom.naturality φ).symm).trans
    (by simp only [Category.assoc, e.hom_inv_id_app, Category.comp_id]; rfl)

theorem pullbackSquareModuleMap_comp (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : g ≫ a = b ≫ f) {M N Q : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (ψ : (Scheme.Modules.pullback f).obj N ⟶ (Scheme.Modules.pullback f).obj Q) :
    pullbackSquareModuleMap a b f g h (φ ≫ ψ) =
      pullbackSquareModuleMap a b f g h φ ≫ pullbackSquareModuleMap a b f g h ψ := by
  unfold pullbackSquareModuleMap
  rw [(Scheme.Modules.pullback b).map_comp]
  simp only [Category.assoc, (SquareMapEquality.modulePullbackSquareIso a b f g h).inv_hom_id_app_assoc]

theorem pullbackSquareModuleMap_isIso (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : g ≫ a = b ≫ f) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) [IsIso φ] :
    IsIso (pullbackSquareModuleMap a b f g h φ) :=
  inferInstanceAs (IsIso ((SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M ≫
    (Scheme.Modules.pullback b).map φ ≫ (SquareMapEquality.modulePullbackSquareIso a b f g h).inv.app N))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents -/

/-! # Associativity Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents

noncomputable section

/-! The associativity comparison for three module-sheaf pullbacks, on components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {W X Y Z : Scheme.{u}}

theorem modulePullbackCongr_hom_app {a b : X ⟶ Y} (h : a = b) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg (fun f : X ⟶ Y => (Scheme.Modules.pullback f).obj M) h) := by
  subst b
  rfl

theorem modulePullback_associativity_components (a : W ⟶ X) (b : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp a (b ≫ f)).inv.app M ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b f).inv.app M) ≫
        (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackComp (a ≫ b) f).hom.app M =
      (Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).hom.app M := by
  have h := congr_app (Scheme.Modules.pseudofunctor_associativity a b f) M
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, modulePullbackCongr_hom_app, eqToHom_app] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion -/

/-! # Associativity Fusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion

noncomputable section

/-! The two canonical ways to combine three pullbacks agree as bundle isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {W X Y Z : Scheme.{u}}

theorem modulePullback_associativity_fusion (a : W ⟶ X) (b : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b f).app M) ≪≫
        (Scheme.Modules.pullbackComp a (b ≫ f)).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app M =
      (Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback f).obj M) ≪≫
        (Scheme.Modules.pullbackComp (a ≫ b) f).app M := by
  let c₁ := (Scheme.Modules.pullbackComp a (b ≫ f)).app M
  let c₂ := (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b f).app M)
  let c₃ := (Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback f).obj M)
  let c₄ := (Scheme.Modules.pullbackComp (a ≫ b) f).app M
  let c₅ := (Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app M
  have h : c₁.inv ≫ c₂.inv ≫ c₃.hom ≫ c₄.hom = c₅.hom :=
    AssociativityComponents.modulePullback_associativity_components a b f M
  have h' := congrArg (fun k => c₂.hom ≫ c₁.hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at h'
  apply Iso.ext
  exact h'.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition -/

/-! # Map Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition

noncomputable section

/-! Composition of pullback for arbitrary maps upstairs, with associativity coherence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {W X Y Z : Scheme.{u}}

theorem moduleMap_homCongr_combine {A B C D E F : X.Modules}
    (eA : A ≅ C) (eB : B ≅ D) (fA : C ≅ E) (fB : D ≅ F) (φ : A ⟶ B) :
    Iso.homCongr fA fB (Iso.homCongr eA eB φ) = Iso.homCongr (eA ≪≫ fA) (eB ≪≫ fB) φ :=
  (Iso.homCongr_trans eA eB fA fB φ).symm

theorem moduleMap_homCongr_naturality (F G : X.Modules ⥤ Y.Modules) (e : F ≅ G)
    {M N : X.Modules} (φ : M ⟶ N) :
    Iso.homCongr (e.app M) (e.app N) (F.map φ) = G.map φ := by
  exact (congrArg (fun k => e.inv.app M ≫ k) (e.hom.naturality φ)).trans
    (e.inv_hom_id_app_assoc M _)

def moduleMapPullbackComp (a : X ⟶ Y) (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback (a ≫ f)).obj M ⟶ (Scheme.Modules.pullback (a ≫ f)).obj N :=
  Iso.homCongr ((Scheme.Modules.pullbackComp a f).app M) ((Scheme.Modules.pullbackComp a f).app N)
    ((Scheme.Modules.pullback a).map φ)

theorem moduleMapPullbackComp_of_map (a : X ⟶ Y) (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : M ⟶ N) : moduleMapPullbackComp a f ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback (a ≫ f)).map φ :=
  moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackComp a f) φ

theorem moduleMapPullbackComp_assoc (a : W ⟶ X) (b : X ⟶ Y) (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    Iso.homCongr ((Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app M)
      ((Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app N)
      (moduleMapPullbackComp a (b ≫ f) (moduleMapPullbackComp b f φ)) =
        moduleMapPullbackComp (a ≫ b) f φ := by
  unfold moduleMapPullbackComp
  rw [Functor.map_homCongr]
  rw [moduleMap_homCongr_combine, moduleMap_homCongr_combine,
    Pullback.AssociativityFusion.modulePullback_associativity_fusion, Pullback.AssociativityFusion.modulePullback_associativity_fusion, Iso.homCongr_trans]
  exact congrArg (fun k => Iso.homCongr ((Scheme.Modules.pullbackComp (a ≫ b) f).app M)
      ((Scheme.Modules.pullbackComp (a ≫ b) f).app N) k)
    (moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackComp a b) φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence -/

/-! # Map Pullback Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence

noncomputable section

/-! Transport of pulled-back module maps along equality of the underlying scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

def moduleMapPullbackCongr {f g : Y ⟶ Z} (h : f = g) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N :=
  Iso.homCongr ((Scheme.Modules.pullbackCongr h).app M)
    ((Scheme.Modules.pullbackCongr h).app N) φ

theorem moduleMapPullbackCongr_refl (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    moduleMapPullbackCongr (rfl : f = f) φ = φ := by
  change (Iso.refl _).homCongr (Iso.refl _) φ = φ
  exact Iso.homCongr_refl φ

theorem moduleMapPullbackCongr_trans {f g h : Y ⟶ Z} (h₁ : f = g) (h₂ : g = h)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    moduleMapPullbackCongr h₂ (moduleMapPullbackCongr h₁ φ) =
      moduleMapPullbackCongr (h₁.trans h₂) φ := by
  subst g h
  simp only [moduleMapPullbackCongr_refl]

theorem moduleMapPullbackComp_congr_base (a : X ⟶ Y) {f g : Y ⟶ Z} (h : f = g)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    moduleMapPullbackCongr (congrArg (fun k => a ≫ k) h) (MapPullbackComposition.moduleMapPullbackComp a f φ) =
      MapPullbackComposition.moduleMapPullbackComp a g (moduleMapPullbackCongr h φ) := by
  subst g
  simp only [moduleMapPullbackCongr_refl]

theorem moduleMapPullbackCongr_of_map {f g : Y ⟶ Z} (h : f = g) {M N : Z.Modules} (φ : M ⟶ N) :
    moduleMapPullbackCongr h ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback g).map φ :=
  MapPullbackComposition.moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackCongr h) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion -/

/-! # Unit Fusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion

noncomputable section

/-! The canonical comparison for pullback by the identity agrees with the unit isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem modulePullback_identity_fusion (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 X) f).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.id_comp f)).app M =
      (Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback f).obj M) := by
  let c₁ := (Scheme.Modules.pullbackComp (𝟙 X) f).app M
  let c₂ := (Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback f).obj M)
  let c₃ := (Scheme.Modules.pullbackCongr (Category.id_comp f)).app M
  have h : c₁.inv ≫ c₂.hom = c₃.hom := by
    have h' := congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      eqToHom_app] at h'
    have h'' : c₁.inv ≫ c₂.hom ≫ 𝟙 _ = c₃.hom := h'
    simpa only [Category.comp_id] using h''
  have h' := congrArg (fun k => c₁.hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at h'
  apply Iso.ext
  exact h'.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitFusion"

@[expose] public section ComponentSource_27
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback -/

/-! # Map Slice Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback

noncomputable section

/-! Functorial pullback of module maps on schemes over a fixed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem moduleMapPullbackComp_assoc_forward {W Y Z : Scheme.{u}}
    (a : W ⟶ Y) (b : Y ⟶ Z) (f : Z ⟶ X) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    MapPullbackComposition.moduleMapPullbackComp a (b ≫ f) (MapPullbackComposition.moduleMapPullbackComp b f φ) =
      MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a b f) (MapPullbackComposition.moduleMapPullbackComp (a ≫ b) f φ) := by
  have h : MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a b f).symm
      (MapPullbackComposition.moduleMapPullbackComp a (b ≫ f) (MapPullbackComposition.moduleMapPullbackComp b f φ)) =
        MapPullbackComposition.moduleMapPullbackComp (a ≫ b) f φ := MapPullbackComposition.moduleMapPullbackComp_assoc a b f φ
  have h' := congrArg (fun k => MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a b f) k) h
  rw [MapPullbackCongruence.moduleMapPullbackCongr_trans] at h'
  simpa only [MapPullbackCongruence.moduleMapPullbackCongr_refl] using h'

def moduleMapPullbackAlong {U V : Over X} (a : U ⟶ V) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N) :
    (Scheme.Modules.pullback U.hom).obj M ⟶ (Scheme.Modules.pullback U.hom).obj N :=
  MapPullbackCongruence.moduleMapPullbackCongr a.w (MapPullbackComposition.moduleMapPullbackComp a.left V.hom φ)

theorem moduleMapPullbackAlong_comp {U V W : Over X} (a : U ⟶ V) (b : V ⟶ W)
    {M N : X.Modules}
    (φ : (Scheme.Modules.pullback W.hom).obj M ⟶ (Scheme.Modules.pullback W.hom).obj N) :
    moduleMapPullbackAlong a (moduleMapPullbackAlong b φ) = moduleMapPullbackAlong (a ≫ b) φ := by
  unfold moduleMapPullbackAlong
  rw [← MapPullbackCongruence.moduleMapPullbackComp_congr_base a.left b.w, MapPullbackCongruence.moduleMapPullbackCongr_trans,
    moduleMapPullbackComp_assoc_forward, MapPullbackCongruence.moduleMapPullbackCongr_trans]
  rfl

theorem moduleMapPullbackAlong_id (U : Over X) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback U.hom).obj M ⟶ (Scheme.Modules.pullback U.hom).obj N) :
    moduleMapPullbackAlong (𝟙 U) φ = φ := by
  unfold moduleMapPullbackAlong MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  rw [MapPullbackComposition.moduleMap_homCongr_combine]
  change Iso.homCongr
      ((Scheme.Modules.pullbackComp (𝟙 U.left) U.hom).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.id_comp U.hom)).app M)
      ((Scheme.Modules.pullbackComp (𝟙 U.left) U.hom).app N ≪≫
        (Scheme.Modules.pullbackCongr (Category.id_comp U.hom)).app N)
      ((Scheme.Modules.pullback (𝟙 U.left)).map φ) = φ
  rw [Pullback.UnitFusion.modulePullback_identity_fusion, Pullback.UnitFusion.modulePullback_identity_fusion]
  exact MapPullbackComposition.moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackId U.left) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback"

@[expose] public section ComponentSource_28
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf -/

/-! # Hom Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf

noncomputable section

/-! Actual module maps after base change form a presheaf on schemes over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def moduleHomPresheaf (M N : X.Modules) : (Over X)ᵒᵖ ⥤ Type u where
  obj U := (Scheme.Modules.pullback U.unop.hom).obj M ⟶ (Scheme.Modules.pullback U.unop.hom).obj N
  map f := TypeCat.ofHom (MapSlicePullback.moduleMapPullbackAlong f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact MapSlicePullback.moduleMapPullbackAlong_id U.unop φ
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact (MapSlicePullback.moduleMapPullbackAlong_comp g.unop f.unop φ).symm

theorem moduleMapPullbackAlong_of_map {U V : Over X} (a : U ⟶ V) {M N : X.Modules} (φ : M ⟶ N) :
    MapSlicePullback.moduleMapPullbackAlong a ((Scheme.Modules.pullback V.hom).map φ) =
      (Scheme.Modules.pullback U.hom).map φ := by
  unfold MapSlicePullback.moduleMapPullbackAlong
  rw [MapPullbackComposition.moduleMapPullbackComp_of_map, MapPullbackCongruence.moduleMapPullbackCongr_of_map]

def globalModuleMapSection (M N : X.Modules) (φ : M ⟶ N) : (moduleHomPresheaf M N).sections where
  val U := (Scheme.Modules.pullback U.unop.hom).map φ
  property f := moduleMapPullbackAlong_of_map f.unop φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf"

@[expose] public section ComponentSource_29
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition -/

/-! # Map Slice Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition

noncomputable section

/-! Pullback on the presheaf of module maps preserves composition and isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {U V : Over X}

theorem moduleMapPullbackAlong_map_comp (a : U ⟶ V) {M N P : X.Modules}
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N)
    (ψ : (Scheme.Modules.pullback V.hom).obj N ⟶ (Scheme.Modules.pullback V.hom).obj P) :
    MapSlicePullback.moduleMapPullbackAlong a (φ ≫ ψ) = MapSlicePullback.moduleMapPullbackAlong a φ ≫ MapSlicePullback.moduleMapPullbackAlong a ψ := by
  unfold MapSlicePullback.moduleMapPullbackAlong MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  rw [Functor.map_comp, Iso.homCongr_comp, Iso.homCongr_comp]

theorem moduleMapPullbackAlong_isIso (a : U ⟶ V) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N) [IsIso φ] :
    IsIso (MapSlicePullback.moduleMapPullbackAlong a φ) := by
  unfold MapSlicePullback.moduleMapPullbackAlong MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  simp only [Iso.homCongr_apply]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition
end ComponentSource_29

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSliceComposition"

@[expose] public section ComponentSource_30
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback -/

/-! # Iso Slice Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback

noncomputable section

/-! Functorial pullback of actual module isomorphisms over a base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem moduleMapPullbackAlong_map_id {U V : Over X} (a : U ⟶ V) (M : X.Modules) :
    MapSlicePullback.moduleMapPullbackAlong a (𝟙 ((Scheme.Modules.pullback V.hom).obj M)) =
      𝟙 ((Scheme.Modules.pullback U.hom).obj M) := by
  have h := HomPresheaf.moduleMapPullbackAlong_of_map a (𝟙 M)
  rw [(Scheme.Modules.pullback V.hom).map_id, (Scheme.Modules.pullback U.hom).map_id] at h
  exact h

def moduleIsoPullbackAlong {U V : Over X} (a : U ⟶ V) {M N : X.Modules}
    (e : (Scheme.Modules.pullback V.hom).obj M ≅ (Scheme.Modules.pullback V.hom).obj N) :
    (Scheme.Modules.pullback U.hom).obj M ≅ (Scheme.Modules.pullback U.hom).obj N where
  hom := MapSlicePullback.moduleMapPullbackAlong a e.hom
  inv := MapSlicePullback.moduleMapPullbackAlong a e.inv
  hom_inv_id := by
    rw [← MapSliceComposition.moduleMapPullbackAlong_map_comp, e.hom_inv_id, moduleMapPullbackAlong_map_id]
  inv_hom_id := by
    rw [← MapSliceComposition.moduleMapPullbackAlong_map_comp, e.inv_hom_id, moduleMapPullbackAlong_map_id]

theorem moduleIsoPullbackAlong_id (U : Over X) {M N : X.Modules}
    (e : (Scheme.Modules.pullback U.hom).obj M ≅ (Scheme.Modules.pullback U.hom).obj N) :
    moduleIsoPullbackAlong (𝟙 U) e = e := by
  apply Iso.ext
  exact MapSlicePullback.moduleMapPullbackAlong_id U e.hom

theorem moduleIsoPullbackAlong_comp {U V W : Over X} (a : U ⟶ V) (b : V ⟶ W) {M N : X.Modules}
    (e : (Scheme.Modules.pullback W.hom).obj M ≅ (Scheme.Modules.pullback W.hom).obj N) :
    moduleIsoPullbackAlong a (moduleIsoPullbackAlong b e) = moduleIsoPullbackAlong (a ≫ b) e := by
  apply Iso.ext
  exact MapSlicePullback.moduleMapPullbackAlong_comp a b e.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback
end ComponentSource_30

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback"

@[expose] public section ComponentSource_31
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-! # Module Descent Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery

noncomputable section

/-! Changing local descent objects to their actual recovered ambient
modules. All recovery maps retain the native pullback composition paths. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-- The existing slice pullback operation is the native pseudofunctor
pullback on both equal endpoint maps. -/
theorem moduleMapPullbackAlong_eq_pullHom {X : Scheme.{u}} {M N : X.Modules}
    {U V : Over X} (a : U ⟶ V)
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N) :
    Module.MapSlicePullback.moduleMapPullbackAlong a φ = pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) φ a.left U.hom U.hom a.w a.w := by
  rw [Picard.PoincareBundle.Geometric.PullHom.pullHom_eq]
  simp only [Module.MapSlicePullback.moduleMapPullbackAlong, Module.MapPullbackCongruence.moduleMapPullbackCongr, Module.MapPullbackComposition.moduleMapPullbackComp,
    Iso.homCongr_apply, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    NatTrans.comp_app, Category.assoc]

namespace NativeModuleDescentRecovery

theorem conjugate_identity {K : Type*} [Category* K] {X Y : K}
    (r : X ≅ Y) (a : Y ⟶ Y) (ha : a = 𝟙 Y) : r.hom ≫ a ≫ r.inv = 𝟙 X := by
  rw [ha, Category.id_comp, r.hom_inv_id]

theorem conjugate_composition {K : Type*} [Category* K] {X Y Z A B C : K}
    (r : X ≅ A) (s : Y ≅ B) (t : Z ≅ C) (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (hc : a ≫ b = c) :
    (r.hom ≫ a ≫ s.inv) ≫ (s.hom ≫ b ≫ t.inv) = r.hom ≫ c ≫ t.inv := by
  simp only [Category.assoc, s.inv_hom_id_assoc]
  rw [← Category.assoc a, hc]

variable {X : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData f) (M : ι → X.Modules)
  (r : ∀ i, (Scheme.Modules.pullback (f i)).obj (M i) ≅ D.obj i)

def recoveryWithIdentity (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (M i) ≅
      (Scheme.Modules.pullback (𝟙 (Y i))).obj (D.obj i) :=
  r i ≪≫ (Scheme.Modules.pullbackId (Y i)).symm.app (D.obj i)

def recoveryAt {T : Scheme.{u}} (q : T ⟶ X) (i : ι) (a : T ⟶ Y i) (ha : a ≫ f i = q) :
    (Scheme.Modules.pullback q).obj (M i) ≅ (Scheme.Modules.pullback a).obj (D.obj i) :=
  Picard.PoincareBundle.PullbackFiberComposition.pullIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (recoveryWithIdentity D M r i) a q a ha (Category.comp_id a)

theorem recoveryAt_hom_pullback {T U : Scheme.{u}}
    (t : U ⟶ T) (q : T ⟶ X) (q' : U ⟶ X) (hq : t ≫ q = q')
    (i : ι) (a : T ⟶ Y i) (ha : a ≫ f i = q)
    (a' : U ⟶ Y i) (ha' : a' ≫ f i = q') (hat : t ≫ a = a') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryAt D M r q i a ha).hom t q' a' hq hat =
      (recoveryAt D M r q' i a' ha').hom := by
  subst a'
  exact pullHom_pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryWithIdentity D M r i).hom
    a q a t q' (t ≫ a) ha (Category.comp_id a) hq rfl

theorem recoveryAt_inv_pullback {T U : Scheme.{u}}
    (t : U ⟶ T) (q : T ⟶ X) (q' : U ⟶ X) (hq : t ≫ q = q')
    (i : ι) (a : T ⟶ Y i) (ha : a ≫ f i = q)
    (a' : U ⟶ Y i) (ha' : a' ≫ f i = q') (hat : t ≫ a = a') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryAt D M r q i a ha).inv t a' q' hat hq =
      (recoveryAt D M r q' i a' ha').inv := by
  subst a'
  exact pullHom_pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryWithIdentity D M r i).inv
    a a q t (t ≫ a) q' (Category.comp_id a) ha rfl hq

/-- The original descent isomorphism expressed on actual ambient
pullbacks, rather than on independently specified local sheaves. -/
def ambientIso {T : Scheme.{u}} (q : T ⟶ X) (i j : ι)
    (a : T ⟶ Y i) (b : T ⟶ Y j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (Scheme.Modules.pullback q).obj (M i) ≅ (Scheme.Modules.pullback q).obj (M j) :=
  recoveryAt D M r q i a ha ≪≫ D.iso q a b ha hb ≪≫ (recoveryAt D M r q j b hb).symm

theorem ambientIso_self {T : Scheme.{u}} (q : T ⟶ X) (i : ι)
    (a : T ⟶ Y i) (ha : a ≫ f i = q) :
    ambientIso D M r q i i a a ha ha = Iso.refl _ := by
  apply Iso.ext
  exact conjugate_identity (recoveryAt D M r q i a ha) (D.hom q a a ha ha) (D.hom_self q a ha)

theorem ambientIso_comp {T : Scheme.{u}} (q : T ⟶ X) (i j k : ι)
    (a : T ⟶ Y i) (b : T ⟶ Y j) (c : T ⟶ Y k)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    (ambientIso D M r q i j a b ha hb).hom ≫ (ambientIso D M r q j k b c hb hc).hom =
      (ambientIso D M r q i k a c ha hc).hom := by
  exact conjugate_composition (recoveryAt D M r q i a ha) (recoveryAt D M r q j b hb)
    (recoveryAt D M r q k c hc) (D.hom q a b ha hb) (D.hom q b c hb hc)
    (D.hom q a c ha hc) (D.hom_comp q a b c ha hb hc)

theorem ambientIso_pullback {T U : Scheme.{u}}
    (t : U ⟶ T) (q : T ⟶ X) (q' : U ⟶ X) (hq : t ≫ q = q')
    (i j : ι) (a : T ⟶ Y i) (b : T ⟶ Y j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q)
    (a' : U ⟶ Y i) (b' : U ⟶ Y j)
    (ha' : a' ≫ f i = q') (hb' : b' ≫ f j = q') (hat : t ≫ a = a') (hbt : t ≫ b = b') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (ambientIso D M r q i j a b ha hb).hom t q' q' hq hq =
      (ambientIso D M r q' i j a' b' ha' hb').hom := by
  have h₁ := Picard.PoincareBundle.PullHom.pullHom_comp (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks)
    (recoveryAt D M r q i a ha).hom
    (D.hom q a b ha hb ≫ (recoveryAt D M r q j b hb).inv) t q' a' q' hq hat hq
  have h₂ := Picard.PoincareBundle.PullHom.pullHom_comp (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (D.hom q a b ha hb)
    (recoveryAt D M r q j b hb).inv t a' b' q' hat hbt hq
  have hi := recoveryAt_hom_pullback D M r t q q' hq i a ha a' ha' hat
  have hj := recoveryAt_inv_pullback D M r t q q' hq j b hb b' hb' hbt
  have hd := D.pullHom_hom t q q' hq a b ha hb a' b' hat hbt
  exact h₁.trans (congrArg₂ (fun x y => x ≫ y) hi
    (h₂.trans (congrArg₂ (fun x y => x ≫ y) hd hj)))

end NativeModuleDescentRecovery

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery
end ComponentSource_31

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery"

@[expose] public section ComponentSource_32
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf -/

/-! # Ring Module Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf

noncomputable section

/-! Sections of a module sheaf form a sheaf of modules over the ring of global functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def globalRingModulePresheaf (M : X.Modules) :
    TopCat.Presheaf (ModuleCat Γ(X, ⊤)) X :=
  (PresheafOfModules.forgetToPresheafModuleCat (.op (⊤ : X.Opens)) isTerminalTop.op).obj M.val

def globalRingModulePresheafForgetIso (M : X.Modules) :
    globalRingModulePresheaf M ⋙ forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat ≅ M.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V f; ext m; rfl)

theorem globalRingModulePresheaf_isSheaf (M : X.Modules) :
    (globalRingModulePresheaf M).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat) (globalRingModulePresheaf M)).mpr
  exact (TopCat.Presheaf.isSheaf_iso_iff (globalRingModulePresheafForgetIso M)).mpr M.isSheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf
end ComponentSource_32

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf"

@[expose] public section ComponentSource_33
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf -/

/-! # Module Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

noncomputable section

/-! Module sections with coefficients in a chosen base ring satisfy the sheaf condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientModulePresheaf (f : R →+* Γ(X, ⊤)) (M : X.Modules) :
    TopCat.Presheaf (ModuleCat R) X :=
  Global.RingModulePresheaf.globalRingModulePresheaf M ⋙ ModuleCat.restrictScalars f

theorem coefficientModulePresheaf_isSheaf (f : R →+* Γ(X, ⊤)) (M : X.Modules) :
    (coefficientModulePresheaf f M).IsSheaf :=
  CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ (ModuleCat.restrictScalars f)
    (Global.RingModulePresheaf.globalRingModulePresheaf_isSheaf M)

def schemeCoefficientMap (p : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom

def schemeModulePresheaf (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    TopCat.Presheaf (ModuleCat R) X :=
  coefficientModulePresheaf (schemeCoefficientMap p) M

theorem schemeModulePresheaf_isSheaf (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    (schemeModulePresheaf p M).IsSheaf :=
  coefficientModulePresheaf_isSheaf (schemeCoefficientMap p) M

def coefficientPairwiseLimit (f : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    IsLimit ((coefficientModulePresheaf f M).mapCone (Pairwise.cocone U).op) :=
  Classical.choice ((coefficientModulePresheaf_isSheaf f M).isSheafPairwiseIntersections U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
end ComponentSource_33

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf"

@[expose] public section ComponentSource_34
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf -/

/-! # Algebra Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf

noncomputable section

/-! The structure sheaf as algebras over a chosen ring of coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientSectionMap (f : R →+* Γ(X, ⊤)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp f

theorem coefficientSectionMap_restrict (f : R →+* Γ(X, ⊤))
    {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (coefficientSectionMap f U) =
      coefficientSectionMap f V := by
  unfold coefficientSectionMap
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
  rfl

def coefficientAlgebraSections (f : R →+* Γ(X, ⊤)) (U : X.Opens) : CommAlgCat.{u} R :=
  letI := (coefficientSectionMap f U).toAlgebra
  .of R Γ(X, U)

def coefficientAlgebraRestriction (f : R →+* Γ(X, ⊤))
    {U V : X.Opens} (h : V ≤ U) :
    coefficientAlgebraSections f U ⟶ coefficientAlgebraSections f V := by
  letI := (coefficientSectionMap f U).toAlgebra
  letI := (coefficientSectionMap f V).toAlgebra
  exact CommAlgCat.ofHom {
    __ := (X.presheaf.map (homOfLE h).op).hom
    commutes' := fun r => DFunLike.congr_fun (coefficientSectionMap_restrict f h) r }

def coefficientAlgebraPresheaf (f : R →+* Γ(X, ⊤)) :
    TopCat.Presheaf (CommAlgCat.{u} R) X where
  obj U := coefficientAlgebraSections f U.unop
  map h := coefficientAlgebraRestriction f h.unop.le
  map_id U := by ext r; exact congrArg (fun k => k r) (X.presheaf.map_id U)
  map_comp h k := by ext r; exact congrArg (fun a => a r) (X.presheaf.map_comp h k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf
end ComponentSource_34

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf"

@[expose] public section ComponentSource_35
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules -/

/-! # Open Function Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules

noncomputable section

/-! Regular functions on a smaller open are modules over the functions on a larger open, with linear restriction maps. These are the local modules used to assemble homogeneous frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def relativeOpenFunctionModule (V W : X.Opens) (h : W ≤ V) : ModuleCat.{u} Γ(X, V) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj (ModuleCat.of Γ(X, W) Γ(X, W))

def relativeOpenFunctionRestriction (V : X.Opens) {W Z : X.Opens}
    (hW : W ≤ V) (hZ : Z ≤ V) (a : Z ≤ W) :
    relativeOpenFunctionModule V W hW ⟶ relativeOpenFunctionModule V Z hZ := by
  exact ModuleCat.ofHom (X := relativeOpenFunctionModule V W hW)
    (Y := relativeOpenFunctionModule V Z hZ) {
    toFun := X.presheaf.map (homOfLE a).op
    map_add' := map_add _
    map_smul' := fun r s => by
      change X.presheaf.map (homOfLE a).op
        (@Mul.mul Γ(X, W) inferInstance (X.presheaf.map (homOfLE hW).op r) s) =
          @Mul.mul Γ(X, Z) inferInstance (X.presheaf.map (homOfLE hZ).op r)
            (X.presheaf.map (homOfLE a).op s)
      have hm := (X.presheaf.map (homOfLE a).op).hom.map_mul
        (X.presheaf.map (homOfLE hW).op r) s
      exact hm.trans (congrArg (fun z : Γ(X, Z) => z * (X.presheaf.map (homOfLE a).op s))
        (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE hW).op (homOfLE a).op) r).symm) }

theorem relativeOpenFunctionRestriction_refl (V W : X.Opens) (h : W ≤ V) :
    relativeOpenFunctionRestriction V h h (le_refl W) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (.op W)) x

theorem relativeOpenFunctionRestriction_comp (V : X.Opens) {W Z Q : X.Opens}
    (hW : W ≤ V) (hZ : Z ≤ V) (hQ : Q ≤ V) (a : Z ≤ W) (b : Q ≤ Z) :
    relativeOpenFunctionRestriction V hW hZ a ≫ relativeOpenFunctionRestriction V hZ hQ b =
      relativeOpenFunctionRestriction V hW hQ (b.trans a) := by
  apply ModuleCat.hom_ext
  ext x
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE a).op (homOfLE b).op) x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules
end ComponentSource_35

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules"

@[expose] public section ComponentSource_36
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars -/

set_option backward.isDefEq.respectTransparency false

/-! # Open Function Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars

noncomputable section

/-! Multiplication by a local function is linear over functions on a containing open and commutes with restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def relativeOpenFunctionScalar (V W : X.Opens) (h : W ≤ V) (a : Γ(X, W)) :
    (OpenFunctionModules.relativeOpenFunctionModule V W h ⟶
      OpenFunctionModules.relativeOpenFunctionModule V W h) :=
  ModuleCat.ofHom (X := OpenFunctionModules.relativeOpenFunctionModule V W h) (Y := OpenFunctionModules.relativeOpenFunctionModule V W h) {
    toFun := @Mul.mul Γ(X, W) inferInstance a
    map_add' := mul_add a
    map_smul' := fun r x => by
      change @Mul.mul Γ(X, W) inferInstance a
          (@Mul.mul Γ(X, W) inferInstance (X.presheaf.map (homOfLE h).op r) x) =
        @Mul.mul Γ(X, W) inferInstance (X.presheaf.map (homOfLE h).op r)
          (@Mul.mul Γ(X, W) inferInstance a x)
      exact mul_left_comm a (X.presheaf.map (homOfLE h).op r) x }

theorem relativeOpenFunctionScalar_restriction (V : X.Opens) {W Z : X.Opens}
    (hW : W ≤ V) (hZ : Z ≤ V) (h : Z ≤ W) (a : Γ(X, W)) :
    relativeOpenFunctionScalar V W hW a ≫ OpenFunctionModules.relativeOpenFunctionRestriction V hW hZ h =
      OpenFunctionModules.relativeOpenFunctionRestriction V hW hZ h ≫
        relativeOpenFunctionScalar V Z hZ (X.presheaf.map (homOfLE h).op a) := by
  apply ModuleCat.hom_ext
  ext x
  exact (X.presheaf.map (homOfLE h).op).hom.map_mul a x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars
end ComponentSource_36

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars"

@[expose] public section ComponentSource_37
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits -/

/-! # Open Function Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

noncomputable section

/-! Restricting regular functions is a linear map from the containing open's free rank-one module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def relativeOpenFunctionUnitMap (V W : X.Opens) (h : W ≤ V) :
    Γ(X, V) →ₗ[Γ(X, V)] OpenFunctionModules.relativeOpenFunctionModule V W h where
  toFun := X.presheaf.map (homOfLE h).op
  map_add' := (X.presheaf.map (homOfLE h).op).hom.map_add
  map_smul' := (X.presheaf.map (homOfLE h).op).hom.map_mul

theorem openFunction_restriction_comp {V W Z : X.Opens} (a : W ≤ V) (b : Z ≤ W) (r : Γ(X, V)) :
    X.presheaf.map (homOfLE b).op (X.presheaf.map (homOfLE a).op r) =
      X.presheaf.map (homOfLE (b.trans a)).op r :=
  (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE a).op (homOfLE b).op) r).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits
end ComponentSource_37

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits"

@[expose] public section ComponentSource_38
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf -/

/-! # Matching Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf

noncomputable section

/-! Effective Zariski gluing of module objects, in section coordinates.
Each local module is allowed to be presented as an ambient pushforward.
The matching equations use actual linear equivalences on common opens;
their compatible sections form a genuine sheaf of modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
universe u

structure OpenModuleTransitions {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M : ι → X.Modules) where
  compare : ∀ (V : X.Opens) (i j : ι), V ≤ U i → V ≤ U j →
    Γ(M i, V) ≃ₗ[Γ(X, V)] Γ(M j, V)
  natural : ∀ (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(M i, V)),
    compare W i j (h.trans hi) (h.trans hj) ((M i).presheaf.map (homOfLE h).op s) =
      (M j).presheaf.map (homOfLE h).op (compare V i j hi hj s)
  identity : ∀ (V : X.Opens) (i : ι) (hi : V ≤ U i) (s : Γ(M i, V)),
    compare V i i hi hi s = s
  composition : ∀ (V : X.Opens) (i j k : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) (s : Γ(M i, V)),
    compare V j k hj hk (compare V i j hi hj s) = compare V i k hi hk s

namespace OpenModuleTransitions
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}

theorem restriction_comp (A : X.Modules) {V W Z : X.Opens}
    (h : W ≤ V) (k : Z ≤ W) (s : Γ(A, V)) :
    A.presheaf.map (homOfLE k).op (A.presheaf.map (homOfLE h).op s) =
      A.presheaf.map (homOfLE (k.trans h)).op s :=
  (ConcreteCategory.congr_hom (A.presheaf.map_comp (homOfLE h).op (homOfLE k).op) s).symm

theorem restriction_self (A : X.Modules) (V : X.Opens) (h : V ≤ V) (s : Γ(A, V)) :
    A.presheaf.map (homOfLE h).op s = s :=
  ConcreteCategory.congr_hom (A.presheaf.map_id (.op V)) s

theorem restriction_zero (A : X.Modules) {V W : X.Opens} (h : W ≤ V) :
    A.presheaf.map (homOfLE h).op (0 : Γ(A, V)) = 0 :=
  (A.presheaf.map (homOfLE h).op).hom.map_zero

theorem restriction_add (A : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (s t : Γ(A, V)) :
    A.presheaf.map (homOfLE h).op (s + t) =
      A.presheaf.map (homOfLE h).op s + A.presheaf.map (homOfLE h).op t :=
  (A.presheaf.map (homOfLE h).op).hom.map_add s t

abbrev relativeSections (A : X.Modules) (V W : X.Opens) (h : W ≤ V) : ModuleCat Γ(X, V) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj (A.val.obj (.op W))

abbrev Tuple (U : ι → X.Opens) (M : ι → X.Modules) (V : X.Opens) :=
  (i : ι) → relativeSections (M i) V (V ⊓ U i) inf_le_left

def tupleRestriction {V W : X.Opens} (h : W ≤ V) :
    Tuple U M V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Tuple U M W where
  toFun s i := (M i).presheaf.map (homOfLE (inf_le_inf h (le_refl (U i)))).op (s i)
  map_add' s t := funext (fun i => map_add _ (s i) (t i))
  map_smul' r s := by
    funext i
    let a : W ⊓ U i ≤ V ⊓ U i := inf_le_inf h (le_refl (U i))
    let si : Γ(M i, V ⊓ U i) := s i
    change (M i).presheaf.map (homOfLE a).op
        (@SMul.smul Γ(X, V ⊓ U i) Γ(M i, V ⊓ U i) inferInstance
          (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r) si) =
      (X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op
        (X.presheaf.map (homOfLE h).op r)) •
          (M i).presheaf.map (homOfLE a).op si
    exact (Scheme.Modules.map_smul (M i) (homOfLE a) _ si).trans
      (congrArg (fun z : Γ(X, W ⊓ U i) => z • (M i).presheaf.map (homOfLE a).op si)
        ((Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U i ≤ V from inf_le_left) a r).trans
          (Relative.OpenFunctionUnits.openFunction_restriction_comp h (show W ⊓ U i ≤ W from inf_le_left) r).symm))

theorem tupleRestriction_self (V : X.Opens) (s : Tuple U M V) :
    tupleRestriction (le_refl V) s = s := by
  funext i
  exact restriction_self (M i) _ _ _

theorem tupleRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (s : Tuple U M V) :
    tupleRestriction k (tupleRestriction h s) = tupleRestriction (k.trans h) s := by
  funext i
  exact restriction_comp (M i) _ _ _

variable (D : OpenModuleTransitions U M)

def sections (V : X.Opens) : Submodule Γ(X, V) (Tuple U M V) where
  carrier := {s | ∀ i j,
    D.compare ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right
      ((M i).presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op (s i)) =
    (M j).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j)}
  zero_mem' := by
    intro i j
    change D.compare _ i j _ _
      ((M i).presheaf.map _ (0 : Γ(M i, V ⊓ U i))) =
        (M j).presheaf.map _ (0 : Γ(M j, V ⊓ U j))
    rw [restriction_zero, restriction_zero, map_zero]
  add_mem' := by
    intro s t hs ht i j
    let Q := (V ⊓ U i) ⊓ U j
    let a := (M i).presheaf.map
      (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op
    let b := (M j).presheaf.map
      (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op
    let c := D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
    exact (congrArg c (a.hom.map_add (s i) (t i))).trans
      ((c.map_add (a (s i)) (a (t i))).trans
        ((congrArg₂ (fun x y : Γ(M j, Q) => x + y) (hs i j) (ht i j)).trans
          (b.hom.map_add (s j) (t j)).symm))
  smul_mem' := by
    intro r s hs i j
    let Q := (V ⊓ U i) ⊓ U j
    let si : Γ(M i, V ⊓ U i) := s i
    let sj : Γ(M j, V ⊓ U j) := s j
    have hs' : D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
        ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op si) =
      (M j).presheaf.map (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op sj := hs i j
    change D.compare Q i j _ _
        ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op
          (@SMul.smul Γ(X, V ⊓ U i) Γ(M i, V ⊓ U i) inferInstance
            (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r) si)) =
      (M j).presheaf.map (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op
          (@SMul.smul Γ(X, V ⊓ U j) Γ(M j, V ⊓ U j) inferInstance
            (X.presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op r) sj)
    let a : Q ≤ V ⊓ U i := inf_le_left
    let b : Q ≤ V ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    let ri : Γ(X, V ⊓ U i) :=
      X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r
    let rj : Γ(X, V ⊓ U j) :=
      X.presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op r
    let c := D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
    have hr : X.presheaf.map (homOfLE a).op ri = X.presheaf.map (homOfLE b).op rj :=
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U i ≤ V from inf_le_left) a r).trans
        (Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U j ≤ V from inf_le_left) b r).symm
    exact (congrArg c (Scheme.Modules.map_smul (M i) (homOfLE a) ri si)).trans
      ((c.map_smul _ _).trans
        ((congrArg₂ (fun (q : Γ(X, Q)) (x : Γ(M j, Q)) => q • x) hr hs').trans
          (Scheme.Modules.map_smul (M j) (homOfLE b) rj sj).symm))

theorem mem_sections (V : X.Opens) (s : Tuple U M V) :
    s ∈ D.sections V ↔ ∀ i j,
      D.compare ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right
        ((M i).presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op (s i)) =
      (M j).presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j) :=
  Iff.rfl

theorem tupleRestriction_mem {V W : X.Opens} (h : W ≤ V)
    (s : Tuple U M V) (hs : s ∈ D.sections V) : tupleRestriction h s ∈ D.sections W := by
  intro i j
  let Q := (V ⊓ U i) ⊓ U j
  let Z := (W ⊓ U i) ⊓ U j
  have a : Z ≤ Q := inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j))
  have hi : (M i).presheaf.map (homOfLE (show Z ≤ W ⊓ U i from inf_le_left)).op
      (tupleRestriction h s i) =
    (M i).presheaf.map (homOfLE a).op
      ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op (s i)) := by
    exact (restriction_comp (M i) _ _ _).trans (restriction_comp (M i) _ _ _).symm
  have hj : (M j).presheaf.map (homOfLE (show Z ≤ W ⊓ U j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (tupleRestriction h s j) =
    (M j).presheaf.map (homOfLE a).op
      ((M j).presheaf.map (homOfLE (show Q ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j)) := by
    exact (restriction_comp (M j) _ _ _).trans (restriction_comp (M j) _ _ _).symm
  exact (congrArg (D.compare Z i j _ _) hi).trans
    ((D.natural Q Z a i j _ _ _).trans
      ((congrArg ((M j).presheaf.map (homOfLE a).op) (hs i j)).trans hj.symm))

def sectionRestriction {V W : X.Opens} (h : W ≤ V) :
    D.sections V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] D.sections W :=
  ((tupleRestriction h).comp (D.sections V).subtype).codRestrict (D.sections W)
    (fun s => D.tupleRestriction_mem h s.val s.property)

theorem sectionRestriction_self (V : X.Opens) (s : D.sections V) :
    D.sectionRestriction (le_refl V) s = s :=
  Subtype.ext (tupleRestriction_self V s.val)

theorem sectionRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (s : D.sections V) :
    D.sectionRestriction k (D.sectionRestriction h s) = D.sectionRestriction (k.trans h) s :=
  Subtype.ext (tupleRestriction_comp h k s.val)

def modulePresheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (D.sections V.unop)
  map {V W} h := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, V.unop) (D.sections V.unop))
    (Y := (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj
      (ModuleCat.of Γ(X, W.unop) (D.sections W.unop)))
    { __ := (D.sectionRestriction h.unop.le).toAddMonoidHom
      map_smul' := (D.sectionRestriction h.unop.le).map_smul' }
  map_id V := by
    apply ModuleCat.hom_ext
    ext s
    exact D.sectionRestriction_self V.unop s
  map_comp {V W Z} h k := by
    apply ModuleCat.hom_ext
    ext s
    exact (D.sectionRestriction_comp h.unop.le k.unop.le s).symm

def tuplePresheaf (U : ι → X.Opens) (M : ι → X.Modules) : TopCat.Presheaf (Type u) X where
  obj V := Tuple U M V.unop
  map h := TypeCat.ofHom (tupleRestriction h.unop.le)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    exact tupleRestriction_self V.unop s
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (tupleRestriction_comp h.unop.le k.unop.le s).symm

theorem tuplePresheaf_isSheaf : (tuplePresheaf U M).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  have hcoord (i : ι) : ∃! t : Γ(M i, (iSup V) ⊓ U i), ∀ a,
      (M i).presheaf.map (homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i)))).op t = s a i := by
    let F : TopCat.Sheaf AddCommGrpCat X := ⟨(M i).presheaf, (M i).isSheaf⟩
    apply F.existsUnique_gluing' (fun a => V a ⊓ U i) ((iSup V) ⊓ U i)
      (fun a => homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i))))
    · intro x hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx.1
      exact Opens.mem_iSup.mpr ⟨a, ha, hx.2⟩
    · intro a b
      let Z := (V a ⊓ U i) ⊓ (V b ⊓ U i)
      have hz : Z ≤ (V a ⊓ V b) ⊓ U i :=
        le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right)
      have he := congrArg (fun t : Tuple U M (V a ⊓ V b) => t i) (hs a b)
      have hr := congrArg ((M i).presheaf.map (homOfLE hz).op) he
      exact (restriction_comp (M i) _ _ _).symm.trans
        (hr.trans (restriction_comp (M i) _ _ _))
  choose t ht hu using hcoord
  refine ⟨t, ?_, ?_⟩
  · intro a
    funext i
    exact ht i a
  · intro q hq
    funext i
    exact hu i (q i) (fun a => congrFun (hq a) i)

theorem mem_sections_of_locally {V : X.Opens} {α : Type u}
    (W : α → X.Opens) (hW : ∀ a, W a ≤ V) (hcover : V ≤ iSup W)
    (s : Tuple U M V) (hs : ∀ a, tupleRestriction (hW a) s ∈ D.sections (W a)) :
    s ∈ D.sections V := by
  intro i j
  let Z := (V ⊓ U i) ⊓ U j
  let Q := fun a => (W a ⊓ U i) ⊓ U j
  have hQ (a : α) : Q a ≤ Z := inf_le_inf (inf_le_inf (hW a) (le_refl (U i))) (le_refl (U j))
  have hc : Z ≤ iSup Q := by
    intro z hz
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcover hz.1.1)
    exact Opens.mem_iSup.mpr ⟨a, ⟨ha, hz.1.2⟩, hz.2⟩
  let Fj : TopCat.Sheaf AddCommGrpCat X := ⟨(M j).presheaf, (M j).isSheaf⟩
  apply Fj.eq_of_locally_eq' Q Z (fun a => homOfLE (hQ a)) hc
  intro a
  have hi : (M i).presheaf.map (homOfLE (show Q a ≤ W a ⊓ U i from inf_le_left)).op
      (tupleRestriction (hW a) s i) =
    (M i).presheaf.map (homOfLE (hQ a)).op
      ((M i).presheaf.map (homOfLE (show Z ≤ V ⊓ U i from inf_le_left)).op (s i)) := by
    exact (restriction_comp (M i) _ _ _).trans (restriction_comp (M i) _ _ _).symm
  have hj : (M j).presheaf.map (homOfLE (show Q a ≤ W a ⊓ U j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (tupleRestriction (hW a) s j) =
    (M j).presheaf.map (homOfLE (hQ a)).op
      ((M j).presheaf.map (homOfLE (show Z ≤ V ⊓ U j from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (s j)) := by
    exact (restriction_comp (M j) _ _ _).trans (restriction_comp (M j) _ _ _).symm
  exact (D.natural Z (Q a) (hQ a) i j _ _ _).symm.trans
    ((congrArg (D.compare (Q a) i j _ _) hi.symm).trans ((hs a i j).trans hj))

def sectionTypePresheaf : TopCat.Presheaf (Type u) X :=
  (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj D.modulePresheaf ⋙ forget AddCommGrpCat

theorem sectionTypePresheaf_isSheaf : D.sectionTypePresheaf.IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  change ∀ a b, D.sectionRestriction (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
    D.sectionRestriction (show V a ⊓ V b ≤ V b from inf_le_right) (s b) at hs
  have hv : (tuplePresheaf U M).IsCompatible V (fun a => (s a).val) := by
    intro a b
    exact congrArg Subtype.val (hs a b)
  obtain ⟨t, ht, hu⟩ := (tuplePresheaf_isSheaf (U := U) (M := M)).isSheafUniqueGluing_types
    (fun a => (s a).val) hv
  have hmem : t ∈ D.sections (iSup V) := D.mem_sections_of_locally V (fun a => le_iSup V a)
    le_rfl t (fun a => (ht a).symm ▸ (s a).property)
  refine ⟨⟨t, hmem⟩, ?_, ?_⟩
  · intro a
    exact Subtype.ext (ht a)
  · intro q hq
    apply Subtype.ext
    exact hu q.val (fun a => congrArg Subtype.val (hq a))

/-- The actual module object formed by matching local sections. -/
def moduleSheaf : X.Modules where
  val := D.modulePresheaf
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat) _).mpr
    D.sectionTypePresheaf_isSheaf

end OpenModuleTransitions

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf
end ComponentSource_38

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingSheaf"

@[expose] public section ComponentSource_39
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions -/

/-! # Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

noncomputable section

/-! Transition units for local frames, expressed on arbitrary common subopens so restriction and cocycle identities have one common section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v}

structure OpenFrameTransitions (U : ι → X.Opens) where
  value : ∀ (V : X.Opens) (i j : ι), V ≤ U i → V ≤ U j → Γ(X, V)ˣ
  restrict : ∀ (V W : X.Opens) (h : W ≤ V) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j),
    X.presheaf.map (homOfLE h).op (value V i j hi hj).val =
      (value W i j (h.trans hi) (h.trans hj)).val
  self : ∀ (V : X.Opens) (i : ι) (hi : V ≤ U i), value V i i hi hi = 1
  comp : ∀ (V : X.Opens) (i j k : ι) (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
    value V i j hi hj * value V j k hj hk = value V i k hi hk

namespace OpenFrameTransitions

variable {U : ι → X.Opens} (D : OpenFrameTransitions U)

theorem inverse (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    (D.value V i j hi hj)⁻¹ = D.value V j i hj hi := by
  apply (inv_eq_iff_mul_eq_one).mpr
  exact (D.comp V i j i hi hj hi).trans (D.self V i hi)

def trivial (U : ι → X.Opens) : OpenFrameTransitions U where
  value _ _ _ _ _ := 1
  restrict _ _ _ _ _ _ _ := map_one _
  self _ _ _ := rfl
  comp _ _ _ _ _ _ _ := one_mul 1

end OpenFrameTransitions

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions
end ComponentSource_39

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions"

@[expose] public section ComponentSource_40
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules -/

/-! # Section Modules -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules

noncomputable section

/-! Compatible regular-function coordinates for a frame cocycle form actual modules over the functions on each open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

abbrev OpenFrameLocalTuple (V : X.Opens) :=
  (i : ι) → Relative.OpenFunctionModules.relativeOpenFunctionModule V (V ⊓ U i) inf_le_left

def openFrameDifference (D : Transitions.OpenFrameTransitions U) (V : X.Opens) (i j : ι) :
    OpenFrameLocalTuple U V →ₗ[Γ(X, V)] Relative.OpenFunctionModules.relativeOpenFunctionModule V ((V ⊓ U i) ⊓ U j)
      (inf_le_left.trans inf_le_left) :=
  (Relative.OpenFunctionModules.relativeOpenFunctionRestriction V inf_le_left (inf_le_left.trans inf_le_left) inf_le_left).hom.comp
      (LinearMap.proj i) -
    (Relative.OpenFunctionScalars.relativeOpenFunctionScalar V ((V ⊓ U i) ⊓ U j) (inf_le_left.trans inf_le_left)
      (D.value ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right).val).hom.comp
        ((Relative.OpenFunctionModules.relativeOpenFunctionRestriction V inf_le_left (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).hom.comp (LinearMap.proj j))

def openFrameSectionModule (D : Transitions.OpenFrameTransitions U) (V : X.Opens) : Submodule Γ(X, V) (OpenFrameLocalTuple U V) :=
  ⨅ i, ⨅ j, (openFrameDifference U D V i j).ker

theorem openFrameSectionModule_mem_iff (D : Transitions.OpenFrameTransitions U) (V : X.Opens) (x : OpenFrameLocalTuple U V) :
    x ∈ openFrameSectionModule U D V ↔ ∀ i j,
      X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op (x i) =
        (D.value ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right).val *
          X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U j from
            le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (x j) := by
  simp only [openFrameSectionModule, Submodule.mem_iInf, LinearMap.mem_ker]
  apply forall₂_congr
  intro i j
  exact sub_eq_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules
end ComponentSource_40

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionModules"

@[expose] public section ComponentSource_41
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions -/

/-! # Tuple Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions

noncomputable section

/-! Coordinate tuples restrict semilinearly along inclusions of opens, with the actual restriction homomorphism on coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

def openFrameTupleRestriction {V W : X.Opens} (h : W ≤ V) :
    SectionModules.OpenFrameLocalTuple U V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] SectionModules.OpenFrameLocalTuple U W where
  toFun s i := X.presheaf.map (homOfLE (inf_le_inf h (le_refl (U i)))).op (s i)
  map_add' s t := funext (fun i => (X.presheaf.map (homOfLE (inf_le_inf h (le_refl (U i)))).op).hom.map_add (s i) (t i))
  map_smul' r s := by
    funext i
    let a : W ⊓ U i ≤ V ⊓ U i := inf_le_inf h (le_refl (U i))
    change X.presheaf.map (homOfLE a).op
        (@Mul.mul Γ(X, V ⊓ U i) inferInstance
          (X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op r) (s i)) =
      @Mul.mul Γ(X, W ⊓ U i) inferInstance
        (X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op
          (X.presheaf.map (homOfLE h).op r))
        (X.presheaf.map (homOfLE a).op (s i))
    have hc := (Relative.OpenFunctionUnits.openFunction_restriction_comp (show V ⊓ U i ≤ V from inf_le_left) a r).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp h (show W ⊓ U i ≤ W from inf_le_left) r).symm
    exact ((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).trans
      (congrArg (fun z : Γ(X, W ⊓ U i) => z * (X.presheaf.map (homOfLE a).op (s i))) hc)

theorem openFrameTupleRestriction_refl (V : X.Opens) (s : SectionModules.OpenFrameLocalTuple U V) :
    openFrameTupleRestriction U (le_refl V) s = s := by
  funext i
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (.op (V ⊓ U i))) (s i)

theorem openFrameTupleRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (s : SectionModules.OpenFrameLocalTuple U V) :
    openFrameTupleRestriction U k (openFrameTupleRestriction U h s) =
      openFrameTupleRestriction U (k.trans h) s := by
  funext i
  exact Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U i))) (inf_le_inf k (le_refl (U i))) (s i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions
end ComponentSource_41

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleRestrictions"

@[expose] public section ComponentSource_42
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility -/

/-! # Restriction Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility

noncomputable section

/-! Restricting frame coordinates preserves their transition compatibility, so the compatible section modules have actual restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameTupleRestriction_preserves {V W : X.Opens} (h : W ≤ V)
    (x : SectionModules.OpenFrameLocalTuple U V) (hx : x ∈ SectionModules.openFrameSectionModule U D V) :
    TupleRestrictions.openFrameTupleRestriction U h x ∈ SectionModules.openFrameSectionModule U D W := by
  apply (SectionModules.openFrameSectionModule_mem_iff U D W _).mpr
  intro i j
  let Q := (V ⊓ U i) ⊓ U j
  let Z := (W ⊓ U i) ⊓ U j
  have a : Z ≤ Q := inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j))
  have qj : Q ≤ V ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have zj : Z ≤ W ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hi := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U i)))
    (show Z ≤ W ⊓ U i from inf_le_left) (x i)).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show Q ≤ V ⊓ U i from inf_le_left) a (x i)).symm
  have hj := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U j))) zj (x j)).trans
    (Relative.OpenFunctionUnits.openFunction_restriction_comp qj a (x j)).symm
  have hc := (SectionModules.openFrameSectionModule_mem_iff U D V x).mp hx i j
  have he := congrArg (fun z : Γ(X, Q) => X.presheaf.map (homOfLE a).op z) hc
  have ht := D.restrict Q Z a i j (inf_le_left.trans inf_le_right) inf_le_right
  exact hi.trans (he.trans (((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).trans
    (congrArg₂ (fun r s : Γ(X, Z) => r * s) ht hj.symm)))

def openFrameSectionRestriction {V W : X.Opens} (h : W ≤ V) :
    SectionModules.openFrameSectionModule U D V →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] SectionModules.openFrameSectionModule U D W :=
  ((TupleRestrictions.openFrameTupleRestriction U h).comp (SectionModules.openFrameSectionModule U D V).subtype).codRestrict
    (SectionModules.openFrameSectionModule U D W) (fun x => openFrameTupleRestriction_preserves D h x.val x.property)

theorem openFrameSectionRestriction_refl (V : X.Opens) (x : SectionModules.openFrameSectionModule U D V) :
    openFrameSectionRestriction D (le_refl V) x = x :=
  Subtype.ext (TupleRestrictions.openFrameTupleRestriction_refl U V x.val)

theorem openFrameSectionRestriction_comp {V W Z : X.Opens} (h : W ≤ V) (k : Z ≤ W)
    (x : SectionModules.openFrameSectionModule U D V) :
    openFrameSectionRestriction D k (openFrameSectionRestriction D h x) =
      openFrameSectionRestriction D (k.trans h) x :=
  Subtype.ext (TupleRestrictions.openFrameTupleRestriction_comp U h k x.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility
end ComponentSource_42

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility"

@[expose] public section ComponentSource_43
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf -/

/-! # Module Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf

noncomputable section

/-! Compatible frame-coordinate modules and their restriction maps form an actual presheaf of modules on the scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def openFrameModulePresheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (SectionModules.openFrameSectionModule U D V.unop)
  map {V W} h := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, V.unop) (SectionModules.openFrameSectionModule U D V.unop))
    (Y := (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj
      (ModuleCat.of Γ(X, W.unop) (SectionModules.openFrameSectionModule U D W.unop))) {
      __ := (RestrictionCompatibility.openFrameSectionRestriction D h.unop.le).toAddMonoidHom
      map_smul' := (RestrictionCompatibility.openFrameSectionRestriction D h.unop.le).map_smul' }
  map_id V := by
    apply ModuleCat.hom_ext
    ext x
    exact RestrictionCompatibility.openFrameSectionRestriction_refl D V.unop x
  map_comp {V W Z} h k := by
    apply ModuleCat.hom_ext
    ext x
    exact (RestrictionCompatibility.openFrameSectionRestriction_comp D h.unop.le k.unop.le x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf
end ComponentSource_43

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModulePresheaf.openFrameModulePresheaf, "definition")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "a263d6a1f353768ab7e2abe49be10196"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:a263d6a1f353768ab7e2abe49be10196"
