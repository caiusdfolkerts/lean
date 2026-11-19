module

public import ToricPower.SchemeAffineLinear
public import ToricPower.FiniteAffineIntersectionSections
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# The literal affine tilde comparison over the base field

The usual map from a module to the global sections of its associated
sheaf is linear for the actual base-field action. The natural
isomorphism below retains `tilde.toOpen M ⊤` as its forward map; there
is no independent choice of section coordinates. It applies to every
module and therefore to arbitrary complexes, without finiteness or
boundedness hypotheses.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

namespace ToricPower

universe u

variable (k : Type u) [Field k] (R : CommRingCat.{u}) [Algebra k R]

/-- The ordinary affine section map, with its literal base-field scalar
structure on both sides. -/
def affineTildeBaseSectionsLinearEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap k R)).obj M ≃ₗ[k]
      (FiniteCover.schemeBaseSections k (Spec R) ⊤).obj (tilde M) where
  toEquiv := (tilde.isoTop M).toLinearEquiv.toEquiv
  map_add' := (tilde.isoTop M).toLinearEquiv.map_add
  map_smul' r x := by
    change M at x
    change (tilde.toOpen M ⊤) ((algebraMap k R r) • x) =
      (Spec R).presheaf.map (𝟙 (op ⊤))
        (Scheme.Modules.baseRingToGlobalSections k (Spec R) r) •
          (show Γ(tilde M, ⊤) from tilde.toOpen M ⊤ x)
    rw [map_smul, CategoryTheory.Functor.map_id, CommRingCat.id_apply,
      TauCeti.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections_Spec_apply]
    exact (IsScalarTower.algebraMap_smul Γ(Spec R, ⊤) (algebraMap k R r)
      (show Γ(tilde M, ⊤) from tilde.toOpen M ⊤ x)).symm

/-- Natural in every actual module and its actual linear maps. -/
def affineTildeBaseSectionsIso :
    ModuleCat.restrictScalars (algebraMap k R) ≅
      tilde.functor R ⋙ FiniteCover.schemeBaseSections k (Spec R) ⊤ :=
  NatIso.ofComponents
    (fun M => (affineTildeBaseSectionsLinearEquiv k R M).toModuleIso)
    (by
      intro M N f
      ext x
      exact ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤).symm x)

/-- The comparison is exactly the original affine section map on every
element, hence in particular on every chosen module generator. -/
@[simp]
theorem affineTildeBaseSectionsIso_hom_apply (M : ModuleCat.{u} R) (x : M) :
    (affineTildeBaseSectionsIso k R).hom.app M x = tilde.toOpen M ⊤ x := rfl

/-- The inverse recovers the original element from its actual section. -/
@[simp]
theorem affineTildeBaseSectionsIso_inv_toOpen (M : ModuleCat.{u} R) (x : M) :
    (affineTildeBaseSectionsIso k R).inv.app M (tilde.toOpen M ⊤ x) = x :=
  (affineTildeBaseSectionsLinearEquiv k R M).symm_apply_apply x

/-- The same natural comparison on all complexes, with every
differential retained. -/
def affineTildeBaseComplexSectionsIso {I : Type*} (shape : ComplexShape I) :
    (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex shape ≅
      (tilde.functor R ⋙ FiniteCover.schemeBaseSections k (Spec R) ⊤).mapHomologicalComplex
        shape :=
  NatIso.mapHomologicalComplex (affineTildeBaseSectionsIso k R) shape

end ToricPower

end
