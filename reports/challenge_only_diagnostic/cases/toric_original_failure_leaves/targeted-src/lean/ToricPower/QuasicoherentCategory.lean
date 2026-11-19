module

public import ToricPower.CoherentRestriction
public import ToricPower.ExactDerivedConservative
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Actual quasicoherent sheaves, colimits, and their derived inclusion

Quasicoherence is proved stable under all small colimits by restricting to
affine opens. On a spectrum, the colimit is explicitly the associated sheaf
of the colimit of the coordinate modules: the tilde--sections counit gives
the diagram isomorphism, and tilde preserves colimits as a left adjoint.

Together with the already proved ambient kernel and cokernel closure, this
gives the actual abelian category `QCoh X`, its actual small colimits, and
the exact inclusion into all module sheaves. Its unbounded derived category
is the localization of complexes of quasicoherent sheaves. The derived
inclusion is constructed, but it is not asserted to be an equivalence onto
the complexes with quasicoherent homology.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace ToricPower

universe u

section Colimits

variable {J : Type u} [SmallCategory J]

/-- On a spectrum the ambient colimit of actual quasicoherent sheaves is
the tilde of the colimit of their modules of global sections. -/
def quasicoherentColimitSpecIso (R : CommRingCat.{u})
    (K : J ⥤ (Spec R).Modules) [∀ j, (K.obj j).IsQuasicoherent] :
    AlgebraicGeometry.tilde
        (colimit (K ⋙ AlgebraicGeometry.moduleSpecΓFunctor (R := R))) ≅ colimit K := by
  let e : (K ⋙ AlgebraicGeometry.moduleSpecΓFunctor (R := R)) ⋙
      AlgebraicGeometry.tilde.functor R ≅ K :=
    NatIso.ofComponents
      (fun j => asIso (K.obj j).fromTildeΓ)
      (fun f => (AlgebraicGeometry.tilde.adjunction (R := R)).counit.naturality (K.map f))
  exact preservesColimitIso (AlgebraicGeometry.tilde.functor R)
      (K ⋙ AlgebraicGeometry.moduleSpecΓFunctor (R := R)) ≪≫
    HasColimit.isoOfNatIso e

theorem quasicoherent_colimit_spec (R : CommRingCat.{u})
    (K : J ⥤ (Spec R).Modules) [∀ j, (K.obj j).IsQuasicoherent] :
    (colimit K).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (quasicoherentColimitSpecIso R K) inferInstance

theorem quasicoherent_colimit_affine (X : Scheme.{u}) [IsAffine X]
    (K : J ⥤ X.Modules) [∀ j, (K.obj j).IsQuasicoherent] :
    (colimit K).IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  letI : ∀ j, ((K ⋙ F).obj j).IsQuasicoherent := fun j =>
    inferInstanceAs ((K.obj j).restrict X.isoSpec.inv).IsQuasicoherent
  have h : (F.obj (colimit K)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (preservesColimitIso F K).symm
      (quasicoherent_colimit_spec (.of Γ(X, ⊤)) (K ⋙ F))
  letI := h
  exact TauCeti.AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict_iso
    X.isoSpec (colimit K)

/-- Arbitrary small ambient colimits of quasicoherent sheaves are
quasicoherent. No Noetherian, separation, or properness hypothesis enters. -/
theorem quasicoherent_colimit (X : Scheme.{u}) (K : J ⥤ X.Modules)
    [∀ j, (K.obj j).IsQuasicoherent] : (colimit K).IsQuasicoherent := by
  apply TauCeti.AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict_affineOpens
    (colimit K)
  intro U
  let F := Scheme.Modules.restrictFunctor U.1.ι
  letI : ∀ j, ((K ⋙ F).obj j).IsQuasicoherent := fun j =>
    inferInstanceAs ((K.obj j).restrict U.1.ι).IsQuasicoherent
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (preservesColimitIso F K).symm
    (quasicoherent_colimit_affine U.1.toScheme (K ⋙ F))

instance quasicoherent_closedUnderColimitsOfShape (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro M ⟨p⟩
    letI : ∀ j, (p.diag.obj j).IsQuasicoherent := p.prop_diag_obj
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (p.isColimit.coconePointUniqueUpToIso (colimit.isColimit p.diag)).symm
      (quasicoherent_colimit X p.diag)

end Colimits

/-- The actual full subcategory of quasicoherent module sheaves. -/
abbrev QCoh (X : Scheme.{u}) := TauCeti.AlgebraicGeometry.QuasicoherentSheaf X

/-- The exact inclusion retains the actual sheaf and its actual morphisms. -/
abbrev quasicoherentInclusion (X : Scheme.{u}) : QCoh X ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

instance quasicoherentObject_property {X : Scheme.{u}} (M : QCoh X) :
    M.obj.IsQuasicoherent := M.property

instance quasicoherent_containsZero (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero where
  exists_zero := by
    letI := coherent_finitePresentation_of_isZero (0 : X.Modules) (isZero_zero _)
    exact ⟨0, isZero_zero _, inferInstance⟩

instance quasicoherent_closedUnderBinaryProducts (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro M ⟨p⟩
    letI := p.prop_diag_obj ⟨.left⟩
    letI := p.prop_diag_obj ⟨.right⟩
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      (Scheme.Modules.isQuasicoherent_biprod _ _)

instance quasicoherent_closedUnderFiniteProducts (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts := .mk'

/-- The actual category of quasicoherent sheaves is abelian, with ambient
kernels and cokernels, on every scheme. -/
instance quasicoherent_abelian (X : Scheme.{u}) : Abelian (QCoh X) := inferInstance

instance quasicoherent_hasColimits (X : Scheme.{u}) : HasColimits (QCoh X) where
  has_colimits_of_shape J _ := inferInstance

instance quasicoherentInclusion_preservesColimits (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u, u} (quasicoherentInclusion X) where
  preservesColimitsOfShape {J} _ := by
    letI : CreatesColimitsOfShape J (quasicoherentInclusion X) :=
      createsColimitsOfShapeFullSubcategoryInclusion J
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    exact preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _

instance quasicoherentInclusion_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (quasicoherentInclusion X) := by
  letI : ∀ {M N : QCoh X} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (quasicoherentInclusion X) :=
    fun f => (SheafOfModules.isQuasicoherent X.ringCatSheaf).preservesKernels_ι f
  exact CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels _

local instance quasicoherentStandardDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (QCoh X) := HasDerivedCategory.standard _

local instance moduleStandardDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The unbounded derived category of complexes of actual quasicoherent
sheaves. This notation is not an assertion of a comparison equivalence. -/
abbrev DerivedQCoh (X : Scheme.{u}) := DerivedCategory (QCoh X)

/-- The actual derived functor of the exact inclusion of quasicoherent
sheaves into all module sheaves. -/
def derivedQuasicoherentInclusion (X : Scheme.{u}) :
    DerivedQCoh X ⥤ DerivedCategory X.Modules :=
  (quasicoherentInclusion X).mapDerivedCategory

instance (X : Scheme.{u}) : (derivedQuasicoherentInclusion X).CommShift ℤ := by
  unfold derivedQuasicoherentInclusion
  infer_instance

instance (X : Scheme.{u}) : (derivedQuasicoherentInclusion X).IsTriangulated := by
  unfold derivedQuasicoherentInclusion
  infer_instance

/-- The actual derived inclusion detects zero objects. This follows from
faithfulness and exactness of the ordinary inclusion, without a derived
full-faithfulness or essential-surjectivity assumption. -/
theorem derivedQuasicoherentInclusion_isZero_iff (X : Scheme.{u})
    (K : DerivedQCoh X) :
    IsZero ((derivedQuasicoherentInclusion X).obj K) ↔ IsZero K :=
  exactDerived_isZero_iff (quasicoherentInclusion X) K

instance derivedQuasicoherentInclusion_reflectsIsomorphisms (X : Scheme.{u}) :
    (derivedQuasicoherentInclusion X).ReflectsIsomorphisms :=
  exactDerivedReflectsIsomorphisms (quasicoherentInclusion X)

/-- On an actual complex, the derived inclusion is the termwise
underlying-sheaf complex followed by the actual localization. -/
def derivedQuasicoherentInclusionComplexIso (X : Scheme.{u})
    (K : CochainComplex (QCoh X) ℤ) :
    (derivedQuasicoherentInclusion X).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((quasicoherentInclusion X).mapHomologicalComplex (.up ℤ)).obj K) :=
  (quasicoherentInclusion X).mapDerivedCategoryFactors.app K

end ToricPower

end
