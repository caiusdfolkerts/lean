module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback
public import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The actual projectivization of a quasicoherent module sheaf

On an affine open `U`, take `Proj Sym_{Γ(U)} Γ(M,U)`. Restriction to a
principal affine open is an actual localization of the module of sections.
The corresponding projective spectra form cartesian squares, so relative
scheme gluing constructs their global projectivization over the original
scheme. No projectivization or local comparison is postulated.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ProjectivizationOfModuleSheaf

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite
open OAI.AlgebraicGeometry.Divisors.LineBundles

variable {X : _root_.AlgebraicGeometry.Scheme.{0}} (M : X.Modules) [M.IsQuasicoherent]

/-- The actual projective symmetric scheme of the module of sections. -/
abbrev chart (U : X.AffineZariskiSite) : _root_.AlgebraicGeometry.Scheme :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme Γ(X, U.val) Γ(M, U.val)

/-- Restriction of a module section, with its actual semilinear scalar map. -/
def restriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Γ(M, V.val) →ₛₗ[(X.presheaf.map (homOfLE (toOpens_mono i.le)).op).hom]
      Γ(M, U.val) where
  toFun := M.presheaf.map (homOfLE (toOpens_mono i.le)).op
  map_add' := map_add _
  map_smul' a m := M.map_smul _ a m

/-- Quasicoherent restriction generates all sections after scalar extension. -/
theorem restriction_span {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Submodule.span Γ(X, U.val) (Set.range (restriction M i)) = ⊤ := by
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  letI : IsLocalization.Away r Γ(X, X.basicOpen r) := V.property.isLocalization_basicOpen r
  letI := _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict M V.property r
  exact SymmetricProjective.Localization.BundleCycles.localizedModule_span_range
    (S := Γ(X, X.basicOpen r)) (Submonoid.powers r) (M.basicOpenRestrict r)

/-- The degree-preserving map of the actual symmetric algebras. -/
def gradedRestriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap
    (X.presheaf.map (homOfLE (toOpens_mono i.le)).op).hom (restriction M i)

theorem gradedRestriction_irrelevant {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading Γ(X, U.val) Γ(M, U.val)) ≤
      (HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading Γ(X, V.val) Γ(M, V.val))).map
          (gradedRestriction M i) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _
    (restriction_span M i)

/-- The induced morphism between actual projective affine-base charts. -/
def chartMap {U V : X.AffineZariskiSite} (i : U ⟶ V) : chart M U ⟶ chart M V :=
  Proj.map (gradedRestriction M i) (gradedRestriction_irrelevant M i)

theorem gradedRestriction_id (U : X.AffineZariskiSite) :
    gradedRestriction M (𝟙 U) = GradedRingHom.id _ := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro a
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
      (algebraMap _ _ a) = algebraMap _ _ a
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ X.presheaf).map_id (.op U)) a
  · intro m
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
      (SymmetricAlgebra.ι _ _ m) = SymmetricAlgebra.ι _ _ m
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ M.presheaf).map_id (.op U)) m

theorem gradedRestriction_comp {U V W : X.AffineZariskiSite}
    (f : U ⟶ V) (g : V ⟶ W) :
    gradedRestriction M (f ≫ g) = (gradedRestriction M f).comp (gradedRestriction M g) := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro a
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (algebraMap _ _ a) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
        (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (algebraMap _ _ a))
    simp only [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ X.presheaf).map_comp g.op f.op) a
  · intro m
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (SymmetricAlgebra.ι _ _ m) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
        (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (SymmetricAlgebra.ι _ _ m))
    simp only [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ M.presheaf).map_comp g.op f.op) m

/-- The actual projective charts and restriction morphisms form a functor. -/
def diagram : X.AffineZariskiSite ⥤ _root_.AlgebraicGeometry.Scheme where
  obj U := chart M U
  map i := chartMap M i
  map_id U :=
    (_root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles.projectiveMap_congr (gradedRestriction_id M U) _
      (by simp)).trans Proj.map_id
  map_comp f g :=
    (_root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles.projectiveMap_congr (gradedRestriction_comp M f g) _
      (HomogeneousIdeal.irrelevant_le_map_comp (gradedRestriction_irrelevant M g)
        (gradedRestriction_irrelevant M f))).trans
      (Proj.map_comp (gradedRestriction M g) (gradedRestriction M f)
        (gradedRestriction_irrelevant M g) (gradedRestriction_irrelevant M f))

/-- The projection to the actual spectra of the base section rings. -/
def toCoefficients : diagram M ⟶
    toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ _root_.AlgebraicGeometry.Scheme.Spec where
  app U := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase Γ(X, U.val) Γ(M, U.val)
  naturality {_U _V} i :=
    SymmetricProjective.Base.BundleCycles.symmetricScalarProjectiveMap_over _ _
      (restriction_span M i)

/-- Principal localization gives the required genuine cartesian squares. -/
theorem toCoefficients_equifibered : (toCoefficients M).Equifibered := by
  intro U V i
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  letI : IsLocalization.Away r Γ(X, X.basicOpen r) := V.property.isLocalization_basicOpen r
  letI := _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict M V.property r
  exact (SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback
    (S := Γ(X, X.basicOpen r)) r (M.basicOpenRestrict r)).flip

/-- Relative scheme gluing data over the actual affine Zariski cover. -/
def glueData : (directedCover X).RelativeGluingData where
  functor := diagram M
  natTrans := toCoefficients M ≫ (restrictIsoSpec X).inv
  equifibered :=
    (toCoefficients_equifibered M).comp
      (NatTrans.Equifibered.of_isIso (restrictIsoSpec X).inv)

instance glueData_isLocallyDirected :
    ((glueData M).functor ⋙ _root_.AlgebraicGeometry.Scheme.forget).IsLocallyDirected :=
  _root_.AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The projectivization of the original quasicoherent sheaf. -/
def projectivization : _root_.AlgebraicGeometry.Scheme := (glueData M).glued

/-- Its actual morphism to the original base scheme. -/
def projection : projectivization M ⟶ X := (glueData M).toBase

/-- The projective affine-base charts form an actual open cover. -/
def openCover : (projectivization M).OpenCover := (glueData M).cover

/-- Each chart is exactly the pullback of the global projectivization to
the original affine open of the base. -/
theorem chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((glueData M).natTrans.app U) ((openCover M).f U) U.val.ι (projection M) :=
  (glueData M).isPullback_natTrans_ι_toBase U

end PaperVerification.ProjectivizationOfModuleSheaf
