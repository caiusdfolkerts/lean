module

public import TauCeti.AlgebraicGeometry.Modules.Restriction

/-! ## Source module `ToricPower.CoherentCategory`
Original SHA256: 0ccb445f9b4f8b2cb127554300e114135d91929fffa040b86e7d2c7e15630ad8.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource07

/-! # The actual abelian category of coherent sheaves

Finite presentation is the genuine local-presentation predicate on sheaves of
modules. Over a locally Noetherian scheme its closure under ambient kernels and
cokernels gives the ordinary abelian category of coherent sheaves. The bounded
derived category below is built by Mathlib's localization of complexes in that
actual abelian category. No categorical generation assertion is assumed.

The affine-to-slice presentation transport is adapted, with the same maps,
from TauCeti's `Modules.Quasicoherent.Pushforward.Finite`; the hypothesis used
here is simply finite presentation on the affine open itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
open scoped ZeroObject

namespace ToricPower

universe u

local instance affineOpenFromSpecIsOpenImmersion {X : Scheme.{u}} (U : X.affineOpens) :
    IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec

/-- The zero module sheaf has the finite presentation on no generators. -/
theorem coherent_finitePresentation_of_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : IsZero M) : M.IsFinitePresentation := by
  let F : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) (PEmpty : Type u)
  have hF : IsZero F := by
    apply (IsZero.iff_id_eq_zero F).mpr
    apply (SheafOfModules.freeHomEquiv F).injective
    funext j
    exact PEmpty.elim j
  have hFP : F.IsFinitePresentation := by
    dsimp only [F]
    infer_instance
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (hF.iso hM) hFP

section LocalPresentation

variable {X Y : Scheme.{u}}

theorem finitePresentation_restrict (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) [M.IsFinitePresentation] : (M.restrict f).IsFinitePresentation := by
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback f).app M).symm
    (Scheme.Modules.isFinitePresentation_pullback f M)

/-- A finite presentation on the actual affine open gives one on its slice
site. All transporting functors preserve the displayed cokernel presentation. -/
theorem finitePresentation_over_of_fromSpec (M : X.Modules) (U : X.affineOpens)
    [hM : (M.restrict U.2.fromSpec).IsFinitePresentation] :
    (M.over U.1).IsFinitePresentation := by
  let K := M.restrict U.2.fromSpec
  obtain ⟨P, hP⟩ := K.exists_isFinite_presentation_of_isAffine
  letI := hP
  let F : SheafOfModules (Spec Γ(X, U.1)).ringCatSheaf ⥤
      SheafOfModules U.1.toScheme.ringCatSheaf := restrictFunctor U.2.isoSpec.hom
  letI : PreservesColimitsOfSize.{u, u} F :=
    (restrictAdjunction U.2.isoSpec.hom).leftAdjoint_preservesColimits
  let e : F.obj K ≅ M.restrict U.1.ι :=
    ((restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).app M).symm ≪≫
      (restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom
    (Iso.isIso_hom e) (P.map F (restrictUnitIso U.2.isoSpec.hom).symm)
  have hQ : Q.IsFinite := by
    apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso
    exact SheafOfModules.Presentation.isFinite_map _ _ _
  letI := hQ
  let G : SheafOfModules U.1.toScheme.ringCatSheaf ⥤
      SheafOfModules (X.ringCatSheaf.over U.1) := (overEquiv U.1).inverse
  letI : PreservesColimitsOfSize.{u, u} G :=
    (overEquiv U.1).symm.toAdjunction.leftAdjoint_preservesColimits
  let e' : G.obj (M.restrict U.1.ι) ≅ M.over U.1 :=
    (overEquiv U.1).inverse.mapIso ((overFunctorEquiv U.1).app M).symm ≪≫
      ((overEquiv U.1).unitIso.app (M.over U.1)).symm
  let P' := (Q.map G (U.1.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso
    e'.hom
  have hP' : P'.IsFinite := by
    apply +allowSynthFailures SheafOfModules.instIsFiniteOfIsIso
    exact SheafOfModules.Presentation.isFinite_map _ _ _
  letI := hP'
  let q := P'.quasicoherentData
  have hq : q.IsFinitePresentation := by
    constructor
    intro V
    dsimp only [q, SheafOfModules.Presentation.quasicoherentData]
    apply +allowSynthFailures SheafOfModules.Presentation.isFinite_map
  exact SheafOfModules.IsFinitePresentation.mk (M := M.over U.1) ⟨q, hq⟩

/-- Descent from the actual affine-open cover, not from an assumed coherent
structure on the ambient sheaf. -/
theorem finitePresentation_of_fromSpec (M : X.Modules)
    (hM : ∀ U : X.affineOpens, (M.restrict U.2.fromSpec).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have hlocal (U : X.affineOpens) : (M.over U.1).IsFinitePresentation := by
    letI := hM U
    exact finitePresentation_over_of_fromSpec M U
  letI := hlocal
  exact SheafOfModules.IsFinitePresentation.of_coversTop M (fun U : X.affineOpens => U.1)
    (by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top X)

end LocalPresentation

section AmbientClosure

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The ambient cokernel of a morphism of finitely presented sheaves is
finitely presented on any scheme. -/
theorem finitePresentation_cokernel (f : M ⟶ N)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  apply finitePresentation_of_fromSpec
  intro U
  let F := restrictFunctor U.2.fromSpec
  letI : (F.obj M).IsFinitePresentation := finitePresentation_restrict U.2.fromSpec M
  letI : (F.obj N).IsFinitePresentation := finitePresentation_restrict U.2.fromSpec N
  letI : (F.obj M).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (F.obj M)
  letI : (F.obj M).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (F.obj M)
  letI : (F.obj N).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (F.obj N)
  have h : (cokernel (F.map f)).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_cokernel_spec (F.map f)
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso F f).symm h

/-- The ambient kernel of a morphism of coherent sheaves is coherent on a
locally Noetherian scheme. The Noetherian hypothesis is used on each affine
coordinate ring, exactly where finite submodules must be finitely presented. -/
theorem finitePresentation_kernel [IsLocallyNoetherian X] (f : M ⟶ N)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (kernel f).IsFinitePresentation := by
  apply finitePresentation_of_fromSpec
  intro U
  let F := restrictFunctor U.2.fromSpec
  letI : (F.obj M).IsFinitePresentation := finitePresentation_restrict U.2.fromSpec M
  letI : (F.obj N).IsFinitePresentation := finitePresentation_restrict U.2.fromSpec N
  letI : (F.obj M).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (F.obj M)
  letI : (F.obj M).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (F.obj M)
  letI : (F.obj N).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (F.obj N)
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have h : (kernel (F.map f)).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_kernel_spec (F.map f)
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (PreservesKernel.iso F f).symm h

end AmbientClosure

section Abelian

variable (X : Scheme.{u})

instance coherent_containsZero :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, coherent_finitePresentation_of_isZero _ (isZero_zero _)⟩

instance coherent_closedUnderBinaryProducts :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro M ⟨p⟩
    let A : SheafOfModules.{u} X.ringCatSheaf := p.diag.obj ⟨.left⟩
    let B : SheafOfModules.{u} X.ringCatSheaf := p.diag.obj ⟨.right⟩
    letI : A.IsFinitePresentation := p.prop_diag_obj ⟨.left⟩
    letI : B.IsFinitePresentation := p.prop_diag_obj ⟨.right⟩
    letI : HasFiniteBiproducts (SheafOfModules.{u} X.ringCatSheaf) :=
      TauCeti.SheafOfModules.hasFiniteBiproducts X.ringCatSheaf
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit A B)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      (TauCeti.SheafOfModules.isFinitePresentation_biprod (M := A) (N := B))

instance coherent_closedUnderFiniteProducts :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := .mk'

instance coherent_closedUnderCokernels :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro K ⟨f, c, hc, hf⟩
    letI := hf.1
    letI := hf.2
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (hc.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
      (finitePresentation_cokernel f)

instance coherent_closedUnderKernels [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro K ⟨f, c, hc, hf⟩
    letI := hf.1
    letI := hf.2
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (hc.conePointUniqueUpToIso (kernelIsKernel f)).symm
      (finitePresentation_kernel f)

/-- The actual full category of coherent sheaves on a locally Noetherian
scheme is abelian, with its kernels and cokernels computed in all module
sheaves. -/
instance coherent_abelian [IsLocallyNoetherian X] :
    Abelian (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X) := inferInstance

end Abelian

end ToricPower



-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource07
