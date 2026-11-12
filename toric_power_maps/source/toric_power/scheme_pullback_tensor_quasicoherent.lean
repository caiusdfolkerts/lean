module

public import ToricPower.SchemePullbackTensorCoherence
public import ToricPower.ModuleColimitComparison
public import ToricPower.QuasicoherentTensorColimits

/-!
# The canonical pullback tensor comparison on quasicoherent sheaves

Over an affine target, an unrestricted free presentation reduces the
specified tensor comparison to the tensor unit. The oplax unit law proves
that case. Restriction to affine opens then proves the assertion on an
arbitrary scheme. Only one factor needs to be quasicoherent.

This proves invertibility of the original adjunction comparison, including
its naturality; an unspecified isomorphism of the two objects would not
suffice for the subsequent diagonal differential calculations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Functor.OplaxMonoidal

namespace ToricPower

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual canonical tensor comparison, natural in its left factor. -/
def pullbackTensorComparisonLeft (N : Y.Modules) :
    tensorRight N ⋙ Scheme.Modules.pullback f ⟶
      Scheme.Modules.pullback f ⋙
        tensorRight ((Scheme.Modules.pullback f).obj N) where
  app M := δ (Scheme.Modules.pullback f) M N
  naturality {M M'} g := (δ_natural_left (Scheme.Modules.pullback f) g N).symm

theorem pullbackTensorComparisonLeft_unit_isIso (N : Y.Modules) :
    IsIso ((pullbackTensorComparisonLeft f N).app (𝟙_ Y.Modules)) := by
  change IsIso (δ (Scheme.Modules.pullback f) (𝟙_ Y.Modules) N)
  have h : IsIso ((Scheme.Modules.pullback f).map (λ_ N).inv ≫
      δ (Scheme.Modules.pullback f) (𝟙_ Y.Modules) N ≫
      η (Scheme.Modules.pullback f) ▷ (Scheme.Modules.pullback f).obj N) := by
    rw [← Functor.OplaxMonoidal.left_unitality]
    infer_instance
  have h' : IsIso (δ (Scheme.Modules.pullback f) (𝟙_ Y.Modules) N ≫
      η (Scheme.Modules.pullback f) ▷ (Scheme.Modules.pullback f).obj N) :=
    IsIso.of_isIso_comp_left ((Scheme.Modules.pullback f).map (λ_ N).inv) _
  exact IsIso.of_isIso_comp_right _
    (η (Scheme.Modules.pullback f) ▷ (Scheme.Modules.pullback f).obj N)

/-- An affine target requires no finiteness assumption on either factor. -/
theorem pullbackTensorComparisonLeft_spec_isIso {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (M N : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso (δ (Scheme.Modules.pullback f) M N) := by
  let α := Functor.whiskerLeft (quasicoherentInclusion (Spec R))
    (pullbackTensorComparisonLeft f N)
  let comparison := Functor.whiskerLeft (tildeEquiv (R := R)).functor α
  have unit : IsIso (comparison.app (ModuleCat.of R R)) := by
    change IsIso ((pullbackTensorComparisonLeft f N).app
      (tilde (ModuleCat.of R R)))
    exact (NatTrans.isIso_app_iff_of_iso (pullbackTensorComparisonLeft f N)
      (tildeSelf (R := R))).mpr (pullbackTensorComparisonLeft_unit_isIso f N)
  let Mq : QCoh (Spec R) := ⟨M, inferInstance⟩
  have h : IsIso (α.app ((tildeEquiv (R := R)).functor.obj
      ((tildeEquiv (R := R)).inverse.obj Mq))) :=
    isIso_natTrans_app_of_free_unit R comparison unit _
  exact (NatTrans.isIso_app_iff_of_iso α
    ((tildeEquiv (R := R)).counitIso.app Mq)).mp h

theorem pullbackTensorComparisonLeft_affine_isIso [IsAffine Y]
    (M N : Y.Modules) [M.IsQuasicoherent] :
    IsIso (δ (Scheme.Modules.pullback f) M N) := by
  have h : IsIso (δ
      (Scheme.Modules.pullback ((f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv)) M N) := by
    rw [Scheme.Modules.pullback_comp_δ]
    have := pullbackTensorComparisonLeft_spec_isIso (f ≫ Y.isoSpec.hom)
      ((Scheme.Modules.pullback Y.isoSpec.inv).obj M)
      ((Scheme.Modules.pullback Y.isoSpec.inv).obj N)
    infer_instance
  have equal : ((f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv) = f := by
    rw [Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  rw [equal] at h
  exact h

/-- The canonical tensor comparison is invertible for every scheme map
when its left coefficient is quasicoherent. -/
theorem pullbackTensorComparisonLeft_isIso (M N : Y.Modules)
    [M.IsQuasicoherent] : IsIso (δ (Scheme.Modules.pullback f) M N) := by
  refine (Scheme.Modules.isIso_iff_of_isOpenCover
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom) _).mpr
    fun V => ?_
  have : IsAffine V.1 := V.2
  have h : IsIso (δ (Scheme.Modules.pullback (f ∣_ V.1 ≫ V.1.ι)) M N) := by
    rw [Scheme.Modules.pullback_comp_δ]
    have := pullbackTensorComparisonLeft_affine_isIso (f ∣_ V.1)
      ((Scheme.Modules.pullback V.1.ι).obj M) ((Scheme.Modules.pullback V.1.ι).obj N)
    infer_instance
  rw [morphismRestrict_ι, Scheme.Modules.pullback_comp_δ,
    isIso_comp_left_iff, isIso_comp_right_iff] at h
  exact h

/-- The right-factor version follows from the actual braiding equation. -/
theorem pullbackTensorComparisonRight_isIso (M N : Y.Modules)
    [N.IsQuasicoherent] : IsIso (δ (Scheme.Modules.pullback f) M N) := by
  letI := pullbackTensorComparisonLeft_isIso f N M
  have h := Scheme.Modules.pullback_map_braiding_hom_comp_δ f M N
  have : IsIso (δ (Scheme.Modules.pullback f) M N ≫ (β_ _ _).hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (β_ _ _).hom

/-- The canonical pullback tensor isomorphism, retaining its specified map. -/
def quasicoherentPullbackTensorIso (M N : Y.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ≅
      (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N := by
  letI := pullbackTensorComparisonLeft_isIso f M N
  exact asIso (δ (Scheme.Modules.pullback f) M N)

end ToricPower

end
