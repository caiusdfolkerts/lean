module

public import ToricPower.AffineSectionsColimits
public import ToricPower.QuasicoherentPullbackLocal

/-!
# Actual affine scalar sections detect quasicoherent homology

The affine comparison uses the original module of sections, with its
specified base-field action. Forgetting that action is faithful; the
tilde equivalence then detects the actual restricted sheaf. Applying
this on a genuine affine open cover detects the global sheaf and the
homology of arbitrary complexes, without a boundedness assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace ToricPower

universe u v w z t

/-- Faithful preservation of zero morphisms already detects zero objects. -/
theorem isZero_of_faithful_map
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {D : Type w} [Category.{z} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms]
    (M : C) (zeroImage : IsZero (F.obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply F.map_injective
  exact (F.map_id M).trans
    (((IsZero.iff_id_eq_zero (F.obj M)).mp zeroImage).trans
      (F.map_zero M M).symm)

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- Vanishing of the actual base-field module of sections on an affine
open implies vanishing of the actual restriction to its spectrum. -/
theorem quasicoherent_fromSpec_isZero_of_sections
    (U : X.Opens) (affine : IsAffineOpen U) (M : QCoh X)
    (zeroSections : IsZero ((FiniteCover.schemeBaseSections k X U).obj M.obj)) :
    IsZero ((quasicoherentRestriction affine.fromSpec).obj M) := by
  let F := (tildeEquiv (R := .of Γ(X,U))).inverse ⋙
    forget₂ (ModuleCat.{u} Γ(X,U)) AddCommGrpCat.{u}
  apply isZero_of_faithful_map F
  exact ((affineSectionsUnderlyingIso k X U affine).app M).isZero_iff.mp
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map_isZero zeroSections)

/-- A genuine affine open cover detects zero quasicoherent sheaves by
their actual scalar sections. No particular affine frames are chosen. -/
theorem quasicoherent_isZero_of_affineSections
    {I : Type t} (U : I → X.Opens) (covering : IsOpenCover U)
    (affine : ∀ i, IsAffineOpen (U i)) (M : QCoh X)
    (zeroSections : ∀ i,
      IsZero ((FiniteCover.schemeBaseSections k X (U i)).obj M.obj)) : IsZero M := by
  let cover : Scheme.OpenCover.{t} X :=
    { I₀ := I
      X := fun i => Spec Γ(X,U i)
      f := fun i => (affine i).fromSpec
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨?_, inferInstance⟩
        intro x
        obtain ⟨i, hi⟩ := covering.exists_mem x
        exact ⟨i, (affine i).range_fromSpec.symm ▸ hi⟩ }
  apply quasicoherent_isZero_of_openCover cover M
  intro i
  exact quasicoherent_fromSpec_isZero_of_sections k X (U i) (affine i) M
    (zeroSections i)

/-- Exact affine sections detect the actual homology of an arbitrary
complex of quasicoherent sheaves, in any complex shape. -/
theorem quasicoherent_homology_isZero_of_affineSections
    {I : Type t} (U : I → X.Opens) (covering : IsOpenCover U)
    (affine : ∀ i, IsAffineOpen (U i))
    {J : Type v} {shape : ComplexShape J} (K : HomologicalComplex (QCoh X) shape)
    (q : J)
    (zeroHomology : ∀ i, IsZero
      ((((quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X (U i)).mapHomologicalComplex
        shape).obj K).homology q)) :
    IsZero (K.homology q) := by
  apply quasicoherent_isZero_of_affineSections k X U covering affine
  intro i
  let F := quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X (U i)
  letI : PreservesFiniteLimits F :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).1
  letI : PreservesFiniteColimits F :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).2
  exact ((K.sc q).mapHomologyIso F).isZero_iff.mp (zeroHomology i)

end ToricPower

end
