module

public import ToricPower.AffineSectionsDetection
public import ToricPower.JointShapeHomologyDetection
public import ToricPower.BoundedProjectiveDimension

/-! # Affine sections detect the original reconstruction map

An additive family naturally isomorphic to the actual scalar sections on
a genuine affine open cover detects quasi-isomorphisms. The comparison is
performed before any toric fan, cellular realization, or augmentation is
substituted. The complex shape and its indexing type are arbitrary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace

namespace ToricPower

universe u v t

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  {I : Type t} (U : I → X.Opens) (covering : IsOpenCover U)
  (affine : ∀ i, IsAffineOpen (U i))
  (G : I → QCoh X ⥤ ModuleCat.{u} k) [∀ i, (G i).Additive]
  (comparison : ∀ i, G i ≅ quasicoherentInclusion X ⋙
    FiniteCover.schemeBaseSections k X (U i))

include covering affine comparison in
/-- The original map is a quasi-isomorphism whenever every naturally
identified affine detector sends it to a quasi-isomorphism. No boundedness
condition is imposed on either complex. -/
theorem reconstruction_quasiIso_of_affineDetectors
    {J : Type v} {shape : ComplexShape J}
    {K L : HomologicalComplex (QCoh X) shape} (f : K ⟶ L)
    (localIso : ∀ i, QuasiIso (((G i).mapHomologicalComplex shape).map f)) :
    QuasiIso f := by
  let sections (i : I) := quasicoherentInclusion X ⋙
    FiniteCover.schemeBaseSections k X (U i)
  letI (i : I) : PreservesFiniteLimits (sections i) :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).1
  letI (i : I) : PreservesFiniteColimits (sections i) :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).2
  apply quasiIso_of_jointly_detect_zero_shape sections
    (fun M zero => quasicoherent_isZero_of_affineSections k X U covering affine M zero)
  intro i
  exact (map_quasiIso_iff_of_natIso (comparison i) f).mp (localIso i)

end ToricPower

end
