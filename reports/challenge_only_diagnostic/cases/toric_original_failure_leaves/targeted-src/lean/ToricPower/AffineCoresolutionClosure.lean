module

public import ToricPower.AffineHomotopyCoresolution

/-!
# The finite affine coresolution is built from actual open direct images

The cone filtration proves a useful universal statement: every
triangulated property containing the direct-image complexes from the
chosen affine opens contains the constructed coresolution. This records
the finite construction itself and can be applied to orthogonality or
to a comparison map without invoking an unbounded convergence theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex TopologicalSpace

namespace ToricPower

universe u v

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (P : ObjectProperty (HomotopyCategory (QCoh X) (.up ℤ)))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- Every finite cone stage belongs to any triangulated property
containing the genuine affine-open direct images. -/
theorem affineConeCoresolution_mem
    (localMem : ∀ (i : I) (K : CochainComplex (QCoh (V i).toScheme) ℤ),
      P ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj K)))
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    P ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
      ((affineConeCoresolution V l).obj K)) := by
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  induction l with
  | nil =>
      exact P.prop_of_isZero
        ((HomotopyCategory.isZero_quotient_obj_iff _).mpr
          ⟨mappingCone.homotopyToZeroOfId K⟩)
  | cons i l ih =>
      let S := openFiberStage V l
      let τ := (openLocalizationComplexUnit (V i).ι).app (S.1.obj K)
      let p := mappingCocone.fst τ
      let g := S.2.app K
      have hfirst : P (Q.obj (mappingCone p)) := by
        let e := HomotopyCategory.isoOfHomotopyEquiv
          (ComplexCone.fiberProjectionConeHomotopyEquiv τ)
        apply (P.prop_iff_of_iso e).mpr
        exact localMem i
          (((quasicoherentRestriction (V i).ι).mapHomologicalComplex (.up ℤ)).obj (S.1.obj K))
      exact P.ext_of_isTriangulatedClosed₂
        (mappingConeCompTriangleh p g)
        (HomotopyCategory.mappingConeCompTriangleh_distinguished p g) hfirst ih

end ToricPower

end
