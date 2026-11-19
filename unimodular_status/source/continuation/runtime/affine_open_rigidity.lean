module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# An affine open is determined by its ring of sections

The result concerns the actual restriction homomorphism of the structure
sheaf. It will be used when a Hartogs theorem proves that restriction across a
closed set of codimension at least two is an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

universe u

/-- An inclusion of affine opens whose actual restriction map is an
isomorphism is equality of the opens. -/
theorem affineOpen_eq_of_isIso_restriction {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    [IsIso (X.presheaf.map (homOfLE hVU).op)] : V = U := by
  apply Opens.ext
  rw [← hV.range_fromSpec, ← hU.range_fromSpec]
  exact range_eq_range_of_surjective hV.fromSpec hU.fromSpec
    (Spec.map (X.presheaf.map (homOfLE hVU).op))
    (hU.map_fromSpec hV (homOfLE hVU).op)

/-- A bijective restriction homomorphism between affine coordinate rings
forces the corresponding inclusion of opens to be equality. -/
theorem affineOpen_eq_of_bijective_restriction {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    (hres : Function.Bijective (X.presheaf.map (homOfLE hVU).op)) : V = U := by
  letI : IsIso (X.presheaf.map (homOfLE hVU).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hres
  exact affineOpen_eq_of_isIso_restriction hU hV hVU

end PaperVerification.ToricSchemes
